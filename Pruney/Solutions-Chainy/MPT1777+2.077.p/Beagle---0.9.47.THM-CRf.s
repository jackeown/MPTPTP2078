%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:43 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 6.21s
% Verified   : 
% Statistics : Number of formulae       :  142 (1209 expanded)
%              Number of leaves         :   40 ( 436 expanded)
%              Depth                    :   13
%              Number of atoms          :  335 (5658 expanded)
%              Number of equality atoms :   15 ( 619 expanded)
%              Maximal formula depth    :   26 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_231,negated_conjecture,(
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
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                       => ( g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = D
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( ( F = G
                                      & r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) )
                                   => r1_tmap_1(D,B,E,F) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_42,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_120,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_68,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_182,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(D),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(B)))) )
                     => ( ( v1_tsep_1(C,D)
                          & m1_pre_topc(C,D) )
                       => ! [F] :
                            ( m1_subset_1(F,u1_struct_0(D))
                           => ! [G] :
                                ( m1_subset_1(G,u1_struct_0(C))
                               => ( F = G
                                 => ( r1_tmap_1(D,B,E,F)
                                  <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_109,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_74,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_91,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( v3_pre_topc(B,A)
               => ! [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(C)))
                   => ( D = B
                     => v3_pre_topc(D,C) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_tops_2)).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_36,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_109,plain,(
    ! [B_304,A_305] :
      ( l1_pre_topc(B_304)
      | ~ m1_pre_topc(B_304,A_305)
      | ~ l1_pre_topc(A_305) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_115,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_109])).

tff(c_122,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_115])).

tff(c_6,plain,(
    ! [A_5] :
      ( l1_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_85,plain,(
    ! [A_302] :
      ( u1_struct_0(A_302) = k2_struct_0(A_302)
      | ~ l1_struct_0(A_302) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [A_5] :
      ( u1_struct_0(A_5) = k2_struct_0(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_129,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_122,c_89])).

tff(c_90,plain,(
    ! [A_303] :
      ( u1_struct_0(A_303) = k2_struct_0(A_303)
      | ~ l1_pre_topc(A_303) ) ),
    inference(resolution,[status(thm)],[c_6,c_85])).

tff(c_98,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_90])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_104,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_50])).

tff(c_134,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_104])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_103,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_48])).

tff(c_168,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_103])).

tff(c_118,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_109])).

tff(c_125,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_118])).

tff(c_28,plain,(
    ! [A_45] :
      ( m1_pre_topc(A_45,A_45)
      | ~ l1_pre_topc(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_120])).

tff(c_133,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_125,c_89])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_140,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_46])).

tff(c_389,plain,(
    ! [A_324,B_325] :
      ( m1_pre_topc(A_324,g1_pre_topc(u1_struct_0(B_325),u1_pre_topc(B_325)))
      | ~ m1_pre_topc(A_324,B_325)
      | ~ l1_pre_topc(B_325)
      | ~ l1_pre_topc(A_324) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_403,plain,(
    ! [A_324] :
      ( m1_pre_topc(A_324,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_324,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_324) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_389])).

tff(c_425,plain,(
    ! [A_326] :
      ( m1_pre_topc(A_326,'#skF_4')
      | ~ m1_pre_topc(A_326,'#skF_3')
      | ~ l1_pre_topc(A_326) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_140,c_403])).

tff(c_436,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_425])).

tff(c_443,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_436])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_135,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_44])).

tff(c_40,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_73,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_141,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_73])).

tff(c_38,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_231])).

tff(c_74,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_1346,plain,(
    ! [B_380,C_381,G_382,D_383,A_379,E_384] :
      ( r1_tmap_1(D_383,B_380,E_384,G_382)
      | ~ r1_tmap_1(C_381,B_380,k3_tmap_1(A_379,B_380,D_383,C_381,E_384),G_382)
      | ~ m1_subset_1(G_382,u1_struct_0(C_381))
      | ~ m1_subset_1(G_382,u1_struct_0(D_383))
      | ~ m1_pre_topc(C_381,D_383)
      | ~ v1_tsep_1(C_381,D_383)
      | ~ m1_subset_1(E_384,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_383),u1_struct_0(B_380))))
      | ~ v1_funct_2(E_384,u1_struct_0(D_383),u1_struct_0(B_380))
      | ~ v1_funct_1(E_384)
      | ~ m1_pre_topc(D_383,A_379)
      | v2_struct_0(D_383)
      | ~ m1_pre_topc(C_381,A_379)
      | v2_struct_0(C_381)
      | ~ l1_pre_topc(B_380)
      | ~ v2_pre_topc(B_380)
      | v2_struct_0(B_380)
      | ~ l1_pre_topc(A_379)
      | ~ v2_pre_topc(A_379)
      | v2_struct_0(A_379) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_1348,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_74,c_1346])).

tff(c_1351,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_134,c_98,c_129,c_168,c_98,c_129,c_443,c_135,c_129,c_141,c_133,c_1348])).

tff(c_1352,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_36,c_1351])).

tff(c_169,plain,(
    ! [B_309,A_310] :
      ( m1_subset_1(u1_struct_0(B_309),k1_zfmisc_1(u1_struct_0(A_310)))
      | ~ m1_pre_topc(B_309,A_310)
      | ~ l1_pre_topc(A_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_181,plain,(
    ! [B_309] :
      ( m1_subset_1(u1_struct_0(B_309),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_309,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_169])).

tff(c_242,plain,(
    ! [B_316] :
      ( m1_subset_1(u1_struct_0(B_316),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_316,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_181])).

tff(c_245,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_242])).

tff(c_682,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_245])).

tff(c_151,plain,(
    ! [B_307,A_308] :
      ( v2_pre_topc(B_307)
      | ~ m1_pre_topc(B_307,A_308)
      | ~ l1_pre_topc(A_308)
      | ~ v2_pre_topc(A_308) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_157,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_151])).

tff(c_164,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_157])).

tff(c_683,plain,(
    ! [B_333,A_334] :
      ( v1_tsep_1(B_333,A_334)
      | ~ v3_pre_topc(u1_struct_0(B_333),A_334)
      | ~ m1_subset_1(u1_struct_0(B_333),k1_zfmisc_1(u1_struct_0(A_334)))
      | ~ m1_pre_topc(B_333,A_334)
      | ~ l1_pre_topc(A_334)
      | ~ v2_pre_topc(A_334) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_698,plain,(
    ! [B_333] :
      ( v1_tsep_1(B_333,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_333),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_333),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_333,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_683])).

tff(c_3090,plain,(
    ! [B_488] :
      ( v1_tsep_1(B_488,'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_488),'#skF_4')
      | ~ m1_subset_1(u1_struct_0(B_488),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_488,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_122,c_698])).

tff(c_3099,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_3090])).

tff(c_3112,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_682,c_133,c_3099])).

tff(c_3113,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1352,c_3112])).

tff(c_302,plain,(
    ! [A_319,B_320] :
      ( m1_pre_topc(A_319,B_320)
      | ~ m1_pre_topc(A_319,g1_pre_topc(u1_struct_0(B_320),u1_pre_topc(B_320)))
      | ~ l1_pre_topc(B_320)
      | ~ l1_pre_topc(A_319) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_305,plain,(
    ! [A_319] :
      ( m1_pre_topc(A_319,'#skF_3')
      | ~ m1_pre_topc(A_319,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_319) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_302])).

tff(c_320,plain,(
    ! [A_319] :
      ( m1_pre_topc(A_319,'#skF_3')
      | ~ m1_pre_topc(A_319,'#skF_4')
      | ~ l1_pre_topc(A_319) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_140,c_305])).

tff(c_175,plain,(
    ! [B_309] :
      ( m1_subset_1(u1_struct_0(B_309),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_309,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_169])).

tff(c_202,plain,(
    ! [B_311] :
      ( m1_subset_1(u1_struct_0(B_311),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_311,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_175])).

tff(c_205,plain,
    ( m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_202])).

tff(c_508,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_205])).

tff(c_514,plain,
    ( ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_320,c_508])).

tff(c_524,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_443,c_514])).

tff(c_525,plain,(
    m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_526,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_205])).

tff(c_160,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_151])).

tff(c_167,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_160])).

tff(c_16,plain,(
    ! [A_19] :
      ( v3_pre_topc(k2_struct_0(A_19),A_19)
      | ~ l1_pre_topc(A_19)
      | ~ v2_pre_topc(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,(
    ! [B_44,A_42] :
      ( m1_subset_1(u1_struct_0(B_44),k1_zfmisc_1(u1_struct_0(A_42)))
      | ~ m1_pre_topc(B_44,A_42)
      | ~ l1_pre_topc(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_1223,plain,(
    ! [B_358,A_359] :
      ( v1_tsep_1(B_358,A_359)
      | ~ v3_pre_topc(u1_struct_0(B_358),A_359)
      | ~ v2_pre_topc(A_359)
      | ~ m1_pre_topc(B_358,A_359)
      | ~ l1_pre_topc(A_359) ) ),
    inference(resolution,[status(thm)],[c_26,c_683])).

tff(c_1334,plain,(
    ! [A_378] :
      ( v1_tsep_1('#skF_3',A_378)
      | ~ v3_pre_topc(k2_struct_0('#skF_3'),A_378)
      | ~ v2_pre_topc(A_378)
      | ~ m1_pre_topc('#skF_3',A_378)
      | ~ l1_pre_topc(A_378) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_1223])).

tff(c_1341,plain,
    ( v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_1334])).

tff(c_1345,plain,(
    v1_tsep_1('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_125,c_526,c_1341])).

tff(c_942,plain,(
    ! [B_342,A_343] :
      ( v3_pre_topc(u1_struct_0(B_342),A_343)
      | ~ v1_tsep_1(B_342,A_343)
      | ~ m1_subset_1(u1_struct_0(B_342),k1_zfmisc_1(u1_struct_0(A_343)))
      | ~ m1_pre_topc(B_342,A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_951,plain,(
    ! [B_342] :
      ( v3_pre_topc(u1_struct_0(B_342),'#skF_3')
      | ~ v1_tsep_1(B_342,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_342),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_342,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_942])).

tff(c_3265,plain,(
    ! [B_492] :
      ( v3_pre_topc(u1_struct_0(B_492),'#skF_3')
      | ~ v1_tsep_1(B_492,'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_492),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_492,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_125,c_951])).

tff(c_3277,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ v1_tsep_1('#skF_3','#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_3265])).

tff(c_3291,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_526,c_525,c_1345,c_133,c_3277])).

tff(c_208,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_202])).

tff(c_573,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_208])).

tff(c_617,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_320,c_573])).

tff(c_620,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_617])).

tff(c_623,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_620])).

tff(c_627,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_623])).

tff(c_629,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_208])).

tff(c_1145,plain,(
    ! [D_351,C_352,A_353] :
      ( v3_pre_topc(D_351,C_352)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(u1_struct_0(C_352)))
      | ~ v3_pre_topc(D_351,A_353)
      | ~ m1_pre_topc(C_352,A_353)
      | ~ m1_subset_1(D_351,k1_zfmisc_1(u1_struct_0(A_353)))
      | ~ l1_pre_topc(A_353) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2344,plain,(
    ! [B_441,A_442,A_443] :
      ( v3_pre_topc(u1_struct_0(B_441),A_442)
      | ~ v3_pre_topc(u1_struct_0(B_441),A_443)
      | ~ m1_pre_topc(A_442,A_443)
      | ~ m1_subset_1(u1_struct_0(B_441),k1_zfmisc_1(u1_struct_0(A_443)))
      | ~ l1_pre_topc(A_443)
      | ~ m1_pre_topc(B_441,A_442)
      | ~ l1_pre_topc(A_442) ) ),
    inference(resolution,[status(thm)],[c_26,c_1145])).

tff(c_2360,plain,(
    ! [B_441] :
      ( v3_pre_topc(u1_struct_0(B_441),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_441),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_441),k1_zfmisc_1(u1_struct_0('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ m1_pre_topc(B_441,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_629,c_2344])).

tff(c_3989,plain,(
    ! [B_523] :
      ( v3_pre_topc(u1_struct_0(B_523),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_523),'#skF_3')
      | ~ m1_subset_1(u1_struct_0(B_523),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_523,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_125,c_133,c_2360])).

tff(c_4001,plain,
    ( v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_3')
    | ~ m1_subset_1(k2_struct_0('#skF_3'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_3989])).

tff(c_4015,plain,(
    v3_pre_topc(k2_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_443,c_525,c_3291,c_133,c_133,c_4001])).

tff(c_4017,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3113,c_4015])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 19:10:02 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.22  
% 6.21/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.22  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.21/2.22  
% 6.21/2.22  %Foreground sorts:
% 6.21/2.22  
% 6.21/2.22  
% 6.21/2.22  %Background operators:
% 6.21/2.22  
% 6.21/2.22  
% 6.21/2.22  %Foreground operators:
% 6.21/2.22  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 6.21/2.22  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 6.21/2.22  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 6.21/2.22  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.21/2.22  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 6.21/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.21/2.22  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 6.21/2.22  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 6.21/2.22  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 6.21/2.22  tff('#skF_7', type, '#skF_7': $i).
% 6.21/2.22  tff('#skF_5', type, '#skF_5': $i).
% 6.21/2.22  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.21/2.22  tff('#skF_6', type, '#skF_6': $i).
% 6.21/2.22  tff('#skF_2', type, '#skF_2': $i).
% 6.21/2.22  tff('#skF_3', type, '#skF_3': $i).
% 6.21/2.22  tff('#skF_1', type, '#skF_1': $i).
% 6.21/2.22  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.21/2.22  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 6.21/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.21/2.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.21/2.22  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 6.21/2.22  tff('#skF_4', type, '#skF_4': $i).
% 6.21/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.21/2.22  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 6.21/2.22  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 6.21/2.22  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 6.21/2.22  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 6.21/2.22  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.21/2.22  
% 6.21/2.25  tff(f_231, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 6.21/2.25  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 6.21/2.25  tff(f_42, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 6.21/2.25  tff(f_38, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 6.21/2.25  tff(f_120, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 6.21/2.25  tff(f_68, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 6.21/2.25  tff(f_182, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 6.21/2.25  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 6.21/2.25  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 6.21/2.25  tff(f_109, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 6.21/2.25  tff(f_74, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 6.21/2.25  tff(f_91, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 6.21/2.25  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_36, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_109, plain, (![B_304, A_305]: (l1_pre_topc(B_304) | ~m1_pre_topc(B_304, A_305) | ~l1_pre_topc(A_305))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.21/2.25  tff(c_115, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_109])).
% 6.21/2.25  tff(c_122, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_115])).
% 6.21/2.25  tff(c_6, plain, (![A_5]: (l1_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_42])).
% 6.21/2.25  tff(c_85, plain, (![A_302]: (u1_struct_0(A_302)=k2_struct_0(A_302) | ~l1_struct_0(A_302))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.21/2.25  tff(c_89, plain, (![A_5]: (u1_struct_0(A_5)=k2_struct_0(A_5) | ~l1_pre_topc(A_5))), inference(resolution, [status(thm)], [c_6, c_85])).
% 6.21/2.25  tff(c_129, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_122, c_89])).
% 6.21/2.25  tff(c_90, plain, (![A_303]: (u1_struct_0(A_303)=k2_struct_0(A_303) | ~l1_pre_topc(A_303))), inference(resolution, [status(thm)], [c_6, c_85])).
% 6.21/2.25  tff(c_98, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_90])).
% 6.21/2.25  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_104, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_50])).
% 6.21/2.25  tff(c_134, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_104])).
% 6.21/2.25  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_103, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_48])).
% 6.21/2.25  tff(c_168, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_103])).
% 6.21/2.25  tff(c_118, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_109])).
% 6.21/2.25  tff(c_125, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_118])).
% 6.21/2.25  tff(c_28, plain, (![A_45]: (m1_pre_topc(A_45, A_45) | ~l1_pre_topc(A_45))), inference(cnfTransformation, [status(thm)], [f_120])).
% 6.21/2.25  tff(c_133, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_125, c_89])).
% 6.21/2.25  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_140, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_46])).
% 6.21/2.25  tff(c_389, plain, (![A_324, B_325]: (m1_pre_topc(A_324, g1_pre_topc(u1_struct_0(B_325), u1_pre_topc(B_325))) | ~m1_pre_topc(A_324, B_325) | ~l1_pre_topc(B_325) | ~l1_pre_topc(A_324))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.21/2.25  tff(c_403, plain, (![A_324]: (m1_pre_topc(A_324, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_324, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_324))), inference(superposition, [status(thm), theory('equality')], [c_133, c_389])).
% 6.21/2.25  tff(c_425, plain, (![A_326]: (m1_pre_topc(A_326, '#skF_4') | ~m1_pre_topc(A_326, '#skF_3') | ~l1_pre_topc(A_326))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_140, c_403])).
% 6.21/2.25  tff(c_436, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_425])).
% 6.21/2.25  tff(c_443, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_125, c_436])).
% 6.21/2.25  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_135, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_129, c_44])).
% 6.21/2.25  tff(c_40, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_73, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 6.21/2.25  tff(c_141, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_73])).
% 6.21/2.25  tff(c_38, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_231])).
% 6.21/2.25  tff(c_74, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 6.21/2.25  tff(c_1346, plain, (![B_380, C_381, G_382, D_383, A_379, E_384]: (r1_tmap_1(D_383, B_380, E_384, G_382) | ~r1_tmap_1(C_381, B_380, k3_tmap_1(A_379, B_380, D_383, C_381, E_384), G_382) | ~m1_subset_1(G_382, u1_struct_0(C_381)) | ~m1_subset_1(G_382, u1_struct_0(D_383)) | ~m1_pre_topc(C_381, D_383) | ~v1_tsep_1(C_381, D_383) | ~m1_subset_1(E_384, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_383), u1_struct_0(B_380)))) | ~v1_funct_2(E_384, u1_struct_0(D_383), u1_struct_0(B_380)) | ~v1_funct_1(E_384) | ~m1_pre_topc(D_383, A_379) | v2_struct_0(D_383) | ~m1_pre_topc(C_381, A_379) | v2_struct_0(C_381) | ~l1_pre_topc(B_380) | ~v2_pre_topc(B_380) | v2_struct_0(B_380) | ~l1_pre_topc(A_379) | ~v2_pre_topc(A_379) | v2_struct_0(A_379))), inference(cnfTransformation, [status(thm)], [f_182])).
% 6.21/2.25  tff(c_1348, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_74, c_1346])).
% 6.21/2.25  tff(c_1351, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_134, c_98, c_129, c_168, c_98, c_129, c_443, c_135, c_129, c_141, c_133, c_1348])).
% 6.21/2.25  tff(c_1352, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_36, c_1351])).
% 6.21/2.25  tff(c_169, plain, (![B_309, A_310]: (m1_subset_1(u1_struct_0(B_309), k1_zfmisc_1(u1_struct_0(A_310))) | ~m1_pre_topc(B_309, A_310) | ~l1_pre_topc(A_310))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.21/2.25  tff(c_181, plain, (![B_309]: (m1_subset_1(u1_struct_0(B_309), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_309, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_169])).
% 6.21/2.25  tff(c_242, plain, (![B_316]: (m1_subset_1(u1_struct_0(B_316), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_316, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_181])).
% 6.21/2.25  tff(c_245, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_242])).
% 6.21/2.25  tff(c_682, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_443, c_245])).
% 6.21/2.25  tff(c_151, plain, (![B_307, A_308]: (v2_pre_topc(B_307) | ~m1_pre_topc(B_307, A_308) | ~l1_pre_topc(A_308) | ~v2_pre_topc(A_308))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.21/2.25  tff(c_157, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_151])).
% 6.21/2.25  tff(c_164, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_157])).
% 6.21/2.25  tff(c_683, plain, (![B_333, A_334]: (v1_tsep_1(B_333, A_334) | ~v3_pre_topc(u1_struct_0(B_333), A_334) | ~m1_subset_1(u1_struct_0(B_333), k1_zfmisc_1(u1_struct_0(A_334))) | ~m1_pre_topc(B_333, A_334) | ~l1_pre_topc(A_334) | ~v2_pre_topc(A_334))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.25  tff(c_698, plain, (![B_333]: (v1_tsep_1(B_333, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_333), '#skF_4') | ~m1_subset_1(u1_struct_0(B_333), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_333, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_683])).
% 6.21/2.25  tff(c_3090, plain, (![B_488]: (v1_tsep_1(B_488, '#skF_4') | ~v3_pre_topc(u1_struct_0(B_488), '#skF_4') | ~m1_subset_1(u1_struct_0(B_488), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_488, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_164, c_122, c_698])).
% 6.21/2.25  tff(c_3099, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_3090])).
% 6.21/2.25  tff(c_3112, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_682, c_133, c_3099])).
% 6.21/2.25  tff(c_3113, plain, (~v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1352, c_3112])).
% 6.21/2.25  tff(c_302, plain, (![A_319, B_320]: (m1_pre_topc(A_319, B_320) | ~m1_pre_topc(A_319, g1_pre_topc(u1_struct_0(B_320), u1_pre_topc(B_320))) | ~l1_pre_topc(B_320) | ~l1_pre_topc(A_319))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.21/2.25  tff(c_305, plain, (![A_319]: (m1_pre_topc(A_319, '#skF_3') | ~m1_pre_topc(A_319, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_319))), inference(superposition, [status(thm), theory('equality')], [c_133, c_302])).
% 6.21/2.25  tff(c_320, plain, (![A_319]: (m1_pre_topc(A_319, '#skF_3') | ~m1_pre_topc(A_319, '#skF_4') | ~l1_pre_topc(A_319))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_140, c_305])).
% 6.21/2.25  tff(c_175, plain, (![B_309]: (m1_subset_1(u1_struct_0(B_309), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_309, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_169])).
% 6.21/2.25  tff(c_202, plain, (![B_311]: (m1_subset_1(u1_struct_0(B_311), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_311, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_175])).
% 6.21/2.25  tff(c_205, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_202])).
% 6.21/2.25  tff(c_508, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_205])).
% 6.21/2.25  tff(c_514, plain, (~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_320, c_508])).
% 6.21/2.25  tff(c_524, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_443, c_514])).
% 6.21/2.25  tff(c_525, plain, (m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(splitRight, [status(thm)], [c_205])).
% 6.21/2.25  tff(c_526, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_205])).
% 6.21/2.25  tff(c_160, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_151])).
% 6.21/2.25  tff(c_167, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_160])).
% 6.21/2.25  tff(c_16, plain, (![A_19]: (v3_pre_topc(k2_struct_0(A_19), A_19) | ~l1_pre_topc(A_19) | ~v2_pre_topc(A_19))), inference(cnfTransformation, [status(thm)], [f_74])).
% 6.21/2.25  tff(c_26, plain, (![B_44, A_42]: (m1_subset_1(u1_struct_0(B_44), k1_zfmisc_1(u1_struct_0(A_42))) | ~m1_pre_topc(B_44, A_42) | ~l1_pre_topc(A_42))), inference(cnfTransformation, [status(thm)], [f_116])).
% 6.21/2.25  tff(c_1223, plain, (![B_358, A_359]: (v1_tsep_1(B_358, A_359) | ~v3_pre_topc(u1_struct_0(B_358), A_359) | ~v2_pre_topc(A_359) | ~m1_pre_topc(B_358, A_359) | ~l1_pre_topc(A_359))), inference(resolution, [status(thm)], [c_26, c_683])).
% 6.21/2.25  tff(c_1334, plain, (![A_378]: (v1_tsep_1('#skF_3', A_378) | ~v3_pre_topc(k2_struct_0('#skF_3'), A_378) | ~v2_pre_topc(A_378) | ~m1_pre_topc('#skF_3', A_378) | ~l1_pre_topc(A_378))), inference(superposition, [status(thm), theory('equality')], [c_133, c_1223])).
% 6.21/2.25  tff(c_1341, plain, (v1_tsep_1('#skF_3', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_16, c_1334])).
% 6.21/2.25  tff(c_1345, plain, (v1_tsep_1('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_167, c_125, c_526, c_1341])).
% 6.21/2.25  tff(c_942, plain, (![B_342, A_343]: (v3_pre_topc(u1_struct_0(B_342), A_343) | ~v1_tsep_1(B_342, A_343) | ~m1_subset_1(u1_struct_0(B_342), k1_zfmisc_1(u1_struct_0(A_343))) | ~m1_pre_topc(B_342, A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.21/2.25  tff(c_951, plain, (![B_342]: (v3_pre_topc(u1_struct_0(B_342), '#skF_3') | ~v1_tsep_1(B_342, '#skF_3') | ~m1_subset_1(u1_struct_0(B_342), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_342, '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_133, c_942])).
% 6.21/2.25  tff(c_3265, plain, (![B_492]: (v3_pre_topc(u1_struct_0(B_492), '#skF_3') | ~v1_tsep_1(B_492, '#skF_3') | ~m1_subset_1(u1_struct_0(B_492), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_492, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_125, c_951])).
% 6.21/2.25  tff(c_3277, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~v1_tsep_1('#skF_3', '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_133, c_3265])).
% 6.21/2.25  tff(c_3291, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_526, c_525, c_1345, c_133, c_3277])).
% 6.21/2.25  tff(c_208, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_129, c_202])).
% 6.21/2.25  tff(c_573, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_208])).
% 6.21/2.25  tff(c_617, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_320, c_573])).
% 6.21/2.25  tff(c_620, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_122, c_617])).
% 6.21/2.25  tff(c_623, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_620])).
% 6.21/2.25  tff(c_627, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_623])).
% 6.21/2.25  tff(c_629, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_208])).
% 6.21/2.25  tff(c_1145, plain, (![D_351, C_352, A_353]: (v3_pre_topc(D_351, C_352) | ~m1_subset_1(D_351, k1_zfmisc_1(u1_struct_0(C_352))) | ~v3_pre_topc(D_351, A_353) | ~m1_pre_topc(C_352, A_353) | ~m1_subset_1(D_351, k1_zfmisc_1(u1_struct_0(A_353))) | ~l1_pre_topc(A_353))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.21/2.25  tff(c_2344, plain, (![B_441, A_442, A_443]: (v3_pre_topc(u1_struct_0(B_441), A_442) | ~v3_pre_topc(u1_struct_0(B_441), A_443) | ~m1_pre_topc(A_442, A_443) | ~m1_subset_1(u1_struct_0(B_441), k1_zfmisc_1(u1_struct_0(A_443))) | ~l1_pre_topc(A_443) | ~m1_pre_topc(B_441, A_442) | ~l1_pre_topc(A_442))), inference(resolution, [status(thm)], [c_26, c_1145])).
% 6.21/2.25  tff(c_2360, plain, (![B_441]: (v3_pre_topc(u1_struct_0(B_441), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_441), '#skF_3') | ~m1_subset_1(u1_struct_0(B_441), k1_zfmisc_1(u1_struct_0('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~m1_pre_topc(B_441, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_629, c_2344])).
% 6.21/2.25  tff(c_3989, plain, (![B_523]: (v3_pre_topc(u1_struct_0(B_523), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_523), '#skF_3') | ~m1_subset_1(u1_struct_0(B_523), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_523, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_122, c_125, c_133, c_2360])).
% 6.21/2.25  tff(c_4001, plain, (v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_3') | ~m1_subset_1(k2_struct_0('#skF_3'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_133, c_3989])).
% 6.21/2.25  tff(c_4015, plain, (v3_pre_topc(k2_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_443, c_525, c_3291, c_133, c_133, c_4001])).
% 6.21/2.25  tff(c_4017, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3113, c_4015])).
% 6.21/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.21/2.25  
% 6.21/2.25  Inference rules
% 6.21/2.25  ----------------------
% 6.21/2.25  #Ref     : 0
% 6.21/2.25  #Sup     : 825
% 6.21/2.25  #Fact    : 0
% 6.21/2.25  #Define  : 0
% 6.21/2.25  #Split   : 20
% 6.21/2.25  #Chain   : 0
% 6.21/2.25  #Close   : 0
% 6.21/2.25  
% 6.21/2.25  Ordering : KBO
% 6.21/2.25  
% 6.21/2.25  Simplification rules
% 6.21/2.25  ----------------------
% 6.21/2.25  #Subsume      : 336
% 6.21/2.25  #Demod        : 1235
% 6.21/2.25  #Tautology    : 198
% 6.21/2.25  #SimpNegUnit  : 37
% 6.21/2.25  #BackRed      : 6
% 6.21/2.25  
% 6.21/2.25  #Partial instantiations: 0
% 6.21/2.25  #Strategies tried      : 1
% 6.21/2.25  
% 6.21/2.25  Timing (in seconds)
% 6.21/2.25  ----------------------
% 6.21/2.26  Preprocessing        : 0.39
% 6.21/2.26  Parsing              : 0.20
% 6.21/2.26  CNF conversion       : 0.05
% 6.21/2.26  Main loop            : 1.06
% 6.21/2.26  Inferencing          : 0.34
% 6.21/2.26  Reduction            : 0.39
% 6.21/2.26  Demodulation         : 0.28
% 6.21/2.26  BG Simplification    : 0.03
% 6.21/2.26  Subsumption          : 0.24
% 6.21/2.26  Abstraction          : 0.04
% 6.21/2.26  MUC search           : 0.00
% 6.21/2.26  Cooper               : 0.00
% 6.21/2.26  Total                : 1.50
% 6.21/2.26  Index Insertion      : 0.00
% 6.21/2.26  Index Deletion       : 0.00
% 6.21/2.26  Index Matching       : 0.00
% 6.21/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
