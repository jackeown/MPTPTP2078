%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:30 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :  132 ( 400 expanded)
%              Number of leaves         :   37 ( 168 expanded)
%              Depth                    :   14
%              Number of atoms          :  492 (3173 expanded)
%              Number of equality atoms :   34 ( 160 expanded)
%              Maximal formula depth    :   22 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_315,negated_conjecture,(
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
                  & m1_pre_topc(C,B) )
               => ! [D] :
                    ( ( ~ v2_struct_0(D)
                      & m1_pre_topc(D,B) )
                   => ! [E] :
                        ( ( v1_funct_1(E)
                          & v1_funct_2(E,u1_struct_0(D),u1_struct_0(A))
                          & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D),u1_struct_0(A)))) )
                       => ( ( v1_tsep_1(C,B)
                            & m1_pre_topc(C,B)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,A,E,F)
                                    <=> r1_tmap_1(C,A,k3_tmap_1(B,A,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_143,axiom,(
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
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_250,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_168,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_161,axiom,(
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

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(B)))
             => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_pre_topc)).

tff(f_84,axiom,(
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

tff(f_208,axiom,(
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
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_38,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_36,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_32,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_34,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_80,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_34])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_76])).

tff(c_152,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_79,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_70])).

tff(c_154,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_79])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_104,plain,(
    ! [B_347,A_348] :
      ( v2_pre_topc(B_347)
      | ~ m1_pre_topc(B_347,A_348)
      | ~ l1_pre_topc(A_348)
      | ~ v2_pre_topc(A_348) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_107,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_104])).

tff(c_116,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_107])).

tff(c_85,plain,(
    ! [B_345,A_346] :
      ( l1_pre_topc(B_345)
      | ~ m1_pre_topc(B_345,A_346)
      | ~ l1_pre_topc(A_346) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_88,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_85])).

tff(c_97,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_88])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_629,plain,(
    ! [B_424,A_421,C_422,D_425,E_423] :
      ( k3_tmap_1(A_421,B_424,C_422,D_425,E_423) = k2_partfun1(u1_struct_0(C_422),u1_struct_0(B_424),E_423,u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,C_422)
      | ~ m1_subset_1(E_423,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_422),u1_struct_0(B_424))))
      | ~ v1_funct_2(E_423,u1_struct_0(C_422),u1_struct_0(B_424))
      | ~ v1_funct_1(E_423)
      | ~ m1_pre_topc(D_425,A_421)
      | ~ m1_pre_topc(C_422,A_421)
      | ~ l1_pre_topc(B_424)
      | ~ v2_pre_topc(B_424)
      | v2_struct_0(B_424)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_631,plain,(
    ! [A_421,D_425] :
      ( k3_tmap_1(A_421,'#skF_1','#skF_4',D_425,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_425,A_421)
      | ~ m1_pre_topc('#skF_4',A_421)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(resolution,[status(thm)],[c_44,c_629])).

tff(c_634,plain,(
    ! [A_421,D_425] :
      ( k3_tmap_1(A_421,'#skF_1','#skF_4',D_425,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_425))
      | ~ m1_pre_topc(D_425,'#skF_4')
      | ~ m1_pre_topc(D_425,A_421)
      | ~ m1_pre_topc('#skF_4',A_421)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421)
      | v2_struct_0(A_421) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_631])).

tff(c_636,plain,(
    ! [A_426,D_427] :
      ( k3_tmap_1(A_426,'#skF_1','#skF_4',D_427,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_427))
      | ~ m1_pre_topc(D_427,'#skF_4')
      | ~ m1_pre_topc(D_427,A_426)
      | ~ m1_pre_topc('#skF_4',A_426)
      | ~ l1_pre_topc(A_426)
      | ~ v2_pre_topc(A_426)
      | v2_struct_0(A_426) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_634])).

tff(c_642,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_636])).

tff(c_654,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_38,c_642])).

tff(c_655,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_654])).

tff(c_558,plain,(
    ! [A_412,B_413,C_414,D_415] :
      ( k2_partfun1(u1_struct_0(A_412),u1_struct_0(B_413),C_414,u1_struct_0(D_415)) = k2_tmap_1(A_412,B_413,C_414,D_415)
      | ~ m1_pre_topc(D_415,A_412)
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412),u1_struct_0(B_413))))
      | ~ v1_funct_2(C_414,u1_struct_0(A_412),u1_struct_0(B_413))
      | ~ v1_funct_1(C_414)
      | ~ l1_pre_topc(B_413)
      | ~ v2_pre_topc(B_413)
      | v2_struct_0(B_413)
      | ~ l1_pre_topc(A_412)
      | ~ v2_pre_topc(A_412)
      | v2_struct_0(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_560,plain,(
    ! [D_415] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_415)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_415)
      | ~ m1_pre_topc(D_415,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_558])).

tff(c_563,plain,(
    ! [D_415] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_415)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_415)
      | ~ m1_pre_topc(D_415,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_97,c_66,c_64,c_48,c_46,c_560])).

tff(c_564,plain,(
    ! [D_415] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_415)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_415)
      | ~ m1_pre_topc(D_415,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_563])).

tff(c_663,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_655,c_564])).

tff(c_670,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_663])).

tff(c_675,plain,(
    r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_670,c_152])).

tff(c_766,plain,(
    ! [F_442,A_443,D_445,C_444,B_441] :
      ( r1_tmap_1(B_441,A_443,C_444,F_442)
      | ~ r1_tmap_1(D_445,A_443,k2_tmap_1(B_441,A_443,C_444,D_445),F_442)
      | ~ m1_subset_1(F_442,u1_struct_0(D_445))
      | ~ m1_subset_1(F_442,u1_struct_0(B_441))
      | ~ m1_pre_topc(D_445,B_441)
      | ~ v1_tsep_1(D_445,B_441)
      | v2_struct_0(D_445)
      | ~ m1_subset_1(C_444,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_441),u1_struct_0(A_443))))
      | ~ v1_funct_2(C_444,u1_struct_0(B_441),u1_struct_0(A_443))
      | ~ v1_funct_1(C_444)
      | ~ l1_pre_topc(B_441)
      | ~ v2_pre_topc(B_441)
      | v2_struct_0(B_441)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443)
      | v2_struct_0(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_250])).

tff(c_770,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_675,c_766])).

tff(c_777,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_116,c_97,c_48,c_46,c_44,c_38,c_36,c_80,c_770])).

tff(c_778,plain,(
    ~ v1_tsep_1('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_56,c_154,c_777])).

tff(c_42,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_315])).

tff(c_22,plain,(
    ! [B_91,A_89] :
      ( m1_subset_1(u1_struct_0(B_91),k1_zfmisc_1(u1_struct_0(A_89)))
      | ~ m1_pre_topc(B_91,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_168])).

tff(c_223,plain,(
    ! [B_377,A_378] :
      ( v3_pre_topc(u1_struct_0(B_377),A_378)
      | ~ v1_tsep_1(B_377,A_378)
      | ~ m1_subset_1(u1_struct_0(B_377),k1_zfmisc_1(u1_struct_0(A_378)))
      | ~ m1_pre_topc(B_377,A_378)
      | ~ l1_pre_topc(A_378)
      | ~ v2_pre_topc(A_378) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_257,plain,(
    ! [B_91,A_89] :
      ( v3_pre_topc(u1_struct_0(B_91),A_89)
      | ~ v1_tsep_1(B_91,A_89)
      | ~ v2_pre_topc(A_89)
      | ~ m1_pre_topc(B_91,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_22,c_223])).

tff(c_155,plain,(
    ! [C_357,A_358,B_359] :
      ( m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ m1_subset_1(C_357,k1_zfmisc_1(u1_struct_0(B_359)))
      | ~ m1_pre_topc(B_359,A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_178,plain,(
    ! [B_365,A_366,A_367] :
      ( m1_subset_1(u1_struct_0(B_365),k1_zfmisc_1(u1_struct_0(A_366)))
      | ~ m1_pre_topc(A_367,A_366)
      | ~ l1_pre_topc(A_366)
      | ~ m1_pre_topc(B_365,A_367)
      | ~ l1_pre_topc(A_367) ) ),
    inference(resolution,[status(thm)],[c_22,c_155])).

tff(c_182,plain,(
    ! [B_365] :
      ( m1_subset_1(u1_struct_0(B_365),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_365,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_178])).

tff(c_192,plain,(
    ! [B_365] :
      ( m1_subset_1(u1_struct_0(B_365),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_365,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_58,c_182])).

tff(c_424,plain,(
    ! [D_396,C_397,A_398] :
      ( v3_pre_topc(D_396,C_397)
      | ~ m1_subset_1(D_396,k1_zfmisc_1(u1_struct_0(C_397)))
      | ~ v3_pre_topc(D_396,A_398)
      | ~ m1_pre_topc(C_397,A_398)
      | ~ m1_subset_1(D_396,k1_zfmisc_1(u1_struct_0(A_398)))
      | ~ l1_pre_topc(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_874,plain,(
    ! [B_454,A_455,A_456] :
      ( v3_pre_topc(u1_struct_0(B_454),A_455)
      | ~ v3_pre_topc(u1_struct_0(B_454),A_456)
      | ~ m1_pre_topc(A_455,A_456)
      | ~ m1_subset_1(u1_struct_0(B_454),k1_zfmisc_1(u1_struct_0(A_456)))
      | ~ l1_pre_topc(A_456)
      | ~ m1_pre_topc(B_454,A_455)
      | ~ l1_pre_topc(A_455) ) ),
    inference(resolution,[status(thm)],[c_22,c_424])).

tff(c_878,plain,(
    ! [B_454] :
      ( v3_pre_topc(u1_struct_0(B_454),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_454),'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_454),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ l1_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_454,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_874])).

tff(c_1014,plain,(
    ! [B_464] :
      ( v3_pre_topc(u1_struct_0(B_464),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_464),'#skF_2')
      | ~ m1_subset_1(u1_struct_0(B_464),k1_zfmisc_1(u1_struct_0('#skF_2')))
      | ~ m1_pre_topc(B_464,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_58,c_878])).

tff(c_1051,plain,(
    ! [B_465] :
      ( v3_pre_topc(u1_struct_0(B_465),'#skF_4')
      | ~ v3_pre_topc(u1_struct_0(B_465),'#skF_2')
      | ~ m1_pre_topc(B_465,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_192,c_1014])).

tff(c_1055,plain,(
    ! [B_91] :
      ( v3_pre_topc(u1_struct_0(B_91),'#skF_4')
      | ~ m1_pre_topc(B_91,'#skF_4')
      | ~ v1_tsep_1(B_91,'#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | ~ m1_pre_topc(B_91,'#skF_2')
      | ~ l1_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_257,c_1051])).

tff(c_1067,plain,(
    ! [B_466] :
      ( v3_pre_topc(u1_struct_0(B_466),'#skF_4')
      | ~ m1_pre_topc(B_466,'#skF_4')
      | ~ v1_tsep_1(B_466,'#skF_2')
      | ~ m1_pre_topc(B_466,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_60,c_1055])).

tff(c_309,plain,(
    ! [B_388,A_389] :
      ( v1_tsep_1(B_388,A_389)
      | ~ v3_pre_topc(u1_struct_0(B_388),A_389)
      | ~ m1_subset_1(u1_struct_0(B_388),k1_zfmisc_1(u1_struct_0(A_389)))
      | ~ m1_pre_topc(B_388,A_389)
      | ~ l1_pre_topc(A_389)
      | ~ v2_pre_topc(A_389) ) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_343,plain,(
    ! [B_91,A_89] :
      ( v1_tsep_1(B_91,A_89)
      | ~ v3_pre_topc(u1_struct_0(B_91),A_89)
      | ~ v2_pre_topc(A_89)
      | ~ m1_pre_topc(B_91,A_89)
      | ~ l1_pre_topc(A_89) ) ),
    inference(resolution,[status(thm)],[c_22,c_309])).

tff(c_1079,plain,(
    ! [B_466] :
      ( v1_tsep_1(B_466,'#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ m1_pre_topc(B_466,'#skF_4')
      | ~ v1_tsep_1(B_466,'#skF_2')
      | ~ m1_pre_topc(B_466,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_1067,c_343])).

tff(c_1097,plain,(
    ! [B_467] :
      ( v1_tsep_1(B_467,'#skF_4')
      | ~ m1_pre_topc(B_467,'#skF_4')
      | ~ v1_tsep_1(B_467,'#skF_2')
      | ~ m1_pre_topc(B_467,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_116,c_1079])).

tff(c_1100,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_42,c_1097])).

tff(c_1103,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_38,c_1100])).

tff(c_1105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_778,c_1103])).

tff(c_1106,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1759,plain,(
    ! [C_550,B_547,A_548,D_546,F_549] :
      ( r1_tmap_1(D_546,A_548,k2_tmap_1(B_547,A_548,C_550,D_546),F_549)
      | ~ r1_tmap_1(B_547,A_548,C_550,F_549)
      | ~ m1_subset_1(F_549,u1_struct_0(D_546))
      | ~ m1_subset_1(F_549,u1_struct_0(B_547))
      | ~ m1_pre_topc(D_546,B_547)
      | v2_struct_0(D_546)
      | ~ m1_subset_1(C_550,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_547),u1_struct_0(A_548))))
      | ~ v1_funct_2(C_550,u1_struct_0(B_547),u1_struct_0(A_548))
      | ~ v1_funct_1(C_550)
      | ~ l1_pre_topc(B_547)
      | ~ v2_pre_topc(B_547)
      | v2_struct_0(B_547)
      | ~ l1_pre_topc(A_548)
      | ~ v2_pre_topc(A_548)
      | v2_struct_0(A_548) ) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_1761,plain,(
    ! [D_546,F_549] :
      ( r1_tmap_1(D_546,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_546),F_549)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_549)
      | ~ m1_subset_1(F_549,u1_struct_0(D_546))
      | ~ m1_subset_1(F_549,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_546,'#skF_4')
      | v2_struct_0(D_546)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_44,c_1759])).

tff(c_1764,plain,(
    ! [D_546,F_549] :
      ( r1_tmap_1(D_546,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_546),F_549)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_549)
      | ~ m1_subset_1(F_549,u1_struct_0(D_546))
      | ~ m1_subset_1(F_549,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_546,'#skF_4')
      | v2_struct_0(D_546)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_116,c_97,c_48,c_46,c_1761])).

tff(c_1768,plain,(
    ! [D_551,F_552] :
      ( r1_tmap_1(D_551,'#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5',D_551),F_552)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',F_552)
      | ~ m1_subset_1(F_552,u1_struct_0(D_551))
      | ~ m1_subset_1(F_552,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_551,'#skF_4')
      | v2_struct_0(D_551) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_52,c_1764])).

tff(c_1691,plain,(
    ! [A_539,C_540,D_543,E_541,B_542] :
      ( k3_tmap_1(A_539,B_542,C_540,D_543,E_541) = k2_partfun1(u1_struct_0(C_540),u1_struct_0(B_542),E_541,u1_struct_0(D_543))
      | ~ m1_pre_topc(D_543,C_540)
      | ~ m1_subset_1(E_541,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_540),u1_struct_0(B_542))))
      | ~ v1_funct_2(E_541,u1_struct_0(C_540),u1_struct_0(B_542))
      | ~ v1_funct_1(E_541)
      | ~ m1_pre_topc(D_543,A_539)
      | ~ m1_pre_topc(C_540,A_539)
      | ~ l1_pre_topc(B_542)
      | ~ v2_pre_topc(B_542)
      | v2_struct_0(B_542)
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_1693,plain,(
    ! [A_539,D_543] :
      ( k3_tmap_1(A_539,'#skF_1','#skF_4',D_543,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_543))
      | ~ m1_pre_topc(D_543,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_543,A_539)
      | ~ m1_pre_topc('#skF_4',A_539)
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(resolution,[status(thm)],[c_44,c_1691])).

tff(c_1696,plain,(
    ! [A_539,D_543] :
      ( k3_tmap_1(A_539,'#skF_1','#skF_4',D_543,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_543))
      | ~ m1_pre_topc(D_543,'#skF_4')
      | ~ m1_pre_topc(D_543,A_539)
      | ~ m1_pre_topc('#skF_4',A_539)
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_48,c_46,c_1693])).

tff(c_1698,plain,(
    ! [A_544,D_545] :
      ( k3_tmap_1(A_544,'#skF_1','#skF_4',D_545,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_545))
      | ~ m1_pre_topc(D_545,'#skF_4')
      | ~ m1_pre_topc(D_545,A_544)
      | ~ m1_pre_topc('#skF_4',A_544)
      | ~ l1_pre_topc(A_544)
      | ~ v2_pre_topc(A_544)
      | v2_struct_0(A_544) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1696])).

tff(c_1704,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_1698])).

tff(c_1716,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_58,c_50,c_38,c_1704])).

tff(c_1717,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1716])).

tff(c_1613,plain,(
    ! [A_529,B_530,C_531,D_532] :
      ( k2_partfun1(u1_struct_0(A_529),u1_struct_0(B_530),C_531,u1_struct_0(D_532)) = k2_tmap_1(A_529,B_530,C_531,D_532)
      | ~ m1_pre_topc(D_532,A_529)
      | ~ m1_subset_1(C_531,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_529),u1_struct_0(B_530))))
      | ~ v1_funct_2(C_531,u1_struct_0(A_529),u1_struct_0(B_530))
      | ~ v1_funct_1(C_531)
      | ~ l1_pre_topc(B_530)
      | ~ v2_pre_topc(B_530)
      | v2_struct_0(B_530)
      | ~ l1_pre_topc(A_529)
      | ~ v2_pre_topc(A_529)
      | v2_struct_0(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1615,plain,(
    ! [D_532] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_532)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_532)
      | ~ m1_pre_topc(D_532,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_1613])).

tff(c_1618,plain,(
    ! [D_532] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_532)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_532)
      | ~ m1_pre_topc(D_532,'#skF_4')
      | v2_struct_0('#skF_1')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_97,c_66,c_64,c_48,c_46,c_1615])).

tff(c_1619,plain,(
    ! [D_532] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'),'#skF_5',u1_struct_0(D_532)) = k2_tmap_1('#skF_4','#skF_1','#skF_5',D_532)
      | ~ m1_pre_topc(D_532,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_68,c_1618])).

tff(c_1725,plain,
    ( k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1717,c_1619])).

tff(c_1732,plain,(
    k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1725])).

tff(c_1108,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_79])).

tff(c_1110,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1106,c_1108])).

tff(c_1111,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_79])).

tff(c_1737,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k2_tmap_1('#skF_4','#skF_1','#skF_5','#skF_3'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1732,c_1111])).

tff(c_1771,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_1768,c_1737])).

tff(c_1774,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_80,c_1106,c_1771])).

tff(c_1776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1774])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:31:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.86  
% 4.92/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.86  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.92/1.86  
% 4.92/1.86  %Foreground sorts:
% 4.92/1.86  
% 4.92/1.86  
% 4.92/1.86  %Background operators:
% 4.92/1.86  
% 4.92/1.86  
% 4.92/1.86  %Foreground operators:
% 4.92/1.86  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.92/1.86  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.92/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.92/1.86  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 4.92/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/1.86  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.92/1.86  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.92/1.86  tff('#skF_7', type, '#skF_7': $i).
% 4.92/1.86  tff('#skF_5', type, '#skF_5': $i).
% 4.92/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.92/1.86  tff('#skF_6', type, '#skF_6': $i).
% 4.92/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.92/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.92/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.92/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.92/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.92/1.86  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.92/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.92/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/1.86  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.92/1.86  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.92/1.86  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.92/1.86  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.92/1.86  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.92/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.92/1.86  
% 4.92/1.89  tff(f_315, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 4.92/1.89  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.92/1.89  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.92/1.89  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.92/1.89  tff(f_111, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.92/1.89  tff(f_250, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.92/1.89  tff(f_168, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.92/1.89  tff(f_161, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_tsep_1)).
% 4.92/1.89  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(B))) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_pre_topc)).
% 4.92/1.89  tff(f_84, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_pre_topc(C, A) => (v3_pre_topc(B, A) => (![D]: (m1_subset_1(D, k1_zfmisc_1(u1_struct_0(C))) => ((D = B) => v3_pre_topc(D, C))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_tops_2)).
% 4.92/1.89  tff(f_208, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.92/1.89  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_38, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_36, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_32, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_34, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_80, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_34])).
% 4.92/1.89  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_78, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_76])).
% 4.92/1.89  tff(c_152, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 4.92/1.89  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_79, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_70])).
% 4.92/1.89  tff(c_154, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_152, c_79])).
% 4.92/1.89  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_104, plain, (![B_347, A_348]: (v2_pre_topc(B_347) | ~m1_pre_topc(B_347, A_348) | ~l1_pre_topc(A_348) | ~v2_pre_topc(A_348))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.92/1.89  tff(c_107, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_104])).
% 4.92/1.89  tff(c_116, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_107])).
% 4.92/1.89  tff(c_85, plain, (![B_345, A_346]: (l1_pre_topc(B_345) | ~m1_pre_topc(B_345, A_346) | ~l1_pre_topc(A_346))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.92/1.89  tff(c_88, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_50, c_85])).
% 4.92/1.89  tff(c_97, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_88])).
% 4.92/1.89  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_629, plain, (![B_424, A_421, C_422, D_425, E_423]: (k3_tmap_1(A_421, B_424, C_422, D_425, E_423)=k2_partfun1(u1_struct_0(C_422), u1_struct_0(B_424), E_423, u1_struct_0(D_425)) | ~m1_pre_topc(D_425, C_422) | ~m1_subset_1(E_423, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_422), u1_struct_0(B_424)))) | ~v1_funct_2(E_423, u1_struct_0(C_422), u1_struct_0(B_424)) | ~v1_funct_1(E_423) | ~m1_pre_topc(D_425, A_421) | ~m1_pre_topc(C_422, A_421) | ~l1_pre_topc(B_424) | ~v2_pre_topc(B_424) | v2_struct_0(B_424) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421) | v2_struct_0(A_421))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.92/1.89  tff(c_631, plain, (![A_421, D_425]: (k3_tmap_1(A_421, '#skF_1', '#skF_4', D_425, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_425)) | ~m1_pre_topc(D_425, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_425, A_421) | ~m1_pre_topc('#skF_4', A_421) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421) | v2_struct_0(A_421))), inference(resolution, [status(thm)], [c_44, c_629])).
% 4.92/1.89  tff(c_634, plain, (![A_421, D_425]: (k3_tmap_1(A_421, '#skF_1', '#skF_4', D_425, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_425)) | ~m1_pre_topc(D_425, '#skF_4') | ~m1_pre_topc(D_425, A_421) | ~m1_pre_topc('#skF_4', A_421) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421) | v2_struct_0(A_421))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_631])).
% 4.92/1.89  tff(c_636, plain, (![A_426, D_427]: (k3_tmap_1(A_426, '#skF_1', '#skF_4', D_427, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_427)) | ~m1_pre_topc(D_427, '#skF_4') | ~m1_pre_topc(D_427, A_426) | ~m1_pre_topc('#skF_4', A_426) | ~l1_pre_topc(A_426) | ~v2_pre_topc(A_426) | v2_struct_0(A_426))), inference(negUnitSimplification, [status(thm)], [c_68, c_634])).
% 4.92/1.89  tff(c_642, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_636])).
% 4.92/1.89  tff(c_654, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_38, c_642])).
% 4.92/1.89  tff(c_655, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_654])).
% 4.92/1.89  tff(c_558, plain, (![A_412, B_413, C_414, D_415]: (k2_partfun1(u1_struct_0(A_412), u1_struct_0(B_413), C_414, u1_struct_0(D_415))=k2_tmap_1(A_412, B_413, C_414, D_415) | ~m1_pre_topc(D_415, A_412) | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_412), u1_struct_0(B_413)))) | ~v1_funct_2(C_414, u1_struct_0(A_412), u1_struct_0(B_413)) | ~v1_funct_1(C_414) | ~l1_pre_topc(B_413) | ~v2_pre_topc(B_413) | v2_struct_0(B_413) | ~l1_pre_topc(A_412) | ~v2_pre_topc(A_412) | v2_struct_0(A_412))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.92/1.89  tff(c_560, plain, (![D_415]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_415))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_415) | ~m1_pre_topc(D_415, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_558])).
% 4.92/1.89  tff(c_563, plain, (![D_415]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_415))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_415) | ~m1_pre_topc(D_415, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_97, c_66, c_64, c_48, c_46, c_560])).
% 4.92/1.89  tff(c_564, plain, (![D_415]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_415))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_415) | ~m1_pre_topc(D_415, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_563])).
% 4.92/1.89  tff(c_663, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_655, c_564])).
% 4.92/1.89  tff(c_670, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_663])).
% 4.92/1.89  tff(c_675, plain, (r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_670, c_152])).
% 4.92/1.89  tff(c_766, plain, (![F_442, A_443, D_445, C_444, B_441]: (r1_tmap_1(B_441, A_443, C_444, F_442) | ~r1_tmap_1(D_445, A_443, k2_tmap_1(B_441, A_443, C_444, D_445), F_442) | ~m1_subset_1(F_442, u1_struct_0(D_445)) | ~m1_subset_1(F_442, u1_struct_0(B_441)) | ~m1_pre_topc(D_445, B_441) | ~v1_tsep_1(D_445, B_441) | v2_struct_0(D_445) | ~m1_subset_1(C_444, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_441), u1_struct_0(A_443)))) | ~v1_funct_2(C_444, u1_struct_0(B_441), u1_struct_0(A_443)) | ~v1_funct_1(C_444) | ~l1_pre_topc(B_441) | ~v2_pre_topc(B_441) | v2_struct_0(B_441) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443) | v2_struct_0(A_443))), inference(cnfTransformation, [status(thm)], [f_250])).
% 4.92/1.89  tff(c_770, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_675, c_766])).
% 4.92/1.89  tff(c_777, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~v1_tsep_1('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_116, c_97, c_48, c_46, c_44, c_38, c_36, c_80, c_770])).
% 4.92/1.89  tff(c_778, plain, (~v1_tsep_1('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_56, c_154, c_777])).
% 4.92/1.89  tff(c_42, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_315])).
% 4.92/1.89  tff(c_22, plain, (![B_91, A_89]: (m1_subset_1(u1_struct_0(B_91), k1_zfmisc_1(u1_struct_0(A_89))) | ~m1_pre_topc(B_91, A_89) | ~l1_pre_topc(A_89))), inference(cnfTransformation, [status(thm)], [f_168])).
% 4.92/1.89  tff(c_223, plain, (![B_377, A_378]: (v3_pre_topc(u1_struct_0(B_377), A_378) | ~v1_tsep_1(B_377, A_378) | ~m1_subset_1(u1_struct_0(B_377), k1_zfmisc_1(u1_struct_0(A_378))) | ~m1_pre_topc(B_377, A_378) | ~l1_pre_topc(A_378) | ~v2_pre_topc(A_378))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.92/1.89  tff(c_257, plain, (![B_91, A_89]: (v3_pre_topc(u1_struct_0(B_91), A_89) | ~v1_tsep_1(B_91, A_89) | ~v2_pre_topc(A_89) | ~m1_pre_topc(B_91, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_22, c_223])).
% 4.92/1.89  tff(c_155, plain, (![C_357, A_358, B_359]: (m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0(A_358))) | ~m1_subset_1(C_357, k1_zfmisc_1(u1_struct_0(B_359))) | ~m1_pre_topc(B_359, A_358) | ~l1_pre_topc(A_358))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.92/1.89  tff(c_178, plain, (![B_365, A_366, A_367]: (m1_subset_1(u1_struct_0(B_365), k1_zfmisc_1(u1_struct_0(A_366))) | ~m1_pre_topc(A_367, A_366) | ~l1_pre_topc(A_366) | ~m1_pre_topc(B_365, A_367) | ~l1_pre_topc(A_367))), inference(resolution, [status(thm)], [c_22, c_155])).
% 4.92/1.89  tff(c_182, plain, (![B_365]: (m1_subset_1(u1_struct_0(B_365), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(B_365, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_178])).
% 4.92/1.89  tff(c_192, plain, (![B_365]: (m1_subset_1(u1_struct_0(B_365), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_365, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_58, c_182])).
% 4.92/1.89  tff(c_424, plain, (![D_396, C_397, A_398]: (v3_pre_topc(D_396, C_397) | ~m1_subset_1(D_396, k1_zfmisc_1(u1_struct_0(C_397))) | ~v3_pre_topc(D_396, A_398) | ~m1_pre_topc(C_397, A_398) | ~m1_subset_1(D_396, k1_zfmisc_1(u1_struct_0(A_398))) | ~l1_pre_topc(A_398))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.92/1.89  tff(c_874, plain, (![B_454, A_455, A_456]: (v3_pre_topc(u1_struct_0(B_454), A_455) | ~v3_pre_topc(u1_struct_0(B_454), A_456) | ~m1_pre_topc(A_455, A_456) | ~m1_subset_1(u1_struct_0(B_454), k1_zfmisc_1(u1_struct_0(A_456))) | ~l1_pre_topc(A_456) | ~m1_pre_topc(B_454, A_455) | ~l1_pre_topc(A_455))), inference(resolution, [status(thm)], [c_22, c_424])).
% 4.92/1.89  tff(c_878, plain, (![B_454]: (v3_pre_topc(u1_struct_0(B_454), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_454), '#skF_2') | ~m1_subset_1(u1_struct_0(B_454), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~l1_pre_topc('#skF_2') | ~m1_pre_topc(B_454, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_874])).
% 4.92/1.89  tff(c_1014, plain, (![B_464]: (v3_pre_topc(u1_struct_0(B_464), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_464), '#skF_2') | ~m1_subset_1(u1_struct_0(B_464), k1_zfmisc_1(u1_struct_0('#skF_2'))) | ~m1_pre_topc(B_464, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_58, c_878])).
% 4.92/1.89  tff(c_1051, plain, (![B_465]: (v3_pre_topc(u1_struct_0(B_465), '#skF_4') | ~v3_pre_topc(u1_struct_0(B_465), '#skF_2') | ~m1_pre_topc(B_465, '#skF_4'))), inference(resolution, [status(thm)], [c_192, c_1014])).
% 4.92/1.89  tff(c_1055, plain, (![B_91]: (v3_pre_topc(u1_struct_0(B_91), '#skF_4') | ~m1_pre_topc(B_91, '#skF_4') | ~v1_tsep_1(B_91, '#skF_2') | ~v2_pre_topc('#skF_2') | ~m1_pre_topc(B_91, '#skF_2') | ~l1_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_257, c_1051])).
% 4.92/1.89  tff(c_1067, plain, (![B_466]: (v3_pre_topc(u1_struct_0(B_466), '#skF_4') | ~m1_pre_topc(B_466, '#skF_4') | ~v1_tsep_1(B_466, '#skF_2') | ~m1_pre_topc(B_466, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_60, c_1055])).
% 4.92/1.89  tff(c_309, plain, (![B_388, A_389]: (v1_tsep_1(B_388, A_389) | ~v3_pre_topc(u1_struct_0(B_388), A_389) | ~m1_subset_1(u1_struct_0(B_388), k1_zfmisc_1(u1_struct_0(A_389))) | ~m1_pre_topc(B_388, A_389) | ~l1_pre_topc(A_389) | ~v2_pre_topc(A_389))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.92/1.89  tff(c_343, plain, (![B_91, A_89]: (v1_tsep_1(B_91, A_89) | ~v3_pre_topc(u1_struct_0(B_91), A_89) | ~v2_pre_topc(A_89) | ~m1_pre_topc(B_91, A_89) | ~l1_pre_topc(A_89))), inference(resolution, [status(thm)], [c_22, c_309])).
% 4.92/1.89  tff(c_1079, plain, (![B_466]: (v1_tsep_1(B_466, '#skF_4') | ~v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc(B_466, '#skF_4') | ~v1_tsep_1(B_466, '#skF_2') | ~m1_pre_topc(B_466, '#skF_2'))), inference(resolution, [status(thm)], [c_1067, c_343])).
% 4.92/1.89  tff(c_1097, plain, (![B_467]: (v1_tsep_1(B_467, '#skF_4') | ~m1_pre_topc(B_467, '#skF_4') | ~v1_tsep_1(B_467, '#skF_2') | ~m1_pre_topc(B_467, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_97, c_116, c_1079])).
% 4.92/1.89  tff(c_1100, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_42, c_1097])).
% 4.92/1.89  tff(c_1103, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_38, c_1100])).
% 4.92/1.89  tff(c_1105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_778, c_1103])).
% 4.92/1.89  tff(c_1106, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 4.92/1.89  tff(c_1759, plain, (![C_550, B_547, A_548, D_546, F_549]: (r1_tmap_1(D_546, A_548, k2_tmap_1(B_547, A_548, C_550, D_546), F_549) | ~r1_tmap_1(B_547, A_548, C_550, F_549) | ~m1_subset_1(F_549, u1_struct_0(D_546)) | ~m1_subset_1(F_549, u1_struct_0(B_547)) | ~m1_pre_topc(D_546, B_547) | v2_struct_0(D_546) | ~m1_subset_1(C_550, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_547), u1_struct_0(A_548)))) | ~v1_funct_2(C_550, u1_struct_0(B_547), u1_struct_0(A_548)) | ~v1_funct_1(C_550) | ~l1_pre_topc(B_547) | ~v2_pre_topc(B_547) | v2_struct_0(B_547) | ~l1_pre_topc(A_548) | ~v2_pre_topc(A_548) | v2_struct_0(A_548))), inference(cnfTransformation, [status(thm)], [f_208])).
% 4.92/1.89  tff(c_1761, plain, (![D_546, F_549]: (r1_tmap_1(D_546, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_546), F_549) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_549) | ~m1_subset_1(F_549, u1_struct_0(D_546)) | ~m1_subset_1(F_549, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_546, '#skF_4') | v2_struct_0(D_546) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_44, c_1759])).
% 4.92/1.89  tff(c_1764, plain, (![D_546, F_549]: (r1_tmap_1(D_546, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_546), F_549) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_549) | ~m1_subset_1(F_549, u1_struct_0(D_546)) | ~m1_subset_1(F_549, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_546, '#skF_4') | v2_struct_0(D_546) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_116, c_97, c_48, c_46, c_1761])).
% 4.92/1.89  tff(c_1768, plain, (![D_551, F_552]: (r1_tmap_1(D_551, '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_551), F_552) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', F_552) | ~m1_subset_1(F_552, u1_struct_0(D_551)) | ~m1_subset_1(F_552, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_551, '#skF_4') | v2_struct_0(D_551))), inference(negUnitSimplification, [status(thm)], [c_68, c_52, c_1764])).
% 4.92/1.89  tff(c_1691, plain, (![A_539, C_540, D_543, E_541, B_542]: (k3_tmap_1(A_539, B_542, C_540, D_543, E_541)=k2_partfun1(u1_struct_0(C_540), u1_struct_0(B_542), E_541, u1_struct_0(D_543)) | ~m1_pre_topc(D_543, C_540) | ~m1_subset_1(E_541, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_540), u1_struct_0(B_542)))) | ~v1_funct_2(E_541, u1_struct_0(C_540), u1_struct_0(B_542)) | ~v1_funct_1(E_541) | ~m1_pre_topc(D_543, A_539) | ~m1_pre_topc(C_540, A_539) | ~l1_pre_topc(B_542) | ~v2_pre_topc(B_542) | v2_struct_0(B_542) | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.92/1.89  tff(c_1693, plain, (![A_539, D_543]: (k3_tmap_1(A_539, '#skF_1', '#skF_4', D_543, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_543)) | ~m1_pre_topc(D_543, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_543, A_539) | ~m1_pre_topc('#skF_4', A_539) | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(resolution, [status(thm)], [c_44, c_1691])).
% 4.92/1.89  tff(c_1696, plain, (![A_539, D_543]: (k3_tmap_1(A_539, '#skF_1', '#skF_4', D_543, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_543)) | ~m1_pre_topc(D_543, '#skF_4') | ~m1_pre_topc(D_543, A_539) | ~m1_pre_topc('#skF_4', A_539) | v2_struct_0('#skF_1') | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_48, c_46, c_1693])).
% 4.92/1.89  tff(c_1698, plain, (![A_544, D_545]: (k3_tmap_1(A_544, '#skF_1', '#skF_4', D_545, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_545)) | ~m1_pre_topc(D_545, '#skF_4') | ~m1_pre_topc(D_545, A_544) | ~m1_pre_topc('#skF_4', A_544) | ~l1_pre_topc(A_544) | ~v2_pre_topc(A_544) | v2_struct_0(A_544))), inference(negUnitSimplification, [status(thm)], [c_68, c_1696])).
% 4.92/1.89  tff(c_1704, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_54, c_1698])).
% 4.92/1.89  tff(c_1716, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_58, c_50, c_38, c_1704])).
% 4.92/1.89  tff(c_1717, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_1716])).
% 4.92/1.89  tff(c_1613, plain, (![A_529, B_530, C_531, D_532]: (k2_partfun1(u1_struct_0(A_529), u1_struct_0(B_530), C_531, u1_struct_0(D_532))=k2_tmap_1(A_529, B_530, C_531, D_532) | ~m1_pre_topc(D_532, A_529) | ~m1_subset_1(C_531, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_529), u1_struct_0(B_530)))) | ~v1_funct_2(C_531, u1_struct_0(A_529), u1_struct_0(B_530)) | ~v1_funct_1(C_531) | ~l1_pre_topc(B_530) | ~v2_pre_topc(B_530) | v2_struct_0(B_530) | ~l1_pre_topc(A_529) | ~v2_pre_topc(A_529) | v2_struct_0(A_529))), inference(cnfTransformation, [status(thm)], [f_111])).
% 4.92/1.89  tff(c_1615, plain, (![D_532]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_532))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_532) | ~m1_pre_topc(D_532, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_1613])).
% 4.92/1.89  tff(c_1618, plain, (![D_532]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_532))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_532) | ~m1_pre_topc(D_532, '#skF_4') | v2_struct_0('#skF_1') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_116, c_97, c_66, c_64, c_48, c_46, c_1615])).
% 4.92/1.89  tff(c_1619, plain, (![D_532]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'), '#skF_5', u1_struct_0(D_532))=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', D_532) | ~m1_pre_topc(D_532, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_68, c_1618])).
% 4.92/1.89  tff(c_1725, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1717, c_1619])).
% 4.92/1.89  tff(c_1732, plain, (k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1725])).
% 4.92/1.89  tff(c_1108, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_79])).
% 4.92/1.89  tff(c_1110, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1106, c_1108])).
% 4.92/1.89  tff(c_1111, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_79])).
% 4.92/1.89  tff(c_1737, plain, (~r1_tmap_1('#skF_3', '#skF_1', k2_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_3'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1732, c_1111])).
% 4.92/1.89  tff(c_1771, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_1768, c_1737])).
% 4.92/1.89  tff(c_1774, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_80, c_1106, c_1771])).
% 4.92/1.89  tff(c_1776, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1774])).
% 4.92/1.89  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.92/1.89  
% 4.92/1.89  Inference rules
% 4.92/1.89  ----------------------
% 4.92/1.89  #Ref     : 0
% 4.92/1.89  #Sup     : 323
% 4.92/1.89  #Fact    : 0
% 4.92/1.89  #Define  : 0
% 4.92/1.89  #Split   : 11
% 4.92/1.89  #Chain   : 0
% 4.92/1.89  #Close   : 0
% 4.92/1.89  
% 4.92/1.89  Ordering : KBO
% 4.92/1.89  
% 4.92/1.89  Simplification rules
% 4.92/1.89  ----------------------
% 4.92/1.89  #Subsume      : 121
% 4.92/1.89  #Demod        : 413
% 4.92/1.89  #Tautology    : 84
% 4.92/1.89  #SimpNegUnit  : 48
% 4.92/1.89  #BackRed      : 4
% 4.92/1.89  
% 4.92/1.89  #Partial instantiations: 0
% 4.92/1.89  #Strategies tried      : 1
% 4.92/1.89  
% 4.92/1.89  Timing (in seconds)
% 4.92/1.89  ----------------------
% 4.92/1.89  Preprocessing        : 0.44
% 4.92/1.89  Parsing              : 0.23
% 4.92/1.89  CNF conversion       : 0.06
% 4.92/1.89  Main loop            : 0.66
% 4.92/1.89  Inferencing          : 0.22
% 4.92/1.89  Reduction            : 0.22
% 4.92/1.89  Demodulation         : 0.15
% 4.92/1.89  BG Simplification    : 0.04
% 4.92/1.89  Subsumption          : 0.14
% 4.92/1.89  Abstraction          : 0.03
% 4.92/1.89  MUC search           : 0.00
% 4.92/1.89  Cooper               : 0.00
% 4.92/1.89  Total                : 1.15
% 4.92/1.89  Index Insertion      : 0.00
% 4.92/1.89  Index Deletion       : 0.00
% 4.92/1.89  Index Matching       : 0.00
% 4.92/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
