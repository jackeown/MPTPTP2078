%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:23 EST 2020

% Result     : Theorem 3.22s
% Output     : CNFRefutation 3.22s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 330 expanded)
%              Number of leaves         :   34 ( 146 expanded)
%              Depth                    :   15
%              Number of atoms          :  423 (2992 expanded)
%              Number of equality atoms :   31 ( 145 expanded)
%              Maximal formula depth    :   26 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tmap_1,type,(
    r1_tmap_1: ( $i * $i * $i * $i ) > $o )).

tff(l1_pre_topc,type,(
    l1_pre_topc: $i > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_219,negated_conjecture,(
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
                       => ( m1_pre_topc(C,D)
                         => ! [F] :
                              ( m1_subset_1(F,k1_zfmisc_1(u1_struct_0(D)))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(D))
                                 => ! [H] :
                                      ( m1_subset_1(H,u1_struct_0(C))
                                     => ( ( v3_pre_topc(F,D)
                                          & r2_hidden(G,F)
                                          & r1_tarski(F,u1_struct_0(C))
                                          & G = H )
                                       => ( r1_tmap_1(D,B,E,G)
                                        <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(f_34,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_100,axiom,(
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

tff(f_68,axiom,(
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

tff(f_149,axiom,(
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
                      ( m1_subset_1(E,k1_zfmisc_1(u1_struct_0(B)))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(B))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( v3_pre_topc(E,B)
                                  & r2_hidden(F,E)
                                  & r1_tarski(E,u1_struct_0(D))
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_tmap_1)).

tff(c_16,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_26,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_67,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_24,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_20,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_68,plain,(
    r2_hidden('#skF_8','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_22,plain,(
    v3_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_18,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_28,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_50,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_40,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_44,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_58,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_66,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_58])).

tff(c_113,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_48,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_46,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_54,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_52,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_38,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_92,plain,(
    ! [B_436,A_437] :
      ( v2_pre_topc(B_436)
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_101,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_92])).

tff(c_110,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_101])).

tff(c_73,plain,(
    ! [B_434,A_435] :
      ( l1_pre_topc(B_434)
      | ~ m1_pre_topc(B_434,A_435)
      | ~ l1_pre_topc(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_82,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_73])).

tff(c_89,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_82])).

tff(c_36,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_34,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_32,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_30,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_42,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_222,plain,(
    ! [C_457,A_454,B_455,D_453,E_456] :
      ( k3_tmap_1(A_454,B_455,C_457,D_453,E_456) = k2_partfun1(u1_struct_0(C_457),u1_struct_0(B_455),E_456,u1_struct_0(D_453))
      | ~ m1_pre_topc(D_453,C_457)
      | ~ m1_subset_1(E_456,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_457),u1_struct_0(B_455))))
      | ~ v1_funct_2(E_456,u1_struct_0(C_457),u1_struct_0(B_455))
      | ~ v1_funct_1(E_456)
      | ~ m1_pre_topc(D_453,A_454)
      | ~ m1_pre_topc(C_457,A_454)
      | ~ l1_pre_topc(B_455)
      | ~ v2_pre_topc(B_455)
      | v2_struct_0(B_455)
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_224,plain,(
    ! [A_454,D_453] :
      ( k3_tmap_1(A_454,'#skF_2','#skF_4',D_453,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_453))
      | ~ m1_pre_topc(D_453,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_453,A_454)
      | ~ m1_pre_topc('#skF_4',A_454)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(resolution,[status(thm)],[c_32,c_222])).

tff(c_227,plain,(
    ! [A_454,D_453] :
      ( k3_tmap_1(A_454,'#skF_2','#skF_4',D_453,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_453))
      | ~ m1_pre_topc(D_453,'#skF_4')
      | ~ m1_pre_topc(D_453,A_454)
      | ~ m1_pre_topc('#skF_4',A_454)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_224])).

tff(c_229,plain,(
    ! [A_458,D_459] :
      ( k3_tmap_1(A_458,'#skF_2','#skF_4',D_459,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_459))
      | ~ m1_pre_topc(D_459,'#skF_4')
      | ~ m1_pre_topc(D_459,A_458)
      | ~ m1_pre_topc('#skF_4',A_458)
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458)
      | v2_struct_0(A_458) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_227])).

tff(c_235,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_229])).

tff(c_248,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_235])).

tff(c_249,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_248])).

tff(c_206,plain,(
    ! [A_448,B_449,C_450,D_451] :
      ( k2_partfun1(u1_struct_0(A_448),u1_struct_0(B_449),C_450,u1_struct_0(D_451)) = k2_tmap_1(A_448,B_449,C_450,D_451)
      | ~ m1_pre_topc(D_451,A_448)
      | ~ m1_subset_1(C_450,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_448),u1_struct_0(B_449))))
      | ~ v1_funct_2(C_450,u1_struct_0(A_448),u1_struct_0(B_449))
      | ~ v1_funct_1(C_450)
      | ~ l1_pre_topc(B_449)
      | ~ v2_pre_topc(B_449)
      | v2_struct_0(B_449)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | v2_struct_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_208,plain,(
    ! [D_451] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_451)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_451)
      | ~ m1_pre_topc(D_451,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_206])).

tff(c_211,plain,(
    ! [D_451] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_451)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_451)
      | ~ m1_pre_topc(D_451,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_89,c_48,c_46,c_36,c_34,c_208])).

tff(c_212,plain,(
    ! [D_451] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_451)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_451)
      | ~ m1_pre_topc(D_451,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_211])).

tff(c_261,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_212])).

tff(c_268,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_261])).

tff(c_64,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_219])).

tff(c_65,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_64])).

tff(c_153,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_65])).

tff(c_273,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_153])).

tff(c_321,plain,(
    ! [G_474,E_476,D_475,A_471,B_472,C_473] :
      ( r1_tmap_1(B_472,A_471,C_473,G_474)
      | ~ r1_tmap_1(D_475,A_471,k2_tmap_1(B_472,A_471,C_473,D_475),G_474)
      | ~ r1_tarski(E_476,u1_struct_0(D_475))
      | ~ r2_hidden(G_474,E_476)
      | ~ v3_pre_topc(E_476,B_472)
      | ~ m1_subset_1(G_474,u1_struct_0(D_475))
      | ~ m1_subset_1(G_474,u1_struct_0(B_472))
      | ~ m1_subset_1(E_476,k1_zfmisc_1(u1_struct_0(B_472)))
      | ~ m1_pre_topc(D_475,B_472)
      | v2_struct_0(D_475)
      | ~ m1_subset_1(C_473,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_472),u1_struct_0(A_471))))
      | ~ v1_funct_2(C_473,u1_struct_0(B_472),u1_struct_0(A_471))
      | ~ v1_funct_1(C_473)
      | ~ l1_pre_topc(B_472)
      | ~ v2_pre_topc(B_472)
      | v2_struct_0(B_472)
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_323,plain,(
    ! [E_476] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski(E_476,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_476)
      | ~ v3_pre_topc(E_476,'#skF_4')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_476,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_273,c_321])).

tff(c_326,plain,(
    ! [E_476] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski(E_476,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_476)
      | ~ v3_pre_topc(E_476,'#skF_4')
      | ~ m1_subset_1(E_476,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_110,c_89,c_36,c_34,c_32,c_30,c_67,c_24,c_323])).

tff(c_328,plain,(
    ! [E_477] :
      ( ~ r1_tarski(E_477,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_8',E_477)
      | ~ v3_pre_topc(E_477,'#skF_4')
      | ~ m1_subset_1(E_477,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_44,c_113,c_326])).

tff(c_331,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ v3_pre_topc('#skF_6','#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_328])).

tff(c_335,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_68,c_18,c_331])).

tff(c_337,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_533,plain,(
    ! [D_511,A_507,B_508,E_512,G_510,C_509] :
      ( r1_tmap_1(D_511,A_507,k2_tmap_1(B_508,A_507,C_509,D_511),G_510)
      | ~ r1_tmap_1(B_508,A_507,C_509,G_510)
      | ~ r1_tarski(E_512,u1_struct_0(D_511))
      | ~ r2_hidden(G_510,E_512)
      | ~ v3_pre_topc(E_512,B_508)
      | ~ m1_subset_1(G_510,u1_struct_0(D_511))
      | ~ m1_subset_1(G_510,u1_struct_0(B_508))
      | ~ m1_subset_1(E_512,k1_zfmisc_1(u1_struct_0(B_508)))
      | ~ m1_pre_topc(D_511,B_508)
      | v2_struct_0(D_511)
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_508),u1_struct_0(A_507))))
      | ~ v1_funct_2(C_509,u1_struct_0(B_508),u1_struct_0(A_507))
      | ~ v1_funct_1(C_509)
      | ~ l1_pre_topc(B_508)
      | ~ v2_pre_topc(B_508)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_535,plain,(
    ! [A_507,B_508,C_509,G_510] :
      ( r1_tmap_1('#skF_3',A_507,k2_tmap_1(B_508,A_507,C_509,'#skF_3'),G_510)
      | ~ r1_tmap_1(B_508,A_507,C_509,G_510)
      | ~ r2_hidden(G_510,'#skF_6')
      | ~ v3_pre_topc('#skF_6',B_508)
      | ~ m1_subset_1(G_510,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_510,u1_struct_0(B_508))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(B_508)))
      | ~ m1_pre_topc('#skF_3',B_508)
      | v2_struct_0('#skF_3')
      | ~ m1_subset_1(C_509,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_508),u1_struct_0(A_507))))
      | ~ v1_funct_2(C_509,u1_struct_0(B_508),u1_struct_0(A_507))
      | ~ v1_funct_1(C_509)
      | ~ l1_pre_topc(B_508)
      | ~ v2_pre_topc(B_508)
      | v2_struct_0(B_508)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(resolution,[status(thm)],[c_18,c_533])).

tff(c_539,plain,(
    ! [A_513,B_514,C_515,G_516] :
      ( r1_tmap_1('#skF_3',A_513,k2_tmap_1(B_514,A_513,C_515,'#skF_3'),G_516)
      | ~ r1_tmap_1(B_514,A_513,C_515,G_516)
      | ~ r2_hidden(G_516,'#skF_6')
      | ~ v3_pre_topc('#skF_6',B_514)
      | ~ m1_subset_1(G_516,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_516,u1_struct_0(B_514))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0(B_514)))
      | ~ m1_pre_topc('#skF_3',B_514)
      | ~ m1_subset_1(C_515,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_514),u1_struct_0(A_513))))
      | ~ v1_funct_2(C_515,u1_struct_0(B_514),u1_struct_0(A_513))
      | ~ v1_funct_1(C_515)
      | ~ l1_pre_topc(B_514)
      | ~ v2_pre_topc(B_514)
      | v2_struct_0(B_514)
      | ~ l1_pre_topc(A_513)
      | ~ v2_pre_topc(A_513)
      | v2_struct_0(A_513) ) ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_535])).

tff(c_541,plain,(
    ! [G_516] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_516)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_516)
      | ~ r2_hidden(G_516,'#skF_6')
      | ~ v3_pre_topc('#skF_6','#skF_4')
      | ~ m1_subset_1(G_516,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_516,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_539])).

tff(c_544,plain,(
    ! [G_516] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_516)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_516)
      | ~ r2_hidden(G_516,'#skF_6')
      | ~ m1_subset_1(G_516,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_516,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_110,c_89,c_36,c_34,c_30,c_28,c_22,c_541])).

tff(c_546,plain,(
    ! [G_517] :
      ( r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),G_517)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',G_517)
      | ~ r2_hidden(G_517,'#skF_6')
      | ~ m1_subset_1(G_517,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(G_517,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_40,c_544])).

tff(c_447,plain,(
    ! [D_493,A_494,C_497,E_496,B_495] :
      ( k3_tmap_1(A_494,B_495,C_497,D_493,E_496) = k2_partfun1(u1_struct_0(C_497),u1_struct_0(B_495),E_496,u1_struct_0(D_493))
      | ~ m1_pre_topc(D_493,C_497)
      | ~ m1_subset_1(E_496,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_497),u1_struct_0(B_495))))
      | ~ v1_funct_2(E_496,u1_struct_0(C_497),u1_struct_0(B_495))
      | ~ v1_funct_1(E_496)
      | ~ m1_pre_topc(D_493,A_494)
      | ~ m1_pre_topc(C_497,A_494)
      | ~ l1_pre_topc(B_495)
      | ~ v2_pre_topc(B_495)
      | v2_struct_0(B_495)
      | ~ l1_pre_topc(A_494)
      | ~ v2_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_449,plain,(
    ! [A_494,D_493] :
      ( k3_tmap_1(A_494,'#skF_2','#skF_4',D_493,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_493))
      | ~ m1_pre_topc(D_493,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_493,A_494)
      | ~ m1_pre_topc('#skF_4',A_494)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_494)
      | ~ v2_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(resolution,[status(thm)],[c_32,c_447])).

tff(c_452,plain,(
    ! [A_494,D_493] :
      ( k3_tmap_1(A_494,'#skF_2','#skF_4',D_493,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_493))
      | ~ m1_pre_topc(D_493,'#skF_4')
      | ~ m1_pre_topc(D_493,A_494)
      | ~ m1_pre_topc('#skF_4',A_494)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_494)
      | ~ v2_pre_topc(A_494)
      | v2_struct_0(A_494) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_36,c_34,c_449])).

tff(c_454,plain,(
    ! [A_498,D_499] :
      ( k3_tmap_1(A_498,'#skF_2','#skF_4',D_499,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_499))
      | ~ m1_pre_topc(D_499,'#skF_4')
      | ~ m1_pre_topc(D_499,A_498)
      | ~ m1_pre_topc('#skF_4',A_498)
      | ~ l1_pre_topc(A_498)
      | ~ v2_pre_topc(A_498)
      | v2_struct_0(A_498) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_452])).

tff(c_460,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_454])).

tff(c_473,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_52,c_38,c_30,c_460])).

tff(c_474,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_473])).

tff(c_405,plain,(
    ! [A_486,B_487,C_488,D_489] :
      ( k2_partfun1(u1_struct_0(A_486),u1_struct_0(B_487),C_488,u1_struct_0(D_489)) = k2_tmap_1(A_486,B_487,C_488,D_489)
      | ~ m1_pre_topc(D_489,A_486)
      | ~ m1_subset_1(C_488,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_486),u1_struct_0(B_487))))
      | ~ v1_funct_2(C_488,u1_struct_0(A_486),u1_struct_0(B_487))
      | ~ v1_funct_1(C_488)
      | ~ l1_pre_topc(B_487)
      | ~ v2_pre_topc(B_487)
      | v2_struct_0(B_487)
      | ~ l1_pre_topc(A_486)
      | ~ v2_pre_topc(A_486)
      | v2_struct_0(A_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_407,plain,(
    ! [D_489] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_489)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_489)
      | ~ m1_pre_topc(D_489,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_32,c_405])).

tff(c_410,plain,(
    ! [D_489] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_489)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_489)
      | ~ m1_pre_topc(D_489,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_89,c_48,c_46,c_36,c_34,c_407])).

tff(c_411,plain,(
    ! [D_489] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_489)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_489)
      | ~ m1_pre_topc(D_489,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_50,c_410])).

tff(c_486,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_411])).

tff(c_493,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_486])).

tff(c_336,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_498,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_336])).

tff(c_551,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | ~ r2_hidden('#skF_8','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_546,c_498])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_67,c_24,c_68,c_337,c_551])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:17:23 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.22/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  
% 3.22/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.49  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.22/1.49  
% 3.22/1.49  %Foreground sorts:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Background operators:
% 3.22/1.49  
% 3.22/1.49  
% 3.22/1.49  %Foreground operators:
% 3.22/1.49  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.22/1.49  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.22/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.22/1.49  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.22/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.22/1.49  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.22/1.49  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.22/1.49  tff('#skF_7', type, '#skF_7': $i).
% 3.22/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.22/1.49  tff('#skF_5', type, '#skF_5': $i).
% 3.22/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.22/1.49  tff('#skF_6', type, '#skF_6': $i).
% 3.22/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.22/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.22/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.22/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.22/1.49  tff('#skF_8', type, '#skF_8': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.22/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.22/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.22/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.22/1.49  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.22/1.49  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.22/1.49  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.22/1.49  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.22/1.49  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.22/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.22/1.49  
% 3.22/1.51  tff(f_219, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.22/1.51  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.22/1.51  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.22/1.51  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.22/1.51  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.22/1.51  tff(f_149, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((v3_pre_topc(E, B) & r2_hidden(F, E)) & r1_tarski(E, u1_struct_0(D))) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_tmap_1)).
% 3.22/1.51  tff(c_16, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_26, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_67, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26])).
% 3.22/1.51  tff(c_24, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_20, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_68, plain, (r2_hidden('#skF_8', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 3.22/1.51  tff(c_22, plain, (v3_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_18, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_28, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_50, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_40, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_44, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_58, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_66, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_58])).
% 3.22/1.51  tff(c_113, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_66])).
% 3.22/1.51  tff(c_48, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_46, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_54, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_52, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_38, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_92, plain, (![B_436, A_437]: (v2_pre_topc(B_436) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.22/1.51  tff(c_101, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_92])).
% 3.22/1.51  tff(c_110, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_101])).
% 3.22/1.51  tff(c_73, plain, (![B_434, A_435]: (l1_pre_topc(B_434) | ~m1_pre_topc(B_434, A_435) | ~l1_pre_topc(A_435))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.22/1.51  tff(c_82, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_38, c_73])).
% 3.22/1.51  tff(c_89, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_82])).
% 3.22/1.51  tff(c_36, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_34, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_32, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_30, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_56, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_42, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_222, plain, (![C_457, A_454, B_455, D_453, E_456]: (k3_tmap_1(A_454, B_455, C_457, D_453, E_456)=k2_partfun1(u1_struct_0(C_457), u1_struct_0(B_455), E_456, u1_struct_0(D_453)) | ~m1_pre_topc(D_453, C_457) | ~m1_subset_1(E_456, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_457), u1_struct_0(B_455)))) | ~v1_funct_2(E_456, u1_struct_0(C_457), u1_struct_0(B_455)) | ~v1_funct_1(E_456) | ~m1_pre_topc(D_453, A_454) | ~m1_pre_topc(C_457, A_454) | ~l1_pre_topc(B_455) | ~v2_pre_topc(B_455) | v2_struct_0(B_455) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.22/1.51  tff(c_224, plain, (![A_454, D_453]: (k3_tmap_1(A_454, '#skF_2', '#skF_4', D_453, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_453)) | ~m1_pre_topc(D_453, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_453, A_454) | ~m1_pre_topc('#skF_4', A_454) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(resolution, [status(thm)], [c_32, c_222])).
% 3.22/1.51  tff(c_227, plain, (![A_454, D_453]: (k3_tmap_1(A_454, '#skF_2', '#skF_4', D_453, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_453)) | ~m1_pre_topc(D_453, '#skF_4') | ~m1_pre_topc(D_453, A_454) | ~m1_pre_topc('#skF_4', A_454) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_224])).
% 3.22/1.51  tff(c_229, plain, (![A_458, D_459]: (k3_tmap_1(A_458, '#skF_2', '#skF_4', D_459, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_459)) | ~m1_pre_topc(D_459, '#skF_4') | ~m1_pre_topc(D_459, A_458) | ~m1_pre_topc('#skF_4', A_458) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458) | v2_struct_0(A_458))), inference(negUnitSimplification, [status(thm)], [c_50, c_227])).
% 3.22/1.51  tff(c_235, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_229])).
% 3.22/1.51  tff(c_248, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_235])).
% 3.22/1.51  tff(c_249, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_248])).
% 3.22/1.51  tff(c_206, plain, (![A_448, B_449, C_450, D_451]: (k2_partfun1(u1_struct_0(A_448), u1_struct_0(B_449), C_450, u1_struct_0(D_451))=k2_tmap_1(A_448, B_449, C_450, D_451) | ~m1_pre_topc(D_451, A_448) | ~m1_subset_1(C_450, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_448), u1_struct_0(B_449)))) | ~v1_funct_2(C_450, u1_struct_0(A_448), u1_struct_0(B_449)) | ~v1_funct_1(C_450) | ~l1_pre_topc(B_449) | ~v2_pre_topc(B_449) | v2_struct_0(B_449) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | v2_struct_0(A_448))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.22/1.51  tff(c_208, plain, (![D_451]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_451))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_451) | ~m1_pre_topc(D_451, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_206])).
% 3.22/1.51  tff(c_211, plain, (![D_451]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_451))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_451) | ~m1_pre_topc(D_451, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_89, c_48, c_46, c_36, c_34, c_208])).
% 3.22/1.51  tff(c_212, plain, (![D_451]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_451))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_451) | ~m1_pre_topc(D_451, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_211])).
% 3.22/1.51  tff(c_261, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_249, c_212])).
% 3.22/1.51  tff(c_268, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_261])).
% 3.22/1.51  tff(c_64, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_219])).
% 3.22/1.51  tff(c_65, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_64])).
% 3.22/1.51  tff(c_153, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_113, c_65])).
% 3.22/1.51  tff(c_273, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_268, c_153])).
% 3.22/1.51  tff(c_321, plain, (![G_474, E_476, D_475, A_471, B_472, C_473]: (r1_tmap_1(B_472, A_471, C_473, G_474) | ~r1_tmap_1(D_475, A_471, k2_tmap_1(B_472, A_471, C_473, D_475), G_474) | ~r1_tarski(E_476, u1_struct_0(D_475)) | ~r2_hidden(G_474, E_476) | ~v3_pre_topc(E_476, B_472) | ~m1_subset_1(G_474, u1_struct_0(D_475)) | ~m1_subset_1(G_474, u1_struct_0(B_472)) | ~m1_subset_1(E_476, k1_zfmisc_1(u1_struct_0(B_472))) | ~m1_pre_topc(D_475, B_472) | v2_struct_0(D_475) | ~m1_subset_1(C_473, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_472), u1_struct_0(A_471)))) | ~v1_funct_2(C_473, u1_struct_0(B_472), u1_struct_0(A_471)) | ~v1_funct_1(C_473) | ~l1_pre_topc(B_472) | ~v2_pre_topc(B_472) | v2_struct_0(B_472) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.22/1.51  tff(c_323, plain, (![E_476]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski(E_476, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_476) | ~v3_pre_topc(E_476, '#skF_4') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_476, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_273, c_321])).
% 3.22/1.51  tff(c_326, plain, (![E_476]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski(E_476, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_476) | ~v3_pre_topc(E_476, '#skF_4') | ~m1_subset_1(E_476, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_110, c_89, c_36, c_34, c_32, c_30, c_67, c_24, c_323])).
% 3.22/1.51  tff(c_328, plain, (![E_477]: (~r1_tarski(E_477, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', E_477) | ~v3_pre_topc(E_477, '#skF_4') | ~m1_subset_1(E_477, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_44, c_113, c_326])).
% 3.22/1.51  tff(c_331, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~r2_hidden('#skF_8', '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4')), inference(resolution, [status(thm)], [c_28, c_328])).
% 3.22/1.51  tff(c_335, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_68, c_18, c_331])).
% 3.22/1.51  tff(c_337, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.22/1.51  tff(c_533, plain, (![D_511, A_507, B_508, E_512, G_510, C_509]: (r1_tmap_1(D_511, A_507, k2_tmap_1(B_508, A_507, C_509, D_511), G_510) | ~r1_tmap_1(B_508, A_507, C_509, G_510) | ~r1_tarski(E_512, u1_struct_0(D_511)) | ~r2_hidden(G_510, E_512) | ~v3_pre_topc(E_512, B_508) | ~m1_subset_1(G_510, u1_struct_0(D_511)) | ~m1_subset_1(G_510, u1_struct_0(B_508)) | ~m1_subset_1(E_512, k1_zfmisc_1(u1_struct_0(B_508))) | ~m1_pre_topc(D_511, B_508) | v2_struct_0(D_511) | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_508), u1_struct_0(A_507)))) | ~v1_funct_2(C_509, u1_struct_0(B_508), u1_struct_0(A_507)) | ~v1_funct_1(C_509) | ~l1_pre_topc(B_508) | ~v2_pre_topc(B_508) | v2_struct_0(B_508) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_149])).
% 3.22/1.51  tff(c_535, plain, (![A_507, B_508, C_509, G_510]: (r1_tmap_1('#skF_3', A_507, k2_tmap_1(B_508, A_507, C_509, '#skF_3'), G_510) | ~r1_tmap_1(B_508, A_507, C_509, G_510) | ~r2_hidden(G_510, '#skF_6') | ~v3_pre_topc('#skF_6', B_508) | ~m1_subset_1(G_510, u1_struct_0('#skF_3')) | ~m1_subset_1(G_510, u1_struct_0(B_508)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(B_508))) | ~m1_pre_topc('#skF_3', B_508) | v2_struct_0('#skF_3') | ~m1_subset_1(C_509, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_508), u1_struct_0(A_507)))) | ~v1_funct_2(C_509, u1_struct_0(B_508), u1_struct_0(A_507)) | ~v1_funct_1(C_509) | ~l1_pre_topc(B_508) | ~v2_pre_topc(B_508) | v2_struct_0(B_508) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(resolution, [status(thm)], [c_18, c_533])).
% 3.22/1.51  tff(c_539, plain, (![A_513, B_514, C_515, G_516]: (r1_tmap_1('#skF_3', A_513, k2_tmap_1(B_514, A_513, C_515, '#skF_3'), G_516) | ~r1_tmap_1(B_514, A_513, C_515, G_516) | ~r2_hidden(G_516, '#skF_6') | ~v3_pre_topc('#skF_6', B_514) | ~m1_subset_1(G_516, u1_struct_0('#skF_3')) | ~m1_subset_1(G_516, u1_struct_0(B_514)) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0(B_514))) | ~m1_pre_topc('#skF_3', B_514) | ~m1_subset_1(C_515, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_514), u1_struct_0(A_513)))) | ~v1_funct_2(C_515, u1_struct_0(B_514), u1_struct_0(A_513)) | ~v1_funct_1(C_515) | ~l1_pre_topc(B_514) | ~v2_pre_topc(B_514) | v2_struct_0(B_514) | ~l1_pre_topc(A_513) | ~v2_pre_topc(A_513) | v2_struct_0(A_513))), inference(negUnitSimplification, [status(thm)], [c_44, c_535])).
% 3.22/1.51  tff(c_541, plain, (![G_516]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_516) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_516) | ~r2_hidden(G_516, '#skF_6') | ~v3_pre_topc('#skF_6', '#skF_4') | ~m1_subset_1(G_516, u1_struct_0('#skF_3')) | ~m1_subset_1(G_516, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_539])).
% 3.22/1.51  tff(c_544, plain, (![G_516]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_516) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_516) | ~r2_hidden(G_516, '#skF_6') | ~m1_subset_1(G_516, u1_struct_0('#skF_3')) | ~m1_subset_1(G_516, u1_struct_0('#skF_4')) | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_110, c_89, c_36, c_34, c_30, c_28, c_22, c_541])).
% 3.22/1.51  tff(c_546, plain, (![G_517]: (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), G_517) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', G_517) | ~r2_hidden(G_517, '#skF_6') | ~m1_subset_1(G_517, u1_struct_0('#skF_3')) | ~m1_subset_1(G_517, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_50, c_40, c_544])).
% 3.22/1.51  tff(c_447, plain, (![D_493, A_494, C_497, E_496, B_495]: (k3_tmap_1(A_494, B_495, C_497, D_493, E_496)=k2_partfun1(u1_struct_0(C_497), u1_struct_0(B_495), E_496, u1_struct_0(D_493)) | ~m1_pre_topc(D_493, C_497) | ~m1_subset_1(E_496, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_497), u1_struct_0(B_495)))) | ~v1_funct_2(E_496, u1_struct_0(C_497), u1_struct_0(B_495)) | ~v1_funct_1(E_496) | ~m1_pre_topc(D_493, A_494) | ~m1_pre_topc(C_497, A_494) | ~l1_pre_topc(B_495) | ~v2_pre_topc(B_495) | v2_struct_0(B_495) | ~l1_pre_topc(A_494) | ~v2_pre_topc(A_494) | v2_struct_0(A_494))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.22/1.51  tff(c_449, plain, (![A_494, D_493]: (k3_tmap_1(A_494, '#skF_2', '#skF_4', D_493, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_493)) | ~m1_pre_topc(D_493, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_493, A_494) | ~m1_pre_topc('#skF_4', A_494) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_494) | ~v2_pre_topc(A_494) | v2_struct_0(A_494))), inference(resolution, [status(thm)], [c_32, c_447])).
% 3.22/1.51  tff(c_452, plain, (![A_494, D_493]: (k3_tmap_1(A_494, '#skF_2', '#skF_4', D_493, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_493)) | ~m1_pre_topc(D_493, '#skF_4') | ~m1_pre_topc(D_493, A_494) | ~m1_pre_topc('#skF_4', A_494) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_494) | ~v2_pre_topc(A_494) | v2_struct_0(A_494))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_36, c_34, c_449])).
% 3.22/1.51  tff(c_454, plain, (![A_498, D_499]: (k3_tmap_1(A_498, '#skF_2', '#skF_4', D_499, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_499)) | ~m1_pre_topc(D_499, '#skF_4') | ~m1_pre_topc(D_499, A_498) | ~m1_pre_topc('#skF_4', A_498) | ~l1_pre_topc(A_498) | ~v2_pre_topc(A_498) | v2_struct_0(A_498))), inference(negUnitSimplification, [status(thm)], [c_50, c_452])).
% 3.22/1.51  tff(c_460, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_42, c_454])).
% 3.22/1.51  tff(c_473, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_52, c_38, c_30, c_460])).
% 3.22/1.51  tff(c_474, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_56, c_473])).
% 3.22/1.51  tff(c_405, plain, (![A_486, B_487, C_488, D_489]: (k2_partfun1(u1_struct_0(A_486), u1_struct_0(B_487), C_488, u1_struct_0(D_489))=k2_tmap_1(A_486, B_487, C_488, D_489) | ~m1_pre_topc(D_489, A_486) | ~m1_subset_1(C_488, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_486), u1_struct_0(B_487)))) | ~v1_funct_2(C_488, u1_struct_0(A_486), u1_struct_0(B_487)) | ~v1_funct_1(C_488) | ~l1_pre_topc(B_487) | ~v2_pre_topc(B_487) | v2_struct_0(B_487) | ~l1_pre_topc(A_486) | ~v2_pre_topc(A_486) | v2_struct_0(A_486))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.22/1.51  tff(c_407, plain, (![D_489]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_489))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_489) | ~m1_pre_topc(D_489, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_32, c_405])).
% 3.22/1.51  tff(c_410, plain, (![D_489]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_489))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_489) | ~m1_pre_topc(D_489, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_89, c_48, c_46, c_36, c_34, c_407])).
% 3.22/1.51  tff(c_411, plain, (![D_489]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_489))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_489) | ~m1_pre_topc(D_489, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_40, c_50, c_410])).
% 3.22/1.51  tff(c_486, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_474, c_411])).
% 3.22/1.51  tff(c_493, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_486])).
% 3.22/1.51  tff(c_336, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_66])).
% 3.22/1.51  tff(c_498, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_336])).
% 3.22/1.51  tff(c_551, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r2_hidden('#skF_8', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_546, c_498])).
% 3.22/1.51  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_67, c_24, c_68, c_337, c_551])).
% 3.22/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.22/1.51  
% 3.22/1.51  Inference rules
% 3.22/1.51  ----------------------
% 3.22/1.51  #Ref     : 0
% 3.22/1.51  #Sup     : 94
% 3.22/1.51  #Fact    : 0
% 3.22/1.51  #Define  : 0
% 3.22/1.51  #Split   : 4
% 3.22/1.51  #Chain   : 0
% 3.22/1.51  #Close   : 0
% 3.22/1.51  
% 3.22/1.51  Ordering : KBO
% 3.22/1.51  
% 3.22/1.51  Simplification rules
% 3.22/1.51  ----------------------
% 3.22/1.51  #Subsume      : 12
% 3.22/1.51  #Demod        : 213
% 3.22/1.51  #Tautology    : 52
% 3.22/1.51  #SimpNegUnit  : 20
% 3.22/1.51  #BackRed      : 4
% 3.22/1.51  
% 3.22/1.51  #Partial instantiations: 0
% 3.22/1.51  #Strategies tried      : 1
% 3.22/1.51  
% 3.22/1.51  Timing (in seconds)
% 3.22/1.51  ----------------------
% 3.22/1.52  Preprocessing        : 0.39
% 3.22/1.52  Parsing              : 0.19
% 3.22/1.52  CNF conversion       : 0.06
% 3.22/1.52  Main loop            : 0.33
% 3.22/1.52  Inferencing          : 0.11
% 3.22/1.52  Reduction            : 0.12
% 3.22/1.52  Demodulation         : 0.09
% 3.22/1.52  BG Simplification    : 0.02
% 3.22/1.52  Subsumption          : 0.06
% 3.22/1.52  Abstraction          : 0.01
% 3.22/1.52  MUC search           : 0.00
% 3.22/1.52  Cooper               : 0.00
% 3.22/1.52  Total                : 0.76
% 3.22/1.52  Index Insertion      : 0.00
% 3.22/1.52  Index Deletion       : 0.00
% 3.22/1.52  Index Matching       : 0.00
% 3.22/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
