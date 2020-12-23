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
% DateTime   : Thu Dec  3 10:27:21 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 327 expanded)
%              Number of leaves         :   33 ( 143 expanded)
%              Depth                    :   15
%              Number of atoms          :  416 (2836 expanded)
%              Number of equality atoms :   31 ( 143 expanded)
%              Maximal formula depth    :   25 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_215,negated_conjecture,(
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
                                     => ( ( r1_tarski(F,u1_struct_0(C))
                                          & m1_connsp_2(F,D,G)
                                          & G = H )
                                       => ( r1_tmap_1(D,B,E,G)
                                        <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_147,axiom,(
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
                             => ( ( r1_tarski(E,u1_struct_0(D))
                                  & m1_connsp_2(E,B,F)
                                  & F = G )
                               => ( r1_tmap_1(B,A,C,F)
                                <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),G) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tmap_1)).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_22,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_20,plain,(
    r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_48,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_46,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_44,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_34,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_32,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_16,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_18,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_66,plain,(
    m1_connsp_2('#skF_6','#skF_4','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_38,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_56,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_64,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_56])).

tff(c_150,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_52,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_50,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_36,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_90,plain,(
    ! [B_436,A_437] :
      ( v2_pre_topc(B_436)
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_99,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_90])).

tff(c_108,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_99])).

tff(c_71,plain,(
    ! [B_434,A_435] :
      ( l1_pre_topc(B_434)
      | ~ m1_pre_topc(B_434,A_435)
      | ~ l1_pre_topc(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_71])).

tff(c_87,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_80])).

tff(c_30,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_65,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_220,plain,(
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

tff(c_222,plain,(
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
    inference(resolution,[status(thm)],[c_30,c_220])).

tff(c_225,plain,(
    ! [A_454,D_453] :
      ( k3_tmap_1(A_454,'#skF_2','#skF_4',D_453,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_453))
      | ~ m1_pre_topc(D_453,'#skF_4')
      | ~ m1_pre_topc(D_453,A_454)
      | ~ m1_pre_topc('#skF_4',A_454)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_454)
      | ~ v2_pre_topc(A_454)
      | v2_struct_0(A_454) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_222])).

tff(c_227,plain,(
    ! [A_458,D_459] :
      ( k3_tmap_1(A_458,'#skF_2','#skF_4',D_459,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_459))
      | ~ m1_pre_topc(D_459,'#skF_4')
      | ~ m1_pre_topc(D_459,A_458)
      | ~ m1_pre_topc('#skF_4',A_458)
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458)
      | v2_struct_0(A_458) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_225])).

tff(c_235,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_227])).

tff(c_250,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_28,c_235])).

tff(c_251,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_250])).

tff(c_152,plain,(
    ! [A_444,B_445,C_446,D_447] :
      ( k2_partfun1(u1_struct_0(A_444),u1_struct_0(B_445),C_446,u1_struct_0(D_447)) = k2_tmap_1(A_444,B_445,C_446,D_447)
      | ~ m1_pre_topc(D_447,A_444)
      | ~ m1_subset_1(C_446,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_444),u1_struct_0(B_445))))
      | ~ v1_funct_2(C_446,u1_struct_0(A_444),u1_struct_0(B_445))
      | ~ v1_funct_1(C_446)
      | ~ l1_pre_topc(B_445)
      | ~ v2_pre_topc(B_445)
      | v2_struct_0(B_445)
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_154,plain,(
    ! [D_447] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_447)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_447)
      | ~ m1_pre_topc(D_447,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_152])).

tff(c_157,plain,(
    ! [D_447] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_447)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_447)
      | ~ m1_pre_topc(D_447,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_87,c_46,c_44,c_34,c_32,c_154])).

tff(c_158,plain,(
    ! [D_447] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_447)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_447)
      | ~ m1_pre_topc(D_447,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_48,c_157])).

tff(c_259,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_158])).

tff(c_266,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_259])).

tff(c_62,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_7')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_215])).

tff(c_63,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_62])).

tff(c_151,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_150,c_63])).

tff(c_271,plain,(
    r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_266,c_151])).

tff(c_319,plain,(
    ! [A_470,G_473,C_472,B_471,D_474,E_475] :
      ( r1_tmap_1(B_471,A_470,C_472,G_473)
      | ~ r1_tmap_1(D_474,A_470,k2_tmap_1(B_471,A_470,C_472,D_474),G_473)
      | ~ m1_connsp_2(E_475,B_471,G_473)
      | ~ r1_tarski(E_475,u1_struct_0(D_474))
      | ~ m1_subset_1(G_473,u1_struct_0(D_474))
      | ~ m1_subset_1(G_473,u1_struct_0(B_471))
      | ~ m1_subset_1(E_475,k1_zfmisc_1(u1_struct_0(B_471)))
      | ~ m1_pre_topc(D_474,B_471)
      | v2_struct_0(D_474)
      | ~ m1_subset_1(C_472,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_471),u1_struct_0(A_470))))
      | ~ v1_funct_2(C_472,u1_struct_0(B_471),u1_struct_0(A_470))
      | ~ v1_funct_1(C_472)
      | ~ l1_pre_topc(B_471)
      | ~ v2_pre_topc(B_471)
      | v2_struct_0(B_471)
      | ~ l1_pre_topc(A_470)
      | ~ v2_pre_topc(A_470)
      | v2_struct_0(A_470) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_321,plain,(
    ! [E_475] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_475,'#skF_4','#skF_8')
      | ~ r1_tarski(E_475,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(E_475,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_271,c_319])).

tff(c_324,plain,(
    ! [E_475] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ m1_connsp_2(E_475,'#skF_4','#skF_8')
      | ~ r1_tarski(E_475,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_475,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_108,c_87,c_34,c_32,c_30,c_28,c_65,c_22,c_321])).

tff(c_326,plain,(
    ! [E_476] :
      ( ~ m1_connsp_2(E_476,'#skF_4','#skF_8')
      | ~ r1_tarski(E_476,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(E_476,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_38,c_42,c_150,c_324])).

tff(c_329,plain,
    ( ~ m1_connsp_2('#skF_6','#skF_4','#skF_8')
    | ~ r1_tarski('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_326])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_66,c_329])).

tff(c_335,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_456,plain,(
    ! [D_497,B_494,A_493,E_498,C_495,G_496] :
      ( r1_tmap_1(D_497,A_493,k2_tmap_1(B_494,A_493,C_495,D_497),G_496)
      | ~ r1_tmap_1(B_494,A_493,C_495,G_496)
      | ~ m1_connsp_2(E_498,B_494,G_496)
      | ~ r1_tarski(E_498,u1_struct_0(D_497))
      | ~ m1_subset_1(G_496,u1_struct_0(D_497))
      | ~ m1_subset_1(G_496,u1_struct_0(B_494))
      | ~ m1_subset_1(E_498,k1_zfmisc_1(u1_struct_0(B_494)))
      | ~ m1_pre_topc(D_497,B_494)
      | v2_struct_0(D_497)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_494),u1_struct_0(A_493))))
      | ~ v1_funct_2(C_495,u1_struct_0(B_494),u1_struct_0(A_493))
      | ~ v1_funct_1(C_495)
      | ~ l1_pre_topc(B_494)
      | ~ v2_pre_topc(B_494)
      | v2_struct_0(B_494)
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_458,plain,(
    ! [D_497,A_493,C_495] :
      ( r1_tmap_1(D_497,A_493,k2_tmap_1('#skF_4',A_493,C_495,D_497),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_493,C_495,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_497))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_497))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc(D_497,'#skF_4')
      | v2_struct_0(D_497)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_493))))
      | ~ v1_funct_2(C_495,u1_struct_0('#skF_4'),u1_struct_0(A_493))
      | ~ v1_funct_1(C_495)
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493) ) ),
    inference(resolution,[status(thm)],[c_66,c_456])).

tff(c_461,plain,(
    ! [D_497,A_493,C_495] :
      ( r1_tmap_1(D_497,A_493,k2_tmap_1('#skF_4',A_493,C_495,D_497),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_493,C_495,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_497))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_497))
      | ~ m1_pre_topc(D_497,'#skF_4')
      | v2_struct_0(D_497)
      | ~ m1_subset_1(C_495,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_493))))
      | ~ v1_funct_2(C_495,u1_struct_0('#skF_4'),u1_struct_0(A_493))
      | ~ v1_funct_1(C_495)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc(A_493)
      | ~ v2_pre_topc(A_493)
      | v2_struct_0(A_493) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_87,c_26,c_65,c_458])).

tff(c_499,plain,(
    ! [D_506,A_507,C_508] :
      ( r1_tmap_1(D_506,A_507,k2_tmap_1('#skF_4',A_507,C_508,D_506),'#skF_8')
      | ~ r1_tmap_1('#skF_4',A_507,C_508,'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_506))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_506))
      | ~ m1_pre_topc(D_506,'#skF_4')
      | v2_struct_0(D_506)
      | ~ m1_subset_1(C_508,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0(A_507))))
      | ~ v1_funct_2(C_508,u1_struct_0('#skF_4'),u1_struct_0(A_507))
      | ~ v1_funct_1(C_508)
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_461])).

tff(c_501,plain,(
    ! [D_506] :
      ( r1_tmap_1(D_506,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_506),'#skF_8')
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_506))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_506))
      | ~ m1_pre_topc(D_506,'#skF_4')
      | v2_struct_0(D_506)
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_499])).

tff(c_504,plain,(
    ! [D_506] :
      ( r1_tmap_1(D_506,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_506),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_506))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_506))
      | ~ m1_pre_topc(D_506,'#skF_4')
      | v2_struct_0(D_506)
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_335,c_501])).

tff(c_506,plain,(
    ! [D_509] :
      ( r1_tmap_1(D_509,'#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5',D_509),'#skF_8')
      | ~ r1_tarski('#skF_6',u1_struct_0(D_509))
      | ~ m1_subset_1('#skF_8',u1_struct_0(D_509))
      | ~ m1_pre_topc(D_509,'#skF_4')
      | v2_struct_0(D_509) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_504])).

tff(c_406,plain,(
    ! [A_487,D_486,B_488,E_489,C_490] :
      ( k3_tmap_1(A_487,B_488,C_490,D_486,E_489) = k2_partfun1(u1_struct_0(C_490),u1_struct_0(B_488),E_489,u1_struct_0(D_486))
      | ~ m1_pre_topc(D_486,C_490)
      | ~ m1_subset_1(E_489,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_490),u1_struct_0(B_488))))
      | ~ v1_funct_2(E_489,u1_struct_0(C_490),u1_struct_0(B_488))
      | ~ v1_funct_1(E_489)
      | ~ m1_pre_topc(D_486,A_487)
      | ~ m1_pre_topc(C_490,A_487)
      | ~ l1_pre_topc(B_488)
      | ~ v2_pre_topc(B_488)
      | v2_struct_0(B_488)
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_408,plain,(
    ! [A_487,D_486] :
      ( k3_tmap_1(A_487,'#skF_2','#skF_4',D_486,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_486))
      | ~ m1_pre_topc(D_486,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_486,A_487)
      | ~ m1_pre_topc('#skF_4',A_487)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(resolution,[status(thm)],[c_30,c_406])).

tff(c_411,plain,(
    ! [A_487,D_486] :
      ( k3_tmap_1(A_487,'#skF_2','#skF_4',D_486,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_486))
      | ~ m1_pre_topc(D_486,'#skF_4')
      | ~ m1_pre_topc(D_486,A_487)
      | ~ m1_pre_topc('#skF_4',A_487)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44,c_34,c_32,c_408])).

tff(c_413,plain,(
    ! [A_491,D_492] :
      ( k3_tmap_1(A_491,'#skF_2','#skF_4',D_492,'#skF_5') = k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_492))
      | ~ m1_pre_topc(D_492,'#skF_4')
      | ~ m1_pre_topc(D_492,A_491)
      | ~ m1_pre_topc('#skF_4',A_491)
      | ~ l1_pre_topc(A_491)
      | ~ v2_pre_topc(A_491)
      | v2_struct_0(A_491) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_411])).

tff(c_421,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_413])).

tff(c_436,plain,
    ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50,c_36,c_28,c_421])).

tff(c_437,plain,(
    k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0('#skF_3')) = k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_436])).

tff(c_390,plain,(
    ! [A_481,B_482,C_483,D_484] :
      ( k2_partfun1(u1_struct_0(A_481),u1_struct_0(B_482),C_483,u1_struct_0(D_484)) = k2_tmap_1(A_481,B_482,C_483,D_484)
      | ~ m1_pre_topc(D_484,A_481)
      | ~ m1_subset_1(C_483,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_481),u1_struct_0(B_482))))
      | ~ v1_funct_2(C_483,u1_struct_0(A_481),u1_struct_0(B_482))
      | ~ v1_funct_1(C_483)
      | ~ l1_pre_topc(B_482)
      | ~ v2_pre_topc(B_482)
      | v2_struct_0(B_482)
      | ~ l1_pre_topc(A_481)
      | ~ v2_pre_topc(A_481)
      | v2_struct_0(A_481) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_392,plain,(
    ! [D_484] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_484)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_484)
      | ~ m1_pre_topc(D_484,'#skF_4')
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_390])).

tff(c_395,plain,(
    ! [D_484] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_484)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_484)
      | ~ m1_pre_topc(D_484,'#skF_4')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_87,c_46,c_44,c_34,c_32,c_392])).

tff(c_396,plain,(
    ! [D_484] :
      ( k2_partfun1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'),'#skF_5',u1_struct_0(D_484)) = k2_tmap_1('#skF_4','#skF_2','#skF_5',D_484)
      | ~ m1_pre_topc(D_484,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_48,c_395])).

tff(c_445,plain,
    ( k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_437,c_396])).

tff(c_452,plain,(
    k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5') = k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_445])).

tff(c_334,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_464,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k2_tmap_1('#skF_4','#skF_2','#skF_5','#skF_3'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_334])).

tff(c_511,plain,
    ( ~ r1_tarski('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_506,c_464])).

tff(c_518,plain,(
    v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_20,c_511])).

tff(c_520,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:56:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.95/1.47  
% 2.95/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.47  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 3.11/1.47  
% 3.11/1.47  %Foreground sorts:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Background operators:
% 3.11/1.47  
% 3.11/1.47  
% 3.11/1.47  %Foreground operators:
% 3.11/1.47  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.11/1.47  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.11/1.47  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.11/1.47  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.11/1.47  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.11/1.47  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.11/1.47  tff('#skF_7', type, '#skF_7': $i).
% 3.11/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.11/1.47  tff('#skF_5', type, '#skF_5': $i).
% 3.11/1.47  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.11/1.47  tff('#skF_6', type, '#skF_6': $i).
% 3.11/1.47  tff('#skF_2', type, '#skF_2': $i).
% 3.11/1.47  tff('#skF_3', type, '#skF_3': $i).
% 3.11/1.47  tff('#skF_1', type, '#skF_1': $i).
% 3.11/1.47  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.11/1.47  tff('#skF_8', type, '#skF_8': $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.11/1.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.11/1.47  tff('#skF_4', type, '#skF_4': $i).
% 3.11/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.11/1.47  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.11/1.47  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 3.11/1.47  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.11/1.47  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 3.11/1.47  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.11/1.47  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.11/1.47  
% 3.11/1.49  tff(f_215, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.11/1.49  tff(f_34, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.11/1.49  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.11/1.49  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 3.11/1.49  tff(f_68, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 3.11/1.49  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(u1_struct_0(B))) => (![F]: (m1_subset_1(F, u1_struct_0(B)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (((r1_tarski(E, u1_struct_0(D)) & m1_connsp_2(E, B, F)) & (F = G)) => (r1_tmap_1(B, A, C, F) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), G))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_tmap_1)).
% 3.11/1.49  tff(c_42, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_22, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_20, plain, (r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_48, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_46, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_44, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_34, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_32, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_16, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_18, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_66, plain, (m1_connsp_2('#skF_6', '#skF_4', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 3.11/1.49  tff(c_26, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4')))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_38, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_56, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_64, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_56])).
% 3.11/1.49  tff(c_150, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitLeft, [status(thm)], [c_64])).
% 3.11/1.49  tff(c_52, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_50, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_36, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_90, plain, (![B_436, A_437]: (v2_pre_topc(B_436) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.11/1.49  tff(c_99, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_90])).
% 3.11/1.49  tff(c_108, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_99])).
% 3.11/1.49  tff(c_71, plain, (![B_434, A_435]: (l1_pre_topc(B_434) | ~m1_pre_topc(B_434, A_435) | ~l1_pre_topc(A_435))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.11/1.49  tff(c_80, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_36, c_71])).
% 3.11/1.49  tff(c_87, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_80])).
% 3.11/1.49  tff(c_30, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_65, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 3.11/1.49  tff(c_54, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_220, plain, (![C_457, A_454, B_455, D_453, E_456]: (k3_tmap_1(A_454, B_455, C_457, D_453, E_456)=k2_partfun1(u1_struct_0(C_457), u1_struct_0(B_455), E_456, u1_struct_0(D_453)) | ~m1_pre_topc(D_453, C_457) | ~m1_subset_1(E_456, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_457), u1_struct_0(B_455)))) | ~v1_funct_2(E_456, u1_struct_0(C_457), u1_struct_0(B_455)) | ~v1_funct_1(E_456) | ~m1_pre_topc(D_453, A_454) | ~m1_pre_topc(C_457, A_454) | ~l1_pre_topc(B_455) | ~v2_pre_topc(B_455) | v2_struct_0(B_455) | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.11/1.49  tff(c_222, plain, (![A_454, D_453]: (k3_tmap_1(A_454, '#skF_2', '#skF_4', D_453, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_453)) | ~m1_pre_topc(D_453, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_453, A_454) | ~m1_pre_topc('#skF_4', A_454) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(resolution, [status(thm)], [c_30, c_220])).
% 3.11/1.49  tff(c_225, plain, (![A_454, D_453]: (k3_tmap_1(A_454, '#skF_2', '#skF_4', D_453, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_453)) | ~m1_pre_topc(D_453, '#skF_4') | ~m1_pre_topc(D_453, A_454) | ~m1_pre_topc('#skF_4', A_454) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_454) | ~v2_pre_topc(A_454) | v2_struct_0(A_454))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_222])).
% 3.11/1.49  tff(c_227, plain, (![A_458, D_459]: (k3_tmap_1(A_458, '#skF_2', '#skF_4', D_459, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_459)) | ~m1_pre_topc(D_459, '#skF_4') | ~m1_pre_topc(D_459, A_458) | ~m1_pre_topc('#skF_4', A_458) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458) | v2_struct_0(A_458))), inference(negUnitSimplification, [status(thm)], [c_48, c_225])).
% 3.11/1.49  tff(c_235, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_227])).
% 3.11/1.49  tff(c_250, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_28, c_235])).
% 3.11/1.49  tff(c_251, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_250])).
% 3.11/1.49  tff(c_152, plain, (![A_444, B_445, C_446, D_447]: (k2_partfun1(u1_struct_0(A_444), u1_struct_0(B_445), C_446, u1_struct_0(D_447))=k2_tmap_1(A_444, B_445, C_446, D_447) | ~m1_pre_topc(D_447, A_444) | ~m1_subset_1(C_446, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_444), u1_struct_0(B_445)))) | ~v1_funct_2(C_446, u1_struct_0(A_444), u1_struct_0(B_445)) | ~v1_funct_1(C_446) | ~l1_pre_topc(B_445) | ~v2_pre_topc(B_445) | v2_struct_0(B_445) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.11/1.49  tff(c_154, plain, (![D_447]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_447))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_447) | ~m1_pre_topc(D_447, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_152])).
% 3.11/1.49  tff(c_157, plain, (![D_447]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_447))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_447) | ~m1_pre_topc(D_447, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_87, c_46, c_44, c_34, c_32, c_154])).
% 3.11/1.49  tff(c_158, plain, (![D_447]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_447))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_447) | ~m1_pre_topc(D_447, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_48, c_157])).
% 3.11/1.49  tff(c_259, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_251, c_158])).
% 3.11/1.49  tff(c_266, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_259])).
% 3.11/1.49  tff(c_62, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_7') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_215])).
% 3.11/1.49  tff(c_63, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_62])).
% 3.11/1.49  tff(c_151, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_150, c_63])).
% 3.11/1.49  tff(c_271, plain, (r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_266, c_151])).
% 3.11/1.49  tff(c_319, plain, (![A_470, G_473, C_472, B_471, D_474, E_475]: (r1_tmap_1(B_471, A_470, C_472, G_473) | ~r1_tmap_1(D_474, A_470, k2_tmap_1(B_471, A_470, C_472, D_474), G_473) | ~m1_connsp_2(E_475, B_471, G_473) | ~r1_tarski(E_475, u1_struct_0(D_474)) | ~m1_subset_1(G_473, u1_struct_0(D_474)) | ~m1_subset_1(G_473, u1_struct_0(B_471)) | ~m1_subset_1(E_475, k1_zfmisc_1(u1_struct_0(B_471))) | ~m1_pre_topc(D_474, B_471) | v2_struct_0(D_474) | ~m1_subset_1(C_472, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_471), u1_struct_0(A_470)))) | ~v1_funct_2(C_472, u1_struct_0(B_471), u1_struct_0(A_470)) | ~v1_funct_1(C_472) | ~l1_pre_topc(B_471) | ~v2_pre_topc(B_471) | v2_struct_0(B_471) | ~l1_pre_topc(A_470) | ~v2_pre_topc(A_470) | v2_struct_0(A_470))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.11/1.49  tff(c_321, plain, (![E_475]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_475, '#skF_4', '#skF_8') | ~r1_tarski(E_475, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1(E_475, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_271, c_319])).
% 3.11/1.49  tff(c_324, plain, (![E_475]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~m1_connsp_2(E_475, '#skF_4', '#skF_8') | ~r1_tarski(E_475, u1_struct_0('#skF_3')) | ~m1_subset_1(E_475, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_3') | v2_struct_0('#skF_4') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_108, c_87, c_34, c_32, c_30, c_28, c_65, c_22, c_321])).
% 3.11/1.49  tff(c_326, plain, (![E_476]: (~m1_connsp_2(E_476, '#skF_4', '#skF_8') | ~r1_tarski(E_476, u1_struct_0('#skF_3')) | ~m1_subset_1(E_476, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_48, c_38, c_42, c_150, c_324])).
% 3.11/1.49  tff(c_329, plain, (~m1_connsp_2('#skF_6', '#skF_4', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_26, c_326])).
% 3.11/1.49  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_66, c_329])).
% 3.11/1.49  tff(c_335, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 3.11/1.49  tff(c_456, plain, (![D_497, B_494, A_493, E_498, C_495, G_496]: (r1_tmap_1(D_497, A_493, k2_tmap_1(B_494, A_493, C_495, D_497), G_496) | ~r1_tmap_1(B_494, A_493, C_495, G_496) | ~m1_connsp_2(E_498, B_494, G_496) | ~r1_tarski(E_498, u1_struct_0(D_497)) | ~m1_subset_1(G_496, u1_struct_0(D_497)) | ~m1_subset_1(G_496, u1_struct_0(B_494)) | ~m1_subset_1(E_498, k1_zfmisc_1(u1_struct_0(B_494))) | ~m1_pre_topc(D_497, B_494) | v2_struct_0(D_497) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_494), u1_struct_0(A_493)))) | ~v1_funct_2(C_495, u1_struct_0(B_494), u1_struct_0(A_493)) | ~v1_funct_1(C_495) | ~l1_pre_topc(B_494) | ~v2_pre_topc(B_494) | v2_struct_0(B_494) | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493))), inference(cnfTransformation, [status(thm)], [f_147])).
% 3.11/1.49  tff(c_458, plain, (![D_497, A_493, C_495]: (r1_tmap_1(D_497, A_493, k2_tmap_1('#skF_4', A_493, C_495, D_497), '#skF_8') | ~r1_tmap_1('#skF_4', A_493, C_495, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_497)) | ~m1_subset_1('#skF_8', u1_struct_0(D_497)) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc(D_497, '#skF_4') | v2_struct_0(D_497) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_493)))) | ~v1_funct_2(C_495, u1_struct_0('#skF_4'), u1_struct_0(A_493)) | ~v1_funct_1(C_495) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493))), inference(resolution, [status(thm)], [c_66, c_456])).
% 3.11/1.49  tff(c_461, plain, (![D_497, A_493, C_495]: (r1_tmap_1(D_497, A_493, k2_tmap_1('#skF_4', A_493, C_495, D_497), '#skF_8') | ~r1_tmap_1('#skF_4', A_493, C_495, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_497)) | ~m1_subset_1('#skF_8', u1_struct_0(D_497)) | ~m1_pre_topc(D_497, '#skF_4') | v2_struct_0(D_497) | ~m1_subset_1(C_495, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_493)))) | ~v1_funct_2(C_495, u1_struct_0('#skF_4'), u1_struct_0(A_493)) | ~v1_funct_1(C_495) | v2_struct_0('#skF_4') | ~l1_pre_topc(A_493) | ~v2_pre_topc(A_493) | v2_struct_0(A_493))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_87, c_26, c_65, c_458])).
% 3.11/1.49  tff(c_499, plain, (![D_506, A_507, C_508]: (r1_tmap_1(D_506, A_507, k2_tmap_1('#skF_4', A_507, C_508, D_506), '#skF_8') | ~r1_tmap_1('#skF_4', A_507, C_508, '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_506)) | ~m1_subset_1('#skF_8', u1_struct_0(D_506)) | ~m1_pre_topc(D_506, '#skF_4') | v2_struct_0(D_506) | ~m1_subset_1(C_508, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0(A_507)))) | ~v1_funct_2(C_508, u1_struct_0('#skF_4'), u1_struct_0(A_507)) | ~v1_funct_1(C_508) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(negUnitSimplification, [status(thm)], [c_38, c_461])).
% 3.11/1.49  tff(c_501, plain, (![D_506]: (r1_tmap_1(D_506, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_506), '#skF_8') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_506)) | ~m1_subset_1('#skF_8', u1_struct_0(D_506)) | ~m1_pre_topc(D_506, '#skF_4') | v2_struct_0(D_506) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_499])).
% 3.11/1.49  tff(c_504, plain, (![D_506]: (r1_tmap_1(D_506, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_506), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_506)) | ~m1_subset_1('#skF_8', u1_struct_0(D_506)) | ~m1_pre_topc(D_506, '#skF_4') | v2_struct_0(D_506) | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_335, c_501])).
% 3.11/1.49  tff(c_506, plain, (![D_509]: (r1_tmap_1(D_509, '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_509), '#skF_8') | ~r1_tarski('#skF_6', u1_struct_0(D_509)) | ~m1_subset_1('#skF_8', u1_struct_0(D_509)) | ~m1_pre_topc(D_509, '#skF_4') | v2_struct_0(D_509))), inference(negUnitSimplification, [status(thm)], [c_48, c_504])).
% 3.11/1.49  tff(c_406, plain, (![A_487, D_486, B_488, E_489, C_490]: (k3_tmap_1(A_487, B_488, C_490, D_486, E_489)=k2_partfun1(u1_struct_0(C_490), u1_struct_0(B_488), E_489, u1_struct_0(D_486)) | ~m1_pre_topc(D_486, C_490) | ~m1_subset_1(E_489, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_490), u1_struct_0(B_488)))) | ~v1_funct_2(E_489, u1_struct_0(C_490), u1_struct_0(B_488)) | ~v1_funct_1(E_489) | ~m1_pre_topc(D_486, A_487) | ~m1_pre_topc(C_490, A_487) | ~l1_pre_topc(B_488) | ~v2_pre_topc(B_488) | v2_struct_0(B_488) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.11/1.49  tff(c_408, plain, (![A_487, D_486]: (k3_tmap_1(A_487, '#skF_2', '#skF_4', D_486, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_486)) | ~m1_pre_topc(D_486, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_486, A_487) | ~m1_pre_topc('#skF_4', A_487) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(resolution, [status(thm)], [c_30, c_406])).
% 3.11/1.49  tff(c_411, plain, (![A_487, D_486]: (k3_tmap_1(A_487, '#skF_2', '#skF_4', D_486, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_486)) | ~m1_pre_topc(D_486, '#skF_4') | ~m1_pre_topc(D_486, A_487) | ~m1_pre_topc('#skF_4', A_487) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44, c_34, c_32, c_408])).
% 3.11/1.49  tff(c_413, plain, (![A_491, D_492]: (k3_tmap_1(A_491, '#skF_2', '#skF_4', D_492, '#skF_5')=k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_492)) | ~m1_pre_topc(D_492, '#skF_4') | ~m1_pre_topc(D_492, A_491) | ~m1_pre_topc('#skF_4', A_491) | ~l1_pre_topc(A_491) | ~v2_pre_topc(A_491) | v2_struct_0(A_491))), inference(negUnitSimplification, [status(thm)], [c_48, c_411])).
% 3.11/1.49  tff(c_421, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_1') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_413])).
% 3.11/1.49  tff(c_436, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50, c_36, c_28, c_421])).
% 3.11/1.49  tff(c_437, plain, (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0('#skF_3'))=k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_54, c_436])).
% 3.11/1.49  tff(c_390, plain, (![A_481, B_482, C_483, D_484]: (k2_partfun1(u1_struct_0(A_481), u1_struct_0(B_482), C_483, u1_struct_0(D_484))=k2_tmap_1(A_481, B_482, C_483, D_484) | ~m1_pre_topc(D_484, A_481) | ~m1_subset_1(C_483, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_481), u1_struct_0(B_482)))) | ~v1_funct_2(C_483, u1_struct_0(A_481), u1_struct_0(B_482)) | ~v1_funct_1(C_483) | ~l1_pre_topc(B_482) | ~v2_pre_topc(B_482) | v2_struct_0(B_482) | ~l1_pre_topc(A_481) | ~v2_pre_topc(A_481) | v2_struct_0(A_481))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.11/1.49  tff(c_392, plain, (![D_484]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_484))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_484) | ~m1_pre_topc(D_484, '#skF_4') | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_390])).
% 3.11/1.49  tff(c_395, plain, (![D_484]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_484))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_484) | ~m1_pre_topc(D_484, '#skF_4') | v2_struct_0('#skF_2') | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_87, c_46, c_44, c_34, c_32, c_392])).
% 3.11/1.49  tff(c_396, plain, (![D_484]: (k2_partfun1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'), '#skF_5', u1_struct_0(D_484))=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', D_484) | ~m1_pre_topc(D_484, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_38, c_48, c_395])).
% 3.11/1.49  tff(c_445, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_437, c_396])).
% 3.11/1.49  tff(c_452, plain, (k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5')=k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_445])).
% 3.11/1.49  tff(c_334, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_64])).
% 3.11/1.49  tff(c_464, plain, (~r1_tmap_1('#skF_3', '#skF_2', k2_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_3'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_334])).
% 3.11/1.49  tff(c_511, plain, (~r1_tarski('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_506, c_464])).
% 3.11/1.49  tff(c_518, plain, (v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_20, c_511])).
% 3.11/1.49  tff(c_520, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_518])).
% 3.11/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.11/1.49  
% 3.11/1.49  Inference rules
% 3.11/1.49  ----------------------
% 3.11/1.49  #Ref     : 0
% 3.11/1.49  #Sup     : 85
% 3.11/1.49  #Fact    : 0
% 3.11/1.49  #Define  : 0
% 3.11/1.49  #Split   : 3
% 3.11/1.49  #Chain   : 0
% 3.11/1.49  #Close   : 0
% 3.11/1.49  
% 3.11/1.49  Ordering : KBO
% 3.11/1.49  
% 3.11/1.49  Simplification rules
% 3.11/1.49  ----------------------
% 3.11/1.49  #Subsume      : 13
% 3.11/1.49  #Demod        : 207
% 3.11/1.49  #Tautology    : 48
% 3.11/1.49  #SimpNegUnit  : 21
% 3.11/1.49  #BackRed      : 4
% 3.11/1.49  
% 3.11/1.49  #Partial instantiations: 0
% 3.11/1.49  #Strategies tried      : 1
% 3.11/1.49  
% 3.11/1.49  Timing (in seconds)
% 3.11/1.49  ----------------------
% 3.11/1.49  Preprocessing        : 0.38
% 3.11/1.49  Parsing              : 0.18
% 3.11/1.49  CNF conversion       : 0.06
% 3.11/1.49  Main loop            : 0.31
% 3.11/1.49  Inferencing          : 0.11
% 3.11/1.49  Reduction            : 0.11
% 3.11/1.49  Demodulation         : 0.08
% 3.11/1.49  BG Simplification    : 0.02
% 3.11/1.49  Subsumption          : 0.06
% 3.11/1.49  Abstraction          : 0.01
% 3.11/1.49  MUC search           : 0.00
% 3.11/1.49  Cooper               : 0.00
% 3.11/1.49  Total                : 0.74
% 3.11/1.49  Index Insertion      : 0.00
% 3.11/1.49  Index Deletion       : 0.00
% 3.11/1.49  Index Matching       : 0.00
% 3.11/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
