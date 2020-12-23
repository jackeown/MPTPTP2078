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
% DateTime   : Thu Dec  3 10:27:31 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 174 expanded)
%              Number of leaves         :   31 (  84 expanded)
%              Depth                    :   10
%              Number of atoms          :  280 (1438 expanded)
%              Number of equality atoms :    4 (  63 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_230,negated_conjecture,(
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

tff(f_36,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_60,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( v1_tsep_1(B,A)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
               => ( v1_tsep_1(B,C)
                  & m1_pre_topc(B,C) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_177,axiom,(
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

tff(f_127,axiom,(
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
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(C))
                         => ! [G] :
                              ( m1_subset_1(G,u1_struct_0(D))
                             => ( ( F = G
                                  & m1_pre_topc(D,C)
                                  & r1_tmap_1(C,B,E,F) )
                               => r1_tmap_1(D,B,k3_tmap_1(A,B,C,D,E),G) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_tmap_1)).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_46,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_50,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_48,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_40,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_44,plain,(
    m1_pre_topc('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_26,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_22,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_24,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_28,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_42,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_60,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_69,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_60])).

tff(c_131,plain,(
    ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_56,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_54,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_38,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_36,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_34,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1')))) ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_32,plain,(
    v1_tsep_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_85,plain,(
    ! [B_401,A_402] :
      ( l1_pre_topc(B_401)
      | ~ m1_pre_topc(B_401,A_402)
      | ~ l1_pre_topc(A_402) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_100,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_91])).

tff(c_104,plain,(
    ! [B_403,A_404] :
      ( m1_subset_1(u1_struct_0(B_403),k1_zfmisc_1(u1_struct_0(A_404)))
      | ~ m1_pre_topc(B_403,A_404)
      | ~ l1_pre_topc(A_404) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_108,plain,(
    ! [B_403,A_404] :
      ( r1_tarski(u1_struct_0(B_403),u1_struct_0(A_404))
      | ~ m1_pre_topc(B_403,A_404)
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_104,c_2])).

tff(c_158,plain,(
    ! [B_418,C_419,A_420] :
      ( v1_tsep_1(B_418,C_419)
      | ~ r1_tarski(u1_struct_0(B_418),u1_struct_0(C_419))
      | ~ m1_pre_topc(C_419,A_420)
      | v2_struct_0(C_419)
      | ~ m1_pre_topc(B_418,A_420)
      | ~ v1_tsep_1(B_418,A_420)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | v2_struct_0(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_162,plain,(
    ! [B_421,A_422,A_423] :
      ( v1_tsep_1(B_421,A_422)
      | ~ m1_pre_topc(A_422,A_423)
      | v2_struct_0(A_422)
      | ~ m1_pre_topc(B_421,A_423)
      | ~ v1_tsep_1(B_421,A_423)
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423)
      | v2_struct_0(A_423)
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(resolution,[status(thm)],[c_108,c_158])).

tff(c_168,plain,(
    ! [B_421] :
      ( v1_tsep_1(B_421,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_421,'#skF_2')
      | ~ v1_tsep_1(B_421,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_421,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_40,c_162])).

tff(c_181,plain,(
    ! [B_421] :
      ( v1_tsep_1(B_421,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_421,'#skF_2')
      | ~ v1_tsep_1(B_421,'#skF_2')
      | v2_struct_0('#skF_2')
      | ~ m1_pre_topc(B_421,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_50,c_48,c_168])).

tff(c_194,plain,(
    ! [B_425] :
      ( v1_tsep_1(B_425,'#skF_4')
      | ~ m1_pre_topc(B_425,'#skF_2')
      | ~ v1_tsep_1(B_425,'#skF_2')
      | ~ m1_pre_topc(B_425,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_42,c_181])).

tff(c_197,plain,
    ( v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_194])).

tff(c_200,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_44,c_197])).

tff(c_66,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_230])).

tff(c_68,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_66])).

tff(c_132,plain,(
    r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_68])).

tff(c_242,plain,(
    ! [D_443,A_447,E_444,C_445,B_448,G_446] :
      ( r1_tmap_1(D_443,B_448,E_444,G_446)
      | ~ r1_tmap_1(C_445,B_448,k3_tmap_1(A_447,B_448,D_443,C_445,E_444),G_446)
      | ~ m1_subset_1(G_446,u1_struct_0(C_445))
      | ~ m1_subset_1(G_446,u1_struct_0(D_443))
      | ~ m1_pre_topc(C_445,D_443)
      | ~ v1_tsep_1(C_445,D_443)
      | ~ m1_subset_1(E_444,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_443),u1_struct_0(B_448))))
      | ~ v1_funct_2(E_444,u1_struct_0(D_443),u1_struct_0(B_448))
      | ~ v1_funct_1(E_444)
      | ~ m1_pre_topc(D_443,A_447)
      | v2_struct_0(D_443)
      | ~ m1_pre_topc(C_445,A_447)
      | v2_struct_0(C_445)
      | ~ l1_pre_topc(B_448)
      | ~ v2_pre_topc(B_448)
      | v2_struct_0(B_448)
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447)
      | v2_struct_0(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_177])).

tff(c_246,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))))
    | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_132,c_242])).

tff(c_253,plain,
    ( r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_56,c_54,c_44,c_40,c_38,c_36,c_34,c_200,c_28,c_26,c_70,c_246])).

tff(c_255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_58,c_46,c_42,c_131,c_253])).

tff(c_257,plain,(
    r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_336,plain,(
    ! [G_464,D_466,E_465,A_467,B_463,C_462] :
      ( r1_tmap_1(D_466,B_463,k3_tmap_1(A_467,B_463,C_462,D_466,E_465),G_464)
      | ~ r1_tmap_1(C_462,B_463,E_465,G_464)
      | ~ m1_pre_topc(D_466,C_462)
      | ~ m1_subset_1(G_464,u1_struct_0(D_466))
      | ~ m1_subset_1(G_464,u1_struct_0(C_462))
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_462),u1_struct_0(B_463))))
      | ~ v1_funct_2(E_465,u1_struct_0(C_462),u1_struct_0(B_463))
      | ~ v1_funct_1(E_465)
      | ~ m1_pre_topc(D_466,A_467)
      | v2_struct_0(D_466)
      | ~ m1_pre_topc(C_462,A_467)
      | v2_struct_0(C_462)
      | ~ l1_pre_topc(B_463)
      | ~ v2_pre_topc(B_463)
      | v2_struct_0(B_463)
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_338,plain,(
    ! [D_466,A_467,G_464] :
      ( r1_tmap_1(D_466,'#skF_1',k3_tmap_1(A_467,'#skF_1','#skF_4',D_466,'#skF_5'),G_464)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_464)
      | ~ m1_pre_topc(D_466,'#skF_4')
      | ~ m1_subset_1(G_464,u1_struct_0(D_466))
      | ~ m1_subset_1(G_464,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_1'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc(D_466,A_467)
      | v2_struct_0(D_466)
      | ~ m1_pre_topc('#skF_4',A_467)
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(resolution,[status(thm)],[c_34,c_336])).

tff(c_344,plain,(
    ! [D_466,A_467,G_464] :
      ( r1_tmap_1(D_466,'#skF_1',k3_tmap_1(A_467,'#skF_1','#skF_4',D_466,'#skF_5'),G_464)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_464)
      | ~ m1_pre_topc(D_466,'#skF_4')
      | ~ m1_subset_1(G_464,u1_struct_0(D_466))
      | ~ m1_subset_1(G_464,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_466,A_467)
      | v2_struct_0(D_466)
      | ~ m1_pre_topc('#skF_4',A_467)
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_1')
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467)
      | v2_struct_0(A_467) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_38,c_36,c_338])).

tff(c_361,plain,(
    ! [D_470,A_471,G_472] :
      ( r1_tmap_1(D_470,'#skF_1',k3_tmap_1(A_471,'#skF_1','#skF_4',D_470,'#skF_5'),G_472)
      | ~ r1_tmap_1('#skF_4','#skF_1','#skF_5',G_472)
      | ~ m1_pre_topc(D_470,'#skF_4')
      | ~ m1_subset_1(G_472,u1_struct_0(D_470))
      | ~ m1_subset_1(G_472,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(D_470,A_471)
      | v2_struct_0(D_470)
      | ~ m1_pre_topc('#skF_4',A_471)
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_42,c_344])).

tff(c_256,plain,(
    ~ r1_tmap_1('#skF_3','#skF_1',k3_tmap_1('#skF_2','#skF_1','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_364,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_1','#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_2')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_2')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_361,c_256])).

tff(c_367,plain,
    ( v2_struct_0('#skF_3')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_48,c_40,c_44,c_26,c_70,c_28,c_257,c_364])).

tff(c_369,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_46,c_367])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n019.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 15:50:07 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.38  
% 3.10/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.38  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.10/1.38  
% 3.10/1.38  %Foreground sorts:
% 3.10/1.38  
% 3.10/1.38  
% 3.10/1.38  %Background operators:
% 3.10/1.38  
% 3.10/1.38  
% 3.10/1.38  %Foreground operators:
% 3.10/1.38  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.10/1.38  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.10/1.38  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.10/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.38  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.10/1.38  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.10/1.38  tff('#skF_7', type, '#skF_7': $i).
% 3.10/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.38  tff('#skF_5', type, '#skF_5': $i).
% 3.10/1.38  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.10/1.38  tff('#skF_6', type, '#skF_6': $i).
% 3.10/1.38  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.38  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.38  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.10/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.10/1.38  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.10/1.38  tff('#skF_4', type, '#skF_4': $i).
% 3.10/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.38  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.10/1.38  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.10/1.38  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.10/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.10/1.38  
% 3.10/1.40  tff(f_230, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.10/1.40  tff(f_36, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.10/1.40  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.10/1.40  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.10/1.40  tff(f_60, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 3.10/1.40  tff(f_177, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.10/1.40  tff(f_127, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.10/1.40  tff(c_52, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_46, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_50, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_48, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_40, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_44, plain, (m1_pre_topc('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_26, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_22, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_24, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_70, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 3.10/1.40  tff(c_28, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_58, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_42, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_60, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_69, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_60])).
% 3.10/1.40  tff(c_131, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_69])).
% 3.10/1.40  tff(c_56, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_54, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_38, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_36, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_34, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1'))))), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_32, plain, (v1_tsep_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_85, plain, (![B_401, A_402]: (l1_pre_topc(B_401) | ~m1_pre_topc(B_401, A_402) | ~l1_pre_topc(A_402))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.10/1.40  tff(c_91, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_40, c_85])).
% 3.10/1.40  tff(c_100, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_91])).
% 3.10/1.40  tff(c_104, plain, (![B_403, A_404]: (m1_subset_1(u1_struct_0(B_403), k1_zfmisc_1(u1_struct_0(A_404))) | ~m1_pre_topc(B_403, A_404) | ~l1_pre_topc(A_404))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.10/1.40  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.40  tff(c_108, plain, (![B_403, A_404]: (r1_tarski(u1_struct_0(B_403), u1_struct_0(A_404)) | ~m1_pre_topc(B_403, A_404) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_104, c_2])).
% 3.10/1.40  tff(c_158, plain, (![B_418, C_419, A_420]: (v1_tsep_1(B_418, C_419) | ~r1_tarski(u1_struct_0(B_418), u1_struct_0(C_419)) | ~m1_pre_topc(C_419, A_420) | v2_struct_0(C_419) | ~m1_pre_topc(B_418, A_420) | ~v1_tsep_1(B_418, A_420) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420) | v2_struct_0(A_420))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.10/1.40  tff(c_162, plain, (![B_421, A_422, A_423]: (v1_tsep_1(B_421, A_422) | ~m1_pre_topc(A_422, A_423) | v2_struct_0(A_422) | ~m1_pre_topc(B_421, A_423) | ~v1_tsep_1(B_421, A_423) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423) | v2_struct_0(A_423) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422))), inference(resolution, [status(thm)], [c_108, c_158])).
% 3.10/1.40  tff(c_168, plain, (![B_421]: (v1_tsep_1(B_421, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_421, '#skF_2') | ~v1_tsep_1(B_421, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_421, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_40, c_162])).
% 3.10/1.40  tff(c_181, plain, (![B_421]: (v1_tsep_1(B_421, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_421, '#skF_2') | ~v1_tsep_1(B_421, '#skF_2') | v2_struct_0('#skF_2') | ~m1_pre_topc(B_421, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_50, c_48, c_168])).
% 3.10/1.40  tff(c_194, plain, (![B_425]: (v1_tsep_1(B_425, '#skF_4') | ~m1_pre_topc(B_425, '#skF_2') | ~v1_tsep_1(B_425, '#skF_2') | ~m1_pre_topc(B_425, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_52, c_42, c_181])).
% 3.10/1.40  tff(c_197, plain, (v1_tsep_1('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_32, c_194])).
% 3.10/1.40  tff(c_200, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_44, c_197])).
% 3.10/1.40  tff(c_66, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_230])).
% 3.10/1.40  tff(c_68, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_66])).
% 3.10/1.40  tff(c_132, plain, (r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_131, c_68])).
% 3.10/1.40  tff(c_242, plain, (![D_443, A_447, E_444, C_445, B_448, G_446]: (r1_tmap_1(D_443, B_448, E_444, G_446) | ~r1_tmap_1(C_445, B_448, k3_tmap_1(A_447, B_448, D_443, C_445, E_444), G_446) | ~m1_subset_1(G_446, u1_struct_0(C_445)) | ~m1_subset_1(G_446, u1_struct_0(D_443)) | ~m1_pre_topc(C_445, D_443) | ~v1_tsep_1(C_445, D_443) | ~m1_subset_1(E_444, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_443), u1_struct_0(B_448)))) | ~v1_funct_2(E_444, u1_struct_0(D_443), u1_struct_0(B_448)) | ~v1_funct_1(E_444) | ~m1_pre_topc(D_443, A_447) | v2_struct_0(D_443) | ~m1_pre_topc(C_445, A_447) | v2_struct_0(C_445) | ~l1_pre_topc(B_448) | ~v2_pre_topc(B_448) | v2_struct_0(B_448) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447) | v2_struct_0(A_447))), inference(cnfTransformation, [status(thm)], [f_177])).
% 3.10/1.40  tff(c_246, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4') | ~v1_tsep_1('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_1')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_132, c_242])).
% 3.10/1.40  tff(c_253, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_56, c_54, c_44, c_40, c_38, c_36, c_34, c_200, c_28, c_26, c_70, c_246])).
% 3.10/1.40  tff(c_255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_58, c_46, c_42, c_131, c_253])).
% 3.10/1.40  tff(c_257, plain, (r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.10/1.40  tff(c_336, plain, (![G_464, D_466, E_465, A_467, B_463, C_462]: (r1_tmap_1(D_466, B_463, k3_tmap_1(A_467, B_463, C_462, D_466, E_465), G_464) | ~r1_tmap_1(C_462, B_463, E_465, G_464) | ~m1_pre_topc(D_466, C_462) | ~m1_subset_1(G_464, u1_struct_0(D_466)) | ~m1_subset_1(G_464, u1_struct_0(C_462)) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_462), u1_struct_0(B_463)))) | ~v1_funct_2(E_465, u1_struct_0(C_462), u1_struct_0(B_463)) | ~v1_funct_1(E_465) | ~m1_pre_topc(D_466, A_467) | v2_struct_0(D_466) | ~m1_pre_topc(C_462, A_467) | v2_struct_0(C_462) | ~l1_pre_topc(B_463) | ~v2_pre_topc(B_463) | v2_struct_0(B_463) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(cnfTransformation, [status(thm)], [f_127])).
% 3.10/1.40  tff(c_338, plain, (![D_466, A_467, G_464]: (r1_tmap_1(D_466, '#skF_1', k3_tmap_1(A_467, '#skF_1', '#skF_4', D_466, '#skF_5'), G_464) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_464) | ~m1_pre_topc(D_466, '#skF_4') | ~m1_subset_1(G_464, u1_struct_0(D_466)) | ~m1_subset_1(G_464, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_1')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc(D_466, A_467) | v2_struct_0(D_466) | ~m1_pre_topc('#skF_4', A_467) | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(resolution, [status(thm)], [c_34, c_336])).
% 3.10/1.40  tff(c_344, plain, (![D_466, A_467, G_464]: (r1_tmap_1(D_466, '#skF_1', k3_tmap_1(A_467, '#skF_1', '#skF_4', D_466, '#skF_5'), G_464) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_464) | ~m1_pre_topc(D_466, '#skF_4') | ~m1_subset_1(G_464, u1_struct_0(D_466)) | ~m1_subset_1(G_464, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_466, A_467) | v2_struct_0(D_466) | ~m1_pre_topc('#skF_4', A_467) | v2_struct_0('#skF_4') | v2_struct_0('#skF_1') | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467) | v2_struct_0(A_467))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_38, c_36, c_338])).
% 3.10/1.40  tff(c_361, plain, (![D_470, A_471, G_472]: (r1_tmap_1(D_470, '#skF_1', k3_tmap_1(A_471, '#skF_1', '#skF_4', D_470, '#skF_5'), G_472) | ~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', G_472) | ~m1_pre_topc(D_470, '#skF_4') | ~m1_subset_1(G_472, u1_struct_0(D_470)) | ~m1_subset_1(G_472, u1_struct_0('#skF_4')) | ~m1_pre_topc(D_470, A_471) | v2_struct_0(D_470) | ~m1_pre_topc('#skF_4', A_471) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471))), inference(negUnitSimplification, [status(thm)], [c_58, c_42, c_344])).
% 3.10/1.40  tff(c_256, plain, (~r1_tmap_1('#skF_3', '#skF_1', k3_tmap_1('#skF_2', '#skF_1', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_69])).
% 3.10/1.40  tff(c_364, plain, (~r1_tmap_1('#skF_4', '#skF_1', '#skF_5', '#skF_6') | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_2') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_361, c_256])).
% 3.10/1.40  tff(c_367, plain, (v2_struct_0('#skF_3') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_50, c_48, c_40, c_44, c_26, c_70, c_28, c_257, c_364])).
% 3.10/1.40  tff(c_369, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_46, c_367])).
% 3.10/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.10/1.40  
% 3.10/1.40  Inference rules
% 3.10/1.40  ----------------------
% 3.10/1.40  #Ref     : 0
% 3.10/1.40  #Sup     : 51
% 3.10/1.40  #Fact    : 0
% 3.10/1.40  #Define  : 0
% 3.10/1.40  #Split   : 7
% 3.10/1.40  #Chain   : 0
% 3.10/1.40  #Close   : 0
% 3.10/1.40  
% 3.10/1.40  Ordering : KBO
% 3.10/1.40  
% 3.10/1.40  Simplification rules
% 3.10/1.40  ----------------------
% 3.10/1.40  #Subsume      : 8
% 3.10/1.40  #Demod        : 110
% 3.10/1.40  #Tautology    : 18
% 3.10/1.40  #SimpNegUnit  : 20
% 3.10/1.40  #BackRed      : 0
% 3.10/1.40  
% 3.10/1.40  #Partial instantiations: 0
% 3.10/1.40  #Strategies tried      : 1
% 3.10/1.40  
% 3.10/1.40  Timing (in seconds)
% 3.10/1.40  ----------------------
% 3.10/1.41  Preprocessing        : 0.38
% 3.10/1.41  Parsing              : 0.20
% 3.10/1.41  CNF conversion       : 0.06
% 3.10/1.41  Main loop            : 0.27
% 3.10/1.41  Inferencing          : 0.10
% 3.10/1.41  Reduction            : 0.09
% 3.10/1.41  Demodulation         : 0.07
% 3.10/1.41  BG Simplification    : 0.02
% 3.10/1.41  Subsumption          : 0.05
% 3.10/1.41  Abstraction          : 0.01
% 3.10/1.41  MUC search           : 0.00
% 3.10/1.41  Cooper               : 0.00
% 3.10/1.41  Total                : 0.70
% 3.10/1.41  Index Insertion      : 0.00
% 3.10/1.41  Index Deletion       : 0.00
% 3.10/1.41  Index Matching       : 0.00
% 3.10/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
