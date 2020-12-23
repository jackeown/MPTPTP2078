%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:33 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.98s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 654 expanded)
%              Number of leaves         :   41 ( 271 expanded)
%              Depth                    :   15
%              Number of atoms          :  326 (4866 expanded)
%              Number of equality atoms :   28 ( 457 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(u1_pre_topc,type,(
    u1_pre_topc: $i > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

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

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_239,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_tmap_1)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_67,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ( ~ v2_struct_0(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_pre_topc)).

tff(f_41,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_116,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ! [C] :
              ( l1_pre_topc(C)
             => ! [D] :
                  ( l1_pre_topc(D)
                 => ( ( g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))
                      & g1_pre_topc(u1_struct_0(C),u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D),u1_pre_topc(D))
                      & m1_pre_topc(C,A) )
                   => m1_pre_topc(D,B) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_pre_topc)).

tff(f_190,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

tff(f_123,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_112,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_100,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_125,plain,(
    ! [B_431,A_432] :
      ( v2_pre_topc(B_431)
      | ~ m1_pre_topc(B_431,A_432)
      | ~ l1_pre_topc(A_432)
      | ~ v2_pre_topc(A_432) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_134,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_141,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_134])).

tff(c_88,plain,(
    ! [B_423,A_424] :
      ( l1_pre_topc(B_423)
      | ~ m1_pre_topc(B_423,A_424)
      | ~ l1_pre_topc(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_101,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_94])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_153,plain,(
    ! [A_436] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_436),u1_pre_topc(A_436)))
      | ~ l1_pre_topc(A_436)
      | v2_struct_0(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,
    ( v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_153])).

tff(c_158,plain,
    ( v1_pre_topc('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_156])).

tff(c_159,plain,(
    v1_pre_topc('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_158])).

tff(c_12,plain,(
    ! [A_5] :
      ( g1_pre_topc(u1_struct_0(A_5),u1_pre_topc(A_5)) = A_5
      | ~ v1_pre_topc(A_5)
      | ~ l1_pre_topc(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_35] :
      ( m1_pre_topc(A_35,A_35)
      | ~ l1_pre_topc(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_294,plain,(
    ! [D_457,B_458,C_459,A_460] :
      ( m1_pre_topc(D_457,B_458)
      | ~ m1_pre_topc(C_459,A_460)
      | g1_pre_topc(u1_struct_0(D_457),u1_pre_topc(D_457)) != g1_pre_topc(u1_struct_0(C_459),u1_pre_topc(C_459))
      | g1_pre_topc(u1_struct_0(B_458),u1_pre_topc(B_458)) != g1_pre_topc(u1_struct_0(A_460),u1_pre_topc(A_460))
      | ~ l1_pre_topc(D_457)
      | ~ l1_pre_topc(C_459)
      | ~ l1_pre_topc(B_458)
      | ~ l1_pre_topc(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_306,plain,(
    ! [D_457,B_458,A_35] :
      ( m1_pre_topc(D_457,B_458)
      | g1_pre_topc(u1_struct_0(D_457),u1_pre_topc(D_457)) != g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35))
      | g1_pre_topc(u1_struct_0(B_458),u1_pre_topc(B_458)) != g1_pre_topc(u1_struct_0(A_35),u1_pre_topc(A_35))
      | ~ l1_pre_topc(D_457)
      | ~ l1_pre_topc(B_458)
      | ~ l1_pre_topc(A_35) ) ),
    inference(resolution,[status(thm)],[c_28,c_294])).

tff(c_1095,plain,(
    ! [A_546,B_547] :
      ( m1_pre_topc(A_546,B_547)
      | g1_pre_topc(u1_struct_0(B_547),u1_pre_topc(B_547)) != g1_pre_topc(u1_struct_0(A_546),u1_pre_topc(A_546))
      | ~ l1_pre_topc(A_546)
      | ~ l1_pre_topc(B_547)
      | ~ l1_pre_topc(A_546) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_306])).

tff(c_1101,plain,(
    ! [A_546] :
      ( m1_pre_topc(A_546,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_546),u1_pre_topc(A_546)) != '#skF_5'
      | ~ l1_pre_topc(A_546)
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_546) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1095])).

tff(c_1108,plain,(
    ! [A_548] :
      ( m1_pre_topc(A_548,'#skF_4')
      | g1_pre_topc(u1_struct_0(A_548),u1_pre_topc(A_548)) != '#skF_5'
      | ~ l1_pre_topc(A_548) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_1101])).

tff(c_1139,plain,(
    ! [A_551] :
      ( m1_pre_topc(A_551,'#skF_4')
      | A_551 != '#skF_5'
      | ~ l1_pre_topc(A_551)
      | ~ v1_pre_topc(A_551)
      | ~ l1_pre_topc(A_551) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1108])).

tff(c_554,plain,(
    ! [A_505,B_506] :
      ( m1_pre_topc(A_505,B_506)
      | g1_pre_topc(u1_struct_0(B_506),u1_pre_topc(B_506)) != g1_pre_topc(u1_struct_0(A_505),u1_pre_topc(A_505))
      | ~ l1_pre_topc(A_505)
      | ~ l1_pre_topc(B_506)
      | ~ l1_pre_topc(A_505) ) ),
    inference(reflexivity,[status(thm),theory(equality)],[c_306])).

tff(c_562,plain,(
    ! [B_506] :
      ( m1_pre_topc('#skF_4',B_506)
      | g1_pre_topc(u1_struct_0(B_506),u1_pre_topc(B_506)) != '#skF_5'
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(B_506)
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_554])).

tff(c_612,plain,(
    ! [B_514] :
      ( m1_pre_topc('#skF_4',B_514)
      | g1_pre_topc(u1_struct_0(B_514),u1_pre_topc(B_514)) != '#skF_5'
      | ~ l1_pre_topc(B_514) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_101,c_562])).

tff(c_689,plain,(
    ! [A_518] :
      ( m1_pre_topc('#skF_4',A_518)
      | A_518 != '#skF_5'
      | ~ l1_pre_topc(A_518)
      | ~ v1_pre_topc(A_518)
      | ~ l1_pre_topc(A_518) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_612])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_75,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_46])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_239])).

tff(c_493,plain,(
    ! [D_490,B_492,C_494,F_493,H_491,E_489,A_495] :
      ( r1_tmap_1(D_490,B_492,E_489,H_491)
      | ~ r1_tmap_1(C_494,B_492,k3_tmap_1(A_495,B_492,D_490,C_494,E_489),H_491)
      | ~ m1_connsp_2(F_493,D_490,H_491)
      | ~ r1_tarski(F_493,u1_struct_0(C_494))
      | ~ m1_subset_1(H_491,u1_struct_0(C_494))
      | ~ m1_subset_1(H_491,u1_struct_0(D_490))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0(D_490)))
      | ~ m1_pre_topc(C_494,D_490)
      | ~ m1_subset_1(E_489,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_490),u1_struct_0(B_492))))
      | ~ v1_funct_2(E_489,u1_struct_0(D_490),u1_struct_0(B_492))
      | ~ v1_funct_1(E_489)
      | ~ m1_pre_topc(D_490,A_495)
      | v2_struct_0(D_490)
      | ~ m1_pre_topc(C_494,A_495)
      | v2_struct_0(C_494)
      | ~ l1_pre_topc(B_492)
      | ~ v2_pre_topc(B_492)
      | v2_struct_0(B_492)
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495) ) ),
    inference(cnfTransformation,[status(thm)],[f_190])).

tff(c_495,plain,(
    ! [F_493] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_493,'#skF_5','#skF_8')
      | ~ r1_tarski(F_493,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))))
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_2')
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_2')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_40,c_493])).

tff(c_498,plain,(
    ! [F_493] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_493,'#skF_5','#skF_8')
      | ~ r1_tarski(F_493,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_52,c_50,c_75,c_44,c_495])).

tff(c_499,plain,(
    ! [F_493] :
      ( ~ m1_connsp_2(F_493,'#skF_5','#skF_8')
      | ~ r1_tarski(F_493,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0('#skF_5')))
      | ~ m1_pre_topc('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_76,c_498])).

tff(c_500,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_499])).

tff(c_692,plain,
    ( ~ v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_689,c_500])).

tff(c_713,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_159,c_692])).

tff(c_715,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_499])).

tff(c_30,plain,(
    ! [B_38,A_36] :
      ( r1_tarski(u1_struct_0(B_38),u1_struct_0(A_36))
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_142,plain,(
    ! [B_433,A_434] :
      ( r1_tarski(u1_struct_0(B_433),u1_struct_0(A_434))
      | ~ m1_pre_topc(B_433,A_434)
      | ~ l1_pre_topc(A_434) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_219,plain,(
    ! [B_443,A_444] :
      ( u1_struct_0(B_443) = u1_struct_0(A_444)
      | ~ r1_tarski(u1_struct_0(A_444),u1_struct_0(B_443))
      | ~ m1_pre_topc(B_443,A_444)
      | ~ l1_pre_topc(A_444) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_227,plain,(
    ! [B_38,A_36] :
      ( u1_struct_0(B_38) = u1_struct_0(A_36)
      | ~ m1_pre_topc(A_36,B_38)
      | ~ l1_pre_topc(B_38)
      | ~ m1_pre_topc(B_38,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(resolution,[status(thm)],[c_30,c_219])).

tff(c_723,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_715,c_227])).

tff(c_743,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_104,c_723])).

tff(c_751,plain,(
    ~ m1_pre_topc('#skF_5','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_1151,plain,
    ( ~ v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_1139,c_751])).

tff(c_1190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_159,c_1151])).

tff(c_1191,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_26,plain,(
    ! [A_32,B_33] :
      ( m1_connsp_2('#skF_1'(A_32,B_33),A_32,B_33)
      | ~ m1_subset_1(B_33,u1_struct_0(A_32))
      | ~ l1_pre_topc(A_32)
      | ~ v2_pre_topc(A_32)
      | v2_struct_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_285,plain,(
    ! [C_452,A_453,B_454] :
      ( m1_subset_1(C_452,k1_zfmisc_1(u1_struct_0(A_453)))
      | ~ m1_connsp_2(C_452,A_453,B_454)
      | ~ m1_subset_1(B_454,u1_struct_0(A_453))
      | ~ l1_pre_topc(A_453)
      | ~ v2_pre_topc(A_453)
      | v2_struct_0(A_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_289,plain,(
    ! [A_455,B_456] :
      ( m1_subset_1('#skF_1'(A_455,B_456),k1_zfmisc_1(u1_struct_0(A_455)))
      | ~ m1_subset_1(B_456,u1_struct_0(A_455))
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455)
      | v2_struct_0(A_455) ) ),
    inference(resolution,[status(thm)],[c_26,c_285])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_293,plain,(
    ! [A_455,B_456] :
      ( r1_tarski('#skF_1'(A_455,B_456),u1_struct_0(A_455))
      | ~ m1_subset_1(B_456,u1_struct_0(A_455))
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455)
      | v2_struct_0(A_455) ) ),
    inference(resolution,[status(thm)],[c_289,c_8])).

tff(c_1247,plain,(
    ! [B_456] :
      ( r1_tarski('#skF_1'('#skF_5',B_456),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_456,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1191,c_293])).

tff(c_1286,plain,(
    ! [B_456] :
      ( r1_tarski('#skF_1'('#skF_5',B_456),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_456,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_104,c_1191,c_1247])).

tff(c_1406,plain,(
    ! [B_560] :
      ( r1_tarski('#skF_1'('#skF_5',B_560),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_560,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1286])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_714,plain,(
    ! [F_493] :
      ( ~ m1_connsp_2(F_493,'#skF_5','#skF_8')
      | ~ r1_tarski(F_493,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_493,k1_zfmisc_1(u1_struct_0('#skF_5'))) ) ),
    inference(splitRight,[status(thm)],[c_499])).

tff(c_1307,plain,(
    ! [F_552] :
      ( ~ m1_connsp_2(F_552,'#skF_5','#skF_8')
      | ~ r1_tarski(F_552,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_552,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1191,c_714])).

tff(c_1320,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1307])).

tff(c_1531,plain,(
    ! [B_564] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_564),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_564,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1406,c_1320])).

tff(c_1535,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_1531])).

tff(c_1538,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_104,c_44,c_1191,c_44,c_1535])).

tff(c_1540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:04:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.84  
% 4.81/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.81/1.84  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.81/1.84  
% 4.81/1.84  %Foreground sorts:
% 4.81/1.84  
% 4.81/1.84  
% 4.81/1.84  %Background operators:
% 4.81/1.84  
% 4.81/1.84  
% 4.81/1.84  %Foreground operators:
% 4.81/1.84  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.81/1.84  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.81/1.84  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.81/1.84  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.81/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.81/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.84  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.81/1.84  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.81/1.84  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.81/1.84  tff('#skF_7', type, '#skF_7': $i).
% 4.81/1.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.84  tff('#skF_5', type, '#skF_5': $i).
% 4.81/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.81/1.84  tff('#skF_6', type, '#skF_6': $i).
% 4.81/1.84  tff('#skF_2', type, '#skF_2': $i).
% 4.81/1.84  tff('#skF_3', type, '#skF_3': $i).
% 4.81/1.84  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.81/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.81/1.84  tff('#skF_8', type, '#skF_8': $i).
% 4.81/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.81/1.84  tff('#skF_4', type, '#skF_4': $i).
% 4.81/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.84  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.81/1.84  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.81/1.84  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.81/1.84  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.81/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.81/1.84  
% 4.98/1.86  tff(f_239, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.98/1.86  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.98/1.86  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.98/1.86  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (~v2_struct_0(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_pre_topc)).
% 4.98/1.86  tff(f_41, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.98/1.86  tff(f_116, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.98/1.86  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (![C]: (l1_pre_topc(C) => (![D]: (l1_pre_topc(D) => ((((g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & (g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = g1_pre_topc(u1_struct_0(D), u1_pre_topc(D)))) & m1_pre_topc(C, A)) => m1_pre_topc(D, B)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_pre_topc)).
% 4.98/1.86  tff(f_190, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.98/1.86  tff(f_123, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.98/1.86  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.98/1.86  tff(f_112, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.98/1.86  tff(f_100, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.98/1.86  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.98/1.86  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_125, plain, (![B_431, A_432]: (v2_pre_topc(B_431) | ~m1_pre_topc(B_431, A_432) | ~l1_pre_topc(A_432) | ~v2_pre_topc(A_432))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.98/1.86  tff(c_134, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_125])).
% 4.98/1.86  tff(c_141, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_134])).
% 4.98/1.86  tff(c_88, plain, (![B_423, A_424]: (l1_pre_topc(B_423) | ~m1_pre_topc(B_423, A_424) | ~l1_pre_topc(A_424))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.98/1.86  tff(c_97, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_88])).
% 4.98/1.86  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 4.98/1.86  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_94, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_88])).
% 4.98/1.86  tff(c_101, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_94])).
% 4.98/1.86  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_153, plain, (![A_436]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_436), u1_pre_topc(A_436))) | ~l1_pre_topc(A_436) | v2_struct_0(A_436))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.98/1.86  tff(c_156, plain, (v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_153])).
% 4.98/1.86  tff(c_158, plain, (v1_pre_topc('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_156])).
% 4.98/1.86  tff(c_159, plain, (v1_pre_topc('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_158])).
% 4.98/1.86  tff(c_12, plain, (![A_5]: (g1_pre_topc(u1_struct_0(A_5), u1_pre_topc(A_5))=A_5 | ~v1_pre_topc(A_5) | ~l1_pre_topc(A_5))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.98/1.86  tff(c_28, plain, (![A_35]: (m1_pre_topc(A_35, A_35) | ~l1_pre_topc(A_35))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.98/1.86  tff(c_294, plain, (![D_457, B_458, C_459, A_460]: (m1_pre_topc(D_457, B_458) | ~m1_pre_topc(C_459, A_460) | g1_pre_topc(u1_struct_0(D_457), u1_pre_topc(D_457))!=g1_pre_topc(u1_struct_0(C_459), u1_pre_topc(C_459)) | g1_pre_topc(u1_struct_0(B_458), u1_pre_topc(B_458))!=g1_pre_topc(u1_struct_0(A_460), u1_pre_topc(A_460)) | ~l1_pre_topc(D_457) | ~l1_pre_topc(C_459) | ~l1_pre_topc(B_458) | ~l1_pre_topc(A_460))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.98/1.86  tff(c_306, plain, (![D_457, B_458, A_35]: (m1_pre_topc(D_457, B_458) | g1_pre_topc(u1_struct_0(D_457), u1_pre_topc(D_457))!=g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35)) | g1_pre_topc(u1_struct_0(B_458), u1_pre_topc(B_458))!=g1_pre_topc(u1_struct_0(A_35), u1_pre_topc(A_35)) | ~l1_pre_topc(D_457) | ~l1_pre_topc(B_458) | ~l1_pre_topc(A_35))), inference(resolution, [status(thm)], [c_28, c_294])).
% 4.98/1.86  tff(c_1095, plain, (![A_546, B_547]: (m1_pre_topc(A_546, B_547) | g1_pre_topc(u1_struct_0(B_547), u1_pre_topc(B_547))!=g1_pre_topc(u1_struct_0(A_546), u1_pre_topc(A_546)) | ~l1_pre_topc(A_546) | ~l1_pre_topc(B_547) | ~l1_pre_topc(A_546))), inference(reflexivity, [status(thm), theory('equality')], [c_306])).
% 4.98/1.86  tff(c_1101, plain, (![A_546]: (m1_pre_topc(A_546, '#skF_4') | g1_pre_topc(u1_struct_0(A_546), u1_pre_topc(A_546))!='#skF_5' | ~l1_pre_topc(A_546) | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_546))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1095])).
% 4.98/1.86  tff(c_1108, plain, (![A_548]: (m1_pre_topc(A_548, '#skF_4') | g1_pre_topc(u1_struct_0(A_548), u1_pre_topc(A_548))!='#skF_5' | ~l1_pre_topc(A_548))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_1101])).
% 4.98/1.86  tff(c_1139, plain, (![A_551]: (m1_pre_topc(A_551, '#skF_4') | A_551!='#skF_5' | ~l1_pre_topc(A_551) | ~v1_pre_topc(A_551) | ~l1_pre_topc(A_551))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1108])).
% 4.98/1.86  tff(c_554, plain, (![A_505, B_506]: (m1_pre_topc(A_505, B_506) | g1_pre_topc(u1_struct_0(B_506), u1_pre_topc(B_506))!=g1_pre_topc(u1_struct_0(A_505), u1_pre_topc(A_505)) | ~l1_pre_topc(A_505) | ~l1_pre_topc(B_506) | ~l1_pre_topc(A_505))), inference(reflexivity, [status(thm), theory('equality')], [c_306])).
% 4.98/1.86  tff(c_562, plain, (![B_506]: (m1_pre_topc('#skF_4', B_506) | g1_pre_topc(u1_struct_0(B_506), u1_pre_topc(B_506))!='#skF_5' | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(B_506) | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_48, c_554])).
% 4.98/1.86  tff(c_612, plain, (![B_514]: (m1_pre_topc('#skF_4', B_514) | g1_pre_topc(u1_struct_0(B_514), u1_pre_topc(B_514))!='#skF_5' | ~l1_pre_topc(B_514))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_101, c_562])).
% 4.98/1.86  tff(c_689, plain, (![A_518]: (m1_pre_topc('#skF_4', A_518) | A_518!='#skF_5' | ~l1_pre_topc(A_518) | ~v1_pre_topc(A_518) | ~l1_pre_topc(A_518))), inference(superposition, [status(thm), theory('equality')], [c_12, c_612])).
% 4.98/1.86  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_38, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 4.98/1.86  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_75, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_46])).
% 4.98/1.86  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_239])).
% 4.98/1.86  tff(c_493, plain, (![D_490, B_492, C_494, F_493, H_491, E_489, A_495]: (r1_tmap_1(D_490, B_492, E_489, H_491) | ~r1_tmap_1(C_494, B_492, k3_tmap_1(A_495, B_492, D_490, C_494, E_489), H_491) | ~m1_connsp_2(F_493, D_490, H_491) | ~r1_tarski(F_493, u1_struct_0(C_494)) | ~m1_subset_1(H_491, u1_struct_0(C_494)) | ~m1_subset_1(H_491, u1_struct_0(D_490)) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0(D_490))) | ~m1_pre_topc(C_494, D_490) | ~m1_subset_1(E_489, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_490), u1_struct_0(B_492)))) | ~v1_funct_2(E_489, u1_struct_0(D_490), u1_struct_0(B_492)) | ~v1_funct_1(E_489) | ~m1_pre_topc(D_490, A_495) | v2_struct_0(D_490) | ~m1_pre_topc(C_494, A_495) | v2_struct_0(C_494) | ~l1_pre_topc(B_492) | ~v2_pre_topc(B_492) | v2_struct_0(B_492) | ~l1_pre_topc(A_495) | ~v2_pre_topc(A_495) | v2_struct_0(A_495))), inference(cnfTransformation, [status(thm)], [f_190])).
% 4.98/1.86  tff(c_495, plain, (![F_493]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_493, '#skF_5', '#skF_8') | ~r1_tarski(F_493, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_493])).
% 4.98/1.86  tff(c_498, plain, (![F_493]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_493, '#skF_5', '#skF_8') | ~r1_tarski(F_493, u1_struct_0('#skF_4')) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_52, c_50, c_75, c_44, c_495])).
% 4.98/1.86  tff(c_499, plain, (![F_493]: (~m1_connsp_2(F_493, '#skF_5', '#skF_8') | ~r1_tarski(F_493, u1_struct_0('#skF_4')) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_76, c_498])).
% 4.98/1.86  tff(c_500, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_499])).
% 4.98/1.86  tff(c_692, plain, (~v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_689, c_500])).
% 4.98/1.86  tff(c_713, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_159, c_692])).
% 4.98/1.86  tff(c_715, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_499])).
% 4.98/1.86  tff(c_30, plain, (![B_38, A_36]: (r1_tarski(u1_struct_0(B_38), u1_struct_0(A_36)) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.98/1.86  tff(c_142, plain, (![B_433, A_434]: (r1_tarski(u1_struct_0(B_433), u1_struct_0(A_434)) | ~m1_pre_topc(B_433, A_434) | ~l1_pre_topc(A_434))), inference(cnfTransformation, [status(thm)], [f_123])).
% 4.98/1.86  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.98/1.86  tff(c_219, plain, (![B_443, A_444]: (u1_struct_0(B_443)=u1_struct_0(A_444) | ~r1_tarski(u1_struct_0(A_444), u1_struct_0(B_443)) | ~m1_pre_topc(B_443, A_444) | ~l1_pre_topc(A_444))), inference(resolution, [status(thm)], [c_142, c_2])).
% 4.98/1.86  tff(c_227, plain, (![B_38, A_36]: (u1_struct_0(B_38)=u1_struct_0(A_36) | ~m1_pre_topc(A_36, B_38) | ~l1_pre_topc(B_38) | ~m1_pre_topc(B_38, A_36) | ~l1_pre_topc(A_36))), inference(resolution, [status(thm)], [c_30, c_219])).
% 4.98/1.86  tff(c_723, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_5') | ~m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_715, c_227])).
% 4.98/1.86  tff(c_743, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_104, c_723])).
% 4.98/1.86  tff(c_751, plain, (~m1_pre_topc('#skF_5', '#skF_4')), inference(splitLeft, [status(thm)], [c_743])).
% 4.98/1.86  tff(c_1151, plain, (~v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_1139, c_751])).
% 4.98/1.86  tff(c_1190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_159, c_1151])).
% 4.98/1.86  tff(c_1191, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_743])).
% 4.98/1.86  tff(c_26, plain, (![A_32, B_33]: (m1_connsp_2('#skF_1'(A_32, B_33), A_32, B_33) | ~m1_subset_1(B_33, u1_struct_0(A_32)) | ~l1_pre_topc(A_32) | ~v2_pre_topc(A_32) | v2_struct_0(A_32))), inference(cnfTransformation, [status(thm)], [f_112])).
% 4.98/1.86  tff(c_285, plain, (![C_452, A_453, B_454]: (m1_subset_1(C_452, k1_zfmisc_1(u1_struct_0(A_453))) | ~m1_connsp_2(C_452, A_453, B_454) | ~m1_subset_1(B_454, u1_struct_0(A_453)) | ~l1_pre_topc(A_453) | ~v2_pre_topc(A_453) | v2_struct_0(A_453))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.98/1.86  tff(c_289, plain, (![A_455, B_456]: (m1_subset_1('#skF_1'(A_455, B_456), k1_zfmisc_1(u1_struct_0(A_455))) | ~m1_subset_1(B_456, u1_struct_0(A_455)) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455) | v2_struct_0(A_455))), inference(resolution, [status(thm)], [c_26, c_285])).
% 4.98/1.86  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.98/1.86  tff(c_293, plain, (![A_455, B_456]: (r1_tarski('#skF_1'(A_455, B_456), u1_struct_0(A_455)) | ~m1_subset_1(B_456, u1_struct_0(A_455)) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455) | v2_struct_0(A_455))), inference(resolution, [status(thm)], [c_289, c_8])).
% 4.98/1.86  tff(c_1247, plain, (![B_456]: (r1_tarski('#skF_1'('#skF_5', B_456), u1_struct_0('#skF_4')) | ~m1_subset_1(B_456, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1191, c_293])).
% 4.98/1.86  tff(c_1286, plain, (![B_456]: (r1_tarski('#skF_1'('#skF_5', B_456), u1_struct_0('#skF_4')) | ~m1_subset_1(B_456, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_104, c_1191, c_1247])).
% 4.98/1.86  tff(c_1406, plain, (![B_560]: (r1_tarski('#skF_1'('#skF_5', B_560), u1_struct_0('#skF_4')) | ~m1_subset_1(B_560, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1286])).
% 4.98/1.86  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.98/1.86  tff(c_714, plain, (![F_493]: (~m1_connsp_2(F_493, '#skF_5', '#skF_8') | ~r1_tarski(F_493, u1_struct_0('#skF_4')) | ~m1_subset_1(F_493, k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(splitRight, [status(thm)], [c_499])).
% 4.98/1.86  tff(c_1307, plain, (![F_552]: (~m1_connsp_2(F_552, '#skF_5', '#skF_8') | ~r1_tarski(F_552, u1_struct_0('#skF_4')) | ~m1_subset_1(F_552, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_1191, c_714])).
% 4.98/1.86  tff(c_1320, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_1307])).
% 4.98/1.86  tff(c_1531, plain, (![B_564]: (~m1_connsp_2('#skF_1'('#skF_5', B_564), '#skF_5', '#skF_8') | ~m1_subset_1(B_564, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1406, c_1320])).
% 4.98/1.86  tff(c_1535, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_26, c_1531])).
% 4.98/1.86  tff(c_1538, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_104, c_44, c_1191, c_44, c_1535])).
% 4.98/1.86  tff(c_1540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1538])).
% 4.98/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.98/1.86  
% 4.98/1.86  Inference rules
% 4.98/1.86  ----------------------
% 4.98/1.86  #Ref     : 18
% 4.98/1.86  #Sup     : 278
% 4.98/1.86  #Fact    : 0
% 4.98/1.86  #Define  : 0
% 4.98/1.86  #Split   : 9
% 4.98/1.86  #Chain   : 0
% 4.98/1.86  #Close   : 0
% 4.98/1.86  
% 4.98/1.86  Ordering : KBO
% 4.98/1.86  
% 4.98/1.86  Simplification rules
% 4.98/1.86  ----------------------
% 4.98/1.86  #Subsume      : 75
% 4.98/1.86  #Demod        : 384
% 4.98/1.86  #Tautology    : 72
% 4.98/1.86  #SimpNegUnit  : 14
% 4.98/1.86  #BackRed      : 7
% 4.98/1.86  
% 4.98/1.86  #Partial instantiations: 0
% 4.98/1.86  #Strategies tried      : 1
% 4.98/1.86  
% 4.98/1.86  Timing (in seconds)
% 4.98/1.86  ----------------------
% 4.98/1.87  Preprocessing        : 0.41
% 4.98/1.87  Parsing              : 0.20
% 4.98/1.87  CNF conversion       : 0.06
% 4.98/1.87  Main loop            : 0.68
% 4.98/1.87  Inferencing          : 0.23
% 4.98/1.87  Reduction            : 0.23
% 4.98/1.87  Demodulation         : 0.17
% 4.98/1.87  BG Simplification    : 0.03
% 4.98/1.87  Subsumption          : 0.15
% 4.98/1.87  Abstraction          : 0.03
% 4.98/1.87  MUC search           : 0.00
% 4.98/1.87  Cooper               : 0.00
% 4.98/1.87  Total                : 1.13
% 4.98/1.87  Index Insertion      : 0.00
% 4.98/1.87  Index Deletion       : 0.00
% 4.98/1.87  Index Matching       : 0.00
% 4.98/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
