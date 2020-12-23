%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:40 EST 2020

% Result     : Theorem 3.74s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :  117 (1294 expanded)
%              Number of leaves         :   38 ( 478 expanded)
%              Depth                    :   18
%              Number of atoms          :  294 (7658 expanded)
%              Number of equality atoms :   11 ( 643 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff(f_220,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_104,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_90,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_74,axiom,(
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

tff(f_171,axiom,(
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

tff(c_56,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_70,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_68,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_54,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_123,plain,(
    ! [B_421,A_422] :
      ( v2_pre_topc(B_421)
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_132,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_123])).

tff(c_139,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_132])).

tff(c_96,plain,(
    ! [B_417,A_418] :
      ( l1_pre_topc(B_417)
      | ~ m1_pre_topc(B_417,A_418)
      | ~ l1_pre_topc(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_105,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_96])).

tff(c_112,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_105])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_96])).

tff(c_109,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_507,plain,(
    ! [B_445,C_446,A_447] :
      ( m1_pre_topc(B_445,C_446)
      | ~ r1_tarski(u1_struct_0(B_445),u1_struct_0(C_446))
      | ~ m1_pre_topc(C_446,A_447)
      | ~ m1_pre_topc(B_445,A_447)
      | ~ l1_pre_topc(A_447)
      | ~ v2_pre_topc(A_447) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_512,plain,(
    ! [B_448,A_449] :
      ( m1_pre_topc(B_448,B_448)
      | ~ m1_pre_topc(B_448,A_449)
      | ~ l1_pre_topc(A_449)
      | ~ v2_pre_topc(A_449) ) ),
    inference(resolution,[status(thm)],[c_6,c_507])).

tff(c_530,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_512])).

tff(c_549,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_530])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_173,plain,(
    ! [A_428,B_429] :
      ( m1_pre_topc(A_428,g1_pre_topc(u1_struct_0(B_429),u1_pre_topc(B_429)))
      | ~ m1_pre_topc(A_428,B_429)
      | ~ l1_pre_topc(B_429)
      | ~ l1_pre_topc(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_188,plain,(
    ! [A_428] :
      ( m1_pre_topc(A_428,'#skF_5')
      | ~ m1_pre_topc(A_428,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_428) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_173])).

tff(c_196,plain,(
    ! [A_428] :
      ( m1_pre_topc(A_428,'#skF_5')
      | ~ m1_pre_topc(A_428,'#skF_4')
      | ~ l1_pre_topc(A_428) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_188])).

tff(c_24,plain,(
    ! [A_21] :
      ( m1_pre_topc(A_21,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_283,plain,(
    ! [A_435,B_436] :
      ( m1_pre_topc(A_435,B_436)
      | ~ m1_pre_topc(A_435,g1_pre_topc(u1_struct_0(B_436),u1_pre_topc(B_436)))
      | ~ l1_pre_topc(B_436)
      | ~ l1_pre_topc(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_293,plain,(
    ! [A_435] :
      ( m1_pre_topc(A_435,'#skF_4')
      | ~ m1_pre_topc(A_435,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_283])).

tff(c_306,plain,(
    ! [A_439] :
      ( m1_pre_topc(A_439,'#skF_4')
      | ~ m1_pre_topc(A_439,'#skF_5')
      | ~ l1_pre_topc(A_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_293])).

tff(c_317,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_306])).

tff(c_324,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_317])).

tff(c_532,plain,
    ( m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_512])).

tff(c_552,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_532])).

tff(c_664,plain,(
    ! [B_453,C_454,A_455] :
      ( r1_tarski(u1_struct_0(B_453),u1_struct_0(C_454))
      | ~ m1_pre_topc(B_453,C_454)
      | ~ m1_pre_topc(C_454,A_455)
      | ~ m1_pre_topc(B_453,A_455)
      | ~ l1_pre_topc(A_455)
      | ~ v2_pre_topc(A_455) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_666,plain,(
    ! [B_453] :
      ( r1_tarski(u1_struct_0(B_453),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_453,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_552,c_664])).

tff(c_691,plain,(
    ! [B_453] :
      ( r1_tarski(u1_struct_0(B_453),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_453,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_112,c_666])).

tff(c_129,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_123])).

tff(c_136,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_129])).

tff(c_668,plain,(
    ! [B_453] :
      ( r1_tarski(u1_struct_0(B_453),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_453,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_549,c_664])).

tff(c_722,plain,(
    ! [B_457] :
      ( r1_tarski(u1_struct_0(B_457),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_457,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_668])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_736,plain,(
    ! [B_460] :
      ( u1_struct_0(B_460) = u1_struct_0('#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0(B_460))
      | ~ m1_pre_topc(B_460,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_722,c_2])).

tff(c_748,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_691,c_736])).

tff(c_760,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_748])).

tff(c_765,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_760])).

tff(c_768,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_196,c_765])).

tff(c_772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_549,c_768])).

tff(c_773,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( m1_connsp_2('#skF_1'(A_18,B_19),A_18,B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_775,plain,(
    ! [C_461,A_462,B_463] :
      ( m1_subset_1(C_461,k1_zfmisc_1(u1_struct_0(A_462)))
      | ~ m1_connsp_2(C_461,A_462,B_463)
      | ~ m1_subset_1(B_463,u1_struct_0(A_462))
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1179,plain,(
    ! [A_489,B_490] :
      ( m1_subset_1('#skF_1'(A_489,B_490),k1_zfmisc_1(u1_struct_0(A_489)))
      | ~ m1_subset_1(B_490,u1_struct_0(A_489))
      | ~ l1_pre_topc(A_489)
      | ~ v2_pre_topc(A_489)
      | v2_struct_0(A_489) ) ),
    inference(resolution,[status(thm)],[c_22,c_775])).

tff(c_1185,plain,(
    ! [B_490] :
      ( m1_subset_1('#skF_1'('#skF_5',B_490),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_490,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_773,c_1179])).

tff(c_1188,plain,(
    ! [B_490] :
      ( m1_subset_1('#skF_1'('#skF_5',B_490),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_490,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_112,c_773,c_1185])).

tff(c_1190,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_5',B_491),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1188])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1195,plain,(
    ! [B_492] :
      ( r1_tarski('#skF_1'('#skF_5',B_492),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_492,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1190,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_40,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_36,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_74,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_36])).

tff(c_64,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_62,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_52,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_50,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_820,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_819,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_48])).

tff(c_774,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_760])).

tff(c_38,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_897,plain,(
    ! [D_467,E_471,B_469,H_466,C_470,F_465,A_468] :
      ( r1_tmap_1(D_467,B_469,E_471,H_466)
      | ~ r1_tmap_1(C_470,B_469,k3_tmap_1(A_468,B_469,D_467,C_470,E_471),H_466)
      | ~ m1_connsp_2(F_465,D_467,H_466)
      | ~ r1_tarski(F_465,u1_struct_0(C_470))
      | ~ m1_subset_1(H_466,u1_struct_0(C_470))
      | ~ m1_subset_1(H_466,u1_struct_0(D_467))
      | ~ m1_subset_1(F_465,k1_zfmisc_1(u1_struct_0(D_467)))
      | ~ m1_pre_topc(C_470,D_467)
      | ~ m1_subset_1(E_471,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_467),u1_struct_0(B_469))))
      | ~ v1_funct_2(E_471,u1_struct_0(D_467),u1_struct_0(B_469))
      | ~ v1_funct_1(E_471)
      | ~ m1_pre_topc(D_467,A_468)
      | v2_struct_0(D_467)
      | ~ m1_pre_topc(C_470,A_468)
      | v2_struct_0(C_470)
      | ~ l1_pre_topc(B_469)
      | ~ v2_pre_topc(B_469)
      | v2_struct_0(B_469)
      | ~ l1_pre_topc(A_468)
      | ~ v2_pre_topc(A_468)
      | v2_struct_0(A_468) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_899,plain,(
    ! [F_465] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_465,'#skF_5','#skF_8')
      | ~ r1_tarski(F_465,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_465,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_38,c_897])).

tff(c_902,plain,(
    ! [F_465] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_465,'#skF_5','#skF_8')
      | ~ r1_tarski(F_465,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_465,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_820,c_773,c_819,c_773,c_774,c_773,c_42,c_773,c_42,c_899])).

tff(c_995,plain,(
    ! [F_474] :
      ( ~ m1_connsp_2(F_474,'#skF_5','#skF_8')
      | ~ r1_tarski(F_474,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_474,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_74,c_902])).

tff(c_1000,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_995])).

tff(c_1203,plain,(
    ! [B_493] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_493),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1195,c_1000])).

tff(c_1207,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1203])).

tff(c_1210,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_112,c_42,c_773,c_42,c_1207])).

tff(c_1212,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n002.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:12:21 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.74/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.57  
% 3.74/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.74/1.57  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.74/1.57  
% 3.74/1.57  %Foreground sorts:
% 3.74/1.57  
% 3.74/1.57  
% 3.74/1.57  %Background operators:
% 3.74/1.57  
% 3.74/1.57  
% 3.74/1.57  %Foreground operators:
% 3.74/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.74/1.57  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.74/1.57  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.74/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.74/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.57  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.74/1.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.74/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.74/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.74/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.74/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.74/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.74/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.74/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.74/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.74/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.74/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.74/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.74/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.74/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.74/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.74/1.57  
% 3.91/1.59  tff(f_220, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.91/1.59  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.91/1.59  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.91/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.91/1.59  tff(f_104, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 3.91/1.59  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.91/1.59  tff(f_90, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.91/1.59  tff(f_86, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.91/1.59  tff(f_74, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.91/1.59  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.91/1.59  tff(f_171, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.91/1.59  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_123, plain, (![B_421, A_422]: (v2_pre_topc(B_421) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.91/1.59  tff(c_132, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_123])).
% 3.91/1.59  tff(c_139, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_132])).
% 3.91/1.59  tff(c_96, plain, (![B_417, A_418]: (l1_pre_topc(B_417) | ~m1_pre_topc(B_417, A_418) | ~l1_pre_topc(A_418))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.91/1.59  tff(c_105, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_96])).
% 3.91/1.59  tff(c_112, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_105])).
% 3.91/1.59  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_102, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_96])).
% 3.91/1.59  tff(c_109, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102])).
% 3.91/1.59  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.59  tff(c_507, plain, (![B_445, C_446, A_447]: (m1_pre_topc(B_445, C_446) | ~r1_tarski(u1_struct_0(B_445), u1_struct_0(C_446)) | ~m1_pre_topc(C_446, A_447) | ~m1_pre_topc(B_445, A_447) | ~l1_pre_topc(A_447) | ~v2_pre_topc(A_447))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.91/1.59  tff(c_512, plain, (![B_448, A_449]: (m1_pre_topc(B_448, B_448) | ~m1_pre_topc(B_448, A_449) | ~l1_pre_topc(A_449) | ~v2_pre_topc(A_449))), inference(resolution, [status(thm)], [c_6, c_507])).
% 3.91/1.59  tff(c_530, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_512])).
% 3.91/1.59  tff(c_549, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_530])).
% 3.91/1.59  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_173, plain, (![A_428, B_429]: (m1_pre_topc(A_428, g1_pre_topc(u1_struct_0(B_429), u1_pre_topc(B_429))) | ~m1_pre_topc(A_428, B_429) | ~l1_pre_topc(B_429) | ~l1_pre_topc(A_428))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.59  tff(c_188, plain, (![A_428]: (m1_pre_topc(A_428, '#skF_5') | ~m1_pre_topc(A_428, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_428))), inference(superposition, [status(thm), theory('equality')], [c_46, c_173])).
% 3.91/1.59  tff(c_196, plain, (![A_428]: (m1_pre_topc(A_428, '#skF_5') | ~m1_pre_topc(A_428, '#skF_4') | ~l1_pre_topc(A_428))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_188])).
% 3.91/1.59  tff(c_24, plain, (![A_21]: (m1_pre_topc(A_21, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.91/1.59  tff(c_283, plain, (![A_435, B_436]: (m1_pre_topc(A_435, B_436) | ~m1_pre_topc(A_435, g1_pre_topc(u1_struct_0(B_436), u1_pre_topc(B_436))) | ~l1_pre_topc(B_436) | ~l1_pre_topc(A_435))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.91/1.59  tff(c_293, plain, (![A_435]: (m1_pre_topc(A_435, '#skF_4') | ~m1_pre_topc(A_435, '#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_435))), inference(superposition, [status(thm), theory('equality')], [c_46, c_283])).
% 3.91/1.59  tff(c_306, plain, (![A_439]: (m1_pre_topc(A_439, '#skF_4') | ~m1_pre_topc(A_439, '#skF_5') | ~l1_pre_topc(A_439))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_293])).
% 3.91/1.59  tff(c_317, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_24, c_306])).
% 3.91/1.59  tff(c_324, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_317])).
% 3.91/1.59  tff(c_532, plain, (m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_512])).
% 3.91/1.59  tff(c_552, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_532])).
% 3.91/1.59  tff(c_664, plain, (![B_453, C_454, A_455]: (r1_tarski(u1_struct_0(B_453), u1_struct_0(C_454)) | ~m1_pre_topc(B_453, C_454) | ~m1_pre_topc(C_454, A_455) | ~m1_pre_topc(B_453, A_455) | ~l1_pre_topc(A_455) | ~v2_pre_topc(A_455))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.91/1.59  tff(c_666, plain, (![B_453]: (r1_tarski(u1_struct_0(B_453), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_453, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_552, c_664])).
% 3.91/1.59  tff(c_691, plain, (![B_453]: (r1_tarski(u1_struct_0(B_453), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_453, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_112, c_666])).
% 3.91/1.59  tff(c_129, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_123])).
% 3.91/1.59  tff(c_136, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_129])).
% 3.91/1.59  tff(c_668, plain, (![B_453]: (r1_tarski(u1_struct_0(B_453), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_453, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_549, c_664])).
% 3.91/1.59  tff(c_722, plain, (![B_457]: (r1_tarski(u1_struct_0(B_457), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_457, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_668])).
% 3.91/1.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.91/1.59  tff(c_736, plain, (![B_460]: (u1_struct_0(B_460)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0(B_460)) | ~m1_pre_topc(B_460, '#skF_4'))), inference(resolution, [status(thm)], [c_722, c_2])).
% 3.91/1.59  tff(c_748, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_691, c_736])).
% 3.91/1.59  tff(c_760, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_324, c_748])).
% 3.91/1.59  tff(c_765, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_760])).
% 3.91/1.59  tff(c_768, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_196, c_765])).
% 3.91/1.59  tff(c_772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_549, c_768])).
% 3.91/1.59  tff(c_773, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_760])).
% 3.91/1.59  tff(c_22, plain, (![A_18, B_19]: (m1_connsp_2('#skF_1'(A_18, B_19), A_18, B_19) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.91/1.59  tff(c_775, plain, (![C_461, A_462, B_463]: (m1_subset_1(C_461, k1_zfmisc_1(u1_struct_0(A_462))) | ~m1_connsp_2(C_461, A_462, B_463) | ~m1_subset_1(B_463, u1_struct_0(A_462)) | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.91/1.59  tff(c_1179, plain, (![A_489, B_490]: (m1_subset_1('#skF_1'(A_489, B_490), k1_zfmisc_1(u1_struct_0(A_489))) | ~m1_subset_1(B_490, u1_struct_0(A_489)) | ~l1_pre_topc(A_489) | ~v2_pre_topc(A_489) | v2_struct_0(A_489))), inference(resolution, [status(thm)], [c_22, c_775])).
% 3.91/1.59  tff(c_1185, plain, (![B_490]: (m1_subset_1('#skF_1'('#skF_5', B_490), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_490, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_773, c_1179])).
% 3.91/1.59  tff(c_1188, plain, (![B_490]: (m1_subset_1('#skF_1'('#skF_5', B_490), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_490, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_139, c_112, c_773, c_1185])).
% 3.91/1.59  tff(c_1190, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_5', B_491), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_491, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1188])).
% 3.91/1.59  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.59  tff(c_1195, plain, (![B_492]: (r1_tarski('#skF_1'('#skF_5', B_492), u1_struct_0('#skF_4')) | ~m1_subset_1(B_492, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1190, c_8])).
% 3.91/1.59  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.59  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_40, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_36, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_74, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.91/1.59  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_50, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_820, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_773, c_50])).
% 3.91/1.59  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_819, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_773, c_48])).
% 3.91/1.59  tff(c_774, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_760])).
% 3.91/1.59  tff(c_38, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.91/1.59  tff(c_897, plain, (![D_467, E_471, B_469, H_466, C_470, F_465, A_468]: (r1_tmap_1(D_467, B_469, E_471, H_466) | ~r1_tmap_1(C_470, B_469, k3_tmap_1(A_468, B_469, D_467, C_470, E_471), H_466) | ~m1_connsp_2(F_465, D_467, H_466) | ~r1_tarski(F_465, u1_struct_0(C_470)) | ~m1_subset_1(H_466, u1_struct_0(C_470)) | ~m1_subset_1(H_466, u1_struct_0(D_467)) | ~m1_subset_1(F_465, k1_zfmisc_1(u1_struct_0(D_467))) | ~m1_pre_topc(C_470, D_467) | ~m1_subset_1(E_471, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_467), u1_struct_0(B_469)))) | ~v1_funct_2(E_471, u1_struct_0(D_467), u1_struct_0(B_469)) | ~v1_funct_1(E_471) | ~m1_pre_topc(D_467, A_468) | v2_struct_0(D_467) | ~m1_pre_topc(C_470, A_468) | v2_struct_0(C_470) | ~l1_pre_topc(B_469) | ~v2_pre_topc(B_469) | v2_struct_0(B_469) | ~l1_pre_topc(A_468) | ~v2_pre_topc(A_468) | v2_struct_0(A_468))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.91/1.59  tff(c_899, plain, (![F_465]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_465, '#skF_5', '#skF_8') | ~r1_tarski(F_465, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_465, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_897])).
% 3.91/1.59  tff(c_902, plain, (![F_465]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_465, '#skF_5', '#skF_8') | ~r1_tarski(F_465, u1_struct_0('#skF_4')) | ~m1_subset_1(F_465, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_820, c_773, c_819, c_773, c_774, c_773, c_42, c_773, c_42, c_899])).
% 3.91/1.59  tff(c_995, plain, (![F_474]: (~m1_connsp_2(F_474, '#skF_5', '#skF_8') | ~r1_tarski(F_474, u1_struct_0('#skF_4')) | ~m1_subset_1(F_474, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_74, c_902])).
% 3.91/1.59  tff(c_1000, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_995])).
% 3.91/1.59  tff(c_1203, plain, (![B_493]: (~m1_connsp_2('#skF_1'('#skF_5', B_493), '#skF_5', '#skF_8') | ~m1_subset_1(B_493, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1195, c_1000])).
% 3.91/1.59  tff(c_1207, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1203])).
% 3.91/1.59  tff(c_1210, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_139, c_112, c_42, c_773, c_42, c_1207])).
% 3.91/1.59  tff(c_1212, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1210])).
% 3.91/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.91/1.59  
% 3.91/1.59  Inference rules
% 3.91/1.59  ----------------------
% 3.91/1.59  #Ref     : 0
% 3.91/1.59  #Sup     : 218
% 3.91/1.59  #Fact    : 0
% 3.91/1.59  #Define  : 0
% 3.91/1.59  #Split   : 5
% 3.91/1.59  #Chain   : 0
% 3.91/1.59  #Close   : 0
% 3.91/1.59  
% 3.91/1.59  Ordering : KBO
% 3.91/1.59  
% 3.91/1.59  Simplification rules
% 3.91/1.59  ----------------------
% 3.91/1.59  #Subsume      : 61
% 3.91/1.59  #Demod        : 346
% 3.91/1.59  #Tautology    : 83
% 3.91/1.59  #SimpNegUnit  : 3
% 3.91/1.59  #BackRed      : 7
% 3.91/1.59  
% 3.91/1.59  #Partial instantiations: 0
% 3.91/1.59  #Strategies tried      : 1
% 3.91/1.59  
% 3.91/1.59  Timing (in seconds)
% 3.91/1.59  ----------------------
% 3.91/1.59  Preprocessing        : 0.39
% 3.91/1.59  Parsing              : 0.19
% 3.91/1.59  CNF conversion       : 0.06
% 3.91/1.59  Main loop            : 0.43
% 3.91/1.59  Inferencing          : 0.14
% 3.91/1.59  Reduction            : 0.15
% 3.91/1.59  Demodulation         : 0.11
% 3.91/1.59  BG Simplification    : 0.02
% 3.91/1.59  Subsumption          : 0.09
% 3.91/1.59  Abstraction          : 0.02
% 3.91/1.59  MUC search           : 0.00
% 3.91/1.59  Cooper               : 0.00
% 3.91/1.59  Total                : 0.86
% 3.91/1.59  Index Insertion      : 0.00
% 3.91/1.59  Index Deletion       : 0.00
% 3.91/1.59  Index Matching       : 0.00
% 3.91/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
