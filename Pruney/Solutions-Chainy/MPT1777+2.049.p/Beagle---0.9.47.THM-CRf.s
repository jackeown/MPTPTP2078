%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:39 EST 2020

% Result     : Theorem 4.12s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 822 expanded)
%              Number of leaves         :   39 ( 302 expanded)
%              Depth                    :   18
%              Number of atoms          :  273 (4169 expanded)
%              Number of equality atoms :   12 ( 365 expanded)
%              Maximal formula depth    :   29 (   4 average)
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

tff(f_222,negated_conjecture,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_51,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_102,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_86,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_173,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_125,plain,(
    ! [B_420,A_421] :
      ( v2_pre_topc(B_420)
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_134,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_125])).

tff(c_141,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_134])).

tff(c_88,plain,(
    ! [B_412,A_413] :
      ( l1_pre_topc(B_412)
      | ~ m1_pre_topc(B_412,A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_88])).

tff(c_104,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_88])).

tff(c_101,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_94])).

tff(c_30,plain,(
    ! [A_27] :
      ( m1_pre_topc(A_27,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_306,plain,(
    ! [A_443,B_444] :
      ( m1_pre_topc(A_443,g1_pre_topc(u1_struct_0(B_444),u1_pre_topc(B_444)))
      | ~ m1_pre_topc(A_443,B_444)
      | ~ l1_pre_topc(B_444)
      | ~ l1_pre_topc(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_327,plain,(
    ! [A_443] :
      ( m1_pre_topc(A_443,'#skF_5')
      | ~ m1_pre_topc(A_443,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_443) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_306])).

tff(c_338,plain,(
    ! [A_443] :
      ( m1_pre_topc(A_443,'#skF_5')
      | ~ m1_pre_topc(A_443,'#skF_4')
      | ~ l1_pre_topc(A_443) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_327])).

tff(c_377,plain,(
    ! [A_446,B_447] :
      ( m1_pre_topc(A_446,B_447)
      | ~ m1_pre_topc(A_446,g1_pre_topc(u1_struct_0(B_447),u1_pre_topc(B_447)))
      | ~ l1_pre_topc(B_447)
      | ~ l1_pre_topc(A_446) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_395,plain,(
    ! [A_446] :
      ( m1_pre_topc(A_446,'#skF_4')
      | ~ m1_pre_topc(A_446,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_446) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_377])).

tff(c_441,plain,(
    ! [A_449] :
      ( m1_pre_topc(A_449,'#skF_4')
      | ~ m1_pre_topc(A_449,'#skF_5')
      | ~ l1_pre_topc(A_449) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_395])).

tff(c_460,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_441])).

tff(c_473,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_460])).

tff(c_142,plain,(
    ! [B_422,A_423] :
      ( m1_subset_1(u1_struct_0(B_422),k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [B_422,A_423] :
      ( r1_tarski(u1_struct_0(B_422),u1_struct_0(A_423))
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_147,plain,(
    ! [B_424,A_425] :
      ( r1_tarski(u1_struct_0(B_424),u1_struct_0(A_425))
      | ~ m1_pre_topc(B_424,A_425)
      | ~ l1_pre_topc(A_425) ) ),
    inference(resolution,[status(thm)],[c_142,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_518,plain,(
    ! [B_451,A_452] :
      ( u1_struct_0(B_451) = u1_struct_0(A_452)
      | ~ r1_tarski(u1_struct_0(A_452),u1_struct_0(B_451))
      | ~ m1_pre_topc(B_451,A_452)
      | ~ l1_pre_topc(A_452) ) ),
    inference(resolution,[status(thm)],[c_147,c_2])).

tff(c_530,plain,(
    ! [B_455,A_456] :
      ( u1_struct_0(B_455) = u1_struct_0(A_456)
      | ~ m1_pre_topc(A_456,B_455)
      | ~ l1_pre_topc(B_455)
      | ~ m1_pre_topc(B_455,A_456)
      | ~ l1_pre_topc(A_456) ) ),
    inference(resolution,[status(thm)],[c_146,c_518])).

tff(c_532,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_473,c_530])).

tff(c_551,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_101,c_532])).

tff(c_571,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_551])).

tff(c_574,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_338,c_571])).

tff(c_577,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_574])).

tff(c_587,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_577])).

tff(c_591,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_587])).

tff(c_592,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( m1_connsp_2('#skF_1'(A_18,B_19),A_18,B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_748,plain,(
    ! [C_457,A_458,B_459] :
      ( m1_subset_1(C_457,k1_zfmisc_1(u1_struct_0(A_458)))
      | ~ m1_connsp_2(C_457,A_458,B_459)
      | ~ m1_subset_1(B_459,u1_struct_0(A_458))
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458)
      | v2_struct_0(A_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1446,plain,(
    ! [A_490,B_491] :
      ( m1_subset_1('#skF_1'(A_490,B_491),k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ m1_subset_1(B_491,u1_struct_0(A_490))
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_22,c_748])).

tff(c_1452,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_5',B_491),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_592,c_1446])).

tff(c_1455,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_5',B_491),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_104,c_592,c_1452])).

tff(c_1674,plain,(
    ! [B_493] :
      ( m1_subset_1('#skF_1'('#skF_5',B_493),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1455])).

tff(c_1682,plain,(
    ! [B_494] :
      ( r1_tarski('#skF_1'('#skF_5',B_494),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_494,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1674,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_682,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_50])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_683,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_592,c_52])).

tff(c_593,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_551])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_757,plain,(
    ! [A_460,C_465,D_466,B_461,E_463,H_464,F_462] :
      ( r1_tmap_1(D_466,B_461,E_463,H_464)
      | ~ r1_tmap_1(C_465,B_461,k3_tmap_1(A_460,B_461,D_466,C_465,E_463),H_464)
      | ~ m1_connsp_2(F_462,D_466,H_464)
      | ~ r1_tarski(F_462,u1_struct_0(C_465))
      | ~ m1_subset_1(H_464,u1_struct_0(C_465))
      | ~ m1_subset_1(H_464,u1_struct_0(D_466))
      | ~ m1_subset_1(F_462,k1_zfmisc_1(u1_struct_0(D_466)))
      | ~ m1_pre_topc(C_465,D_466)
      | ~ m1_subset_1(E_463,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_466),u1_struct_0(B_461))))
      | ~ v1_funct_2(E_463,u1_struct_0(D_466),u1_struct_0(B_461))
      | ~ v1_funct_1(E_463)
      | ~ m1_pre_topc(D_466,A_460)
      | v2_struct_0(D_466)
      | ~ m1_pre_topc(C_465,A_460)
      | v2_struct_0(C_465)
      | ~ l1_pre_topc(B_461)
      | ~ v2_pre_topc(B_461)
      | v2_struct_0(B_461)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_759,plain,(
    ! [F_462] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_462,'#skF_5','#skF_8')
      | ~ r1_tarski(F_462,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_462,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_40,c_757])).

tff(c_762,plain,(
    ! [F_462] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_462,'#skF_5','#skF_8')
      | ~ r1_tarski(F_462,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_462,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3'))))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_683,c_592,c_592,c_593,c_592,c_44,c_592,c_44,c_759])).

tff(c_763,plain,(
    ! [F_462] :
      ( ~ m1_connsp_2(F_462,'#skF_5','#skF_8')
      | ~ r1_tarski(F_462,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_462,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_76,c_762])).

tff(c_919,plain,(
    ! [F_477] :
      ( ~ m1_connsp_2(F_477,'#skF_5','#skF_8')
      | ~ r1_tarski(F_477,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_477,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_682,c_763])).

tff(c_941,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_919])).

tff(c_1772,plain,(
    ! [B_497] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_497),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1682,c_941])).

tff(c_1776,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1772])).

tff(c_1779,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_104,c_44,c_592,c_44,c_1776])).

tff(c_1781,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1779])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.12/1.63  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.64  
% 4.12/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.65  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.12/1.65  
% 4.12/1.65  %Foreground sorts:
% 4.12/1.65  
% 4.12/1.65  
% 4.12/1.65  %Background operators:
% 4.12/1.65  
% 4.12/1.65  
% 4.12/1.65  %Foreground operators:
% 4.12/1.65  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.12/1.65  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.12/1.65  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.12/1.65  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.12/1.65  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.65  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.12/1.65  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.12/1.65  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.12/1.65  tff('#skF_7', type, '#skF_7': $i).
% 4.12/1.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.65  tff('#skF_5', type, '#skF_5': $i).
% 4.12/1.65  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.65  tff('#skF_6', type, '#skF_6': $i).
% 4.12/1.65  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.65  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.65  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.12/1.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.65  tff('#skF_8', type, '#skF_8': $i).
% 4.12/1.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.65  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.65  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.65  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.12/1.65  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.12/1.65  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.12/1.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.12/1.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.65  
% 4.12/1.68  tff(f_222, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.12/1.68  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.12/1.68  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.12/1.68  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.12/1.68  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.12/1.68  tff(f_102, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.12/1.68  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.12/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.12/1.68  tff(f_86, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.12/1.68  tff(f_74, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.12/1.68  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.12/1.68  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_125, plain, (![B_420, A_421]: (v2_pre_topc(B_420) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.12/1.68  tff(c_134, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_125])).
% 4.12/1.68  tff(c_141, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_134])).
% 4.12/1.68  tff(c_88, plain, (![B_412, A_413]: (l1_pre_topc(B_412) | ~m1_pre_topc(B_412, A_413) | ~l1_pre_topc(A_413))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.12/1.68  tff(c_97, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_88])).
% 4.12/1.68  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 4.12/1.68  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_94, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_88])).
% 4.12/1.68  tff(c_101, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_94])).
% 4.12/1.68  tff(c_30, plain, (![A_27]: (m1_pre_topc(A_27, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.12/1.68  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_306, plain, (![A_443, B_444]: (m1_pre_topc(A_443, g1_pre_topc(u1_struct_0(B_444), u1_pre_topc(B_444))) | ~m1_pre_topc(A_443, B_444) | ~l1_pre_topc(B_444) | ~l1_pre_topc(A_443))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.12/1.68  tff(c_327, plain, (![A_443]: (m1_pre_topc(A_443, '#skF_5') | ~m1_pre_topc(A_443, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_443))), inference(superposition, [status(thm), theory('equality')], [c_48, c_306])).
% 4.12/1.68  tff(c_338, plain, (![A_443]: (m1_pre_topc(A_443, '#skF_5') | ~m1_pre_topc(A_443, '#skF_4') | ~l1_pre_topc(A_443))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_327])).
% 4.12/1.68  tff(c_377, plain, (![A_446, B_447]: (m1_pre_topc(A_446, B_447) | ~m1_pre_topc(A_446, g1_pre_topc(u1_struct_0(B_447), u1_pre_topc(B_447))) | ~l1_pre_topc(B_447) | ~l1_pre_topc(A_446))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.12/1.68  tff(c_395, plain, (![A_446]: (m1_pre_topc(A_446, '#skF_4') | ~m1_pre_topc(A_446, '#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_446))), inference(superposition, [status(thm), theory('equality')], [c_48, c_377])).
% 4.12/1.68  tff(c_441, plain, (![A_449]: (m1_pre_topc(A_449, '#skF_4') | ~m1_pre_topc(A_449, '#skF_5') | ~l1_pre_topc(A_449))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_395])).
% 4.12/1.68  tff(c_460, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_30, c_441])).
% 4.12/1.68  tff(c_473, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_460])).
% 4.12/1.68  tff(c_142, plain, (![B_422, A_423]: (m1_subset_1(u1_struct_0(B_422), k1_zfmisc_1(u1_struct_0(A_423))) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_102])).
% 4.12/1.68  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.12/1.68  tff(c_146, plain, (![B_422, A_423]: (r1_tarski(u1_struct_0(B_422), u1_struct_0(A_423)) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423))), inference(resolution, [status(thm)], [c_142, c_8])).
% 4.12/1.68  tff(c_147, plain, (![B_424, A_425]: (r1_tarski(u1_struct_0(B_424), u1_struct_0(A_425)) | ~m1_pre_topc(B_424, A_425) | ~l1_pre_topc(A_425))), inference(resolution, [status(thm)], [c_142, c_8])).
% 4.12/1.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.12/1.68  tff(c_518, plain, (![B_451, A_452]: (u1_struct_0(B_451)=u1_struct_0(A_452) | ~r1_tarski(u1_struct_0(A_452), u1_struct_0(B_451)) | ~m1_pre_topc(B_451, A_452) | ~l1_pre_topc(A_452))), inference(resolution, [status(thm)], [c_147, c_2])).
% 4.12/1.68  tff(c_530, plain, (![B_455, A_456]: (u1_struct_0(B_455)=u1_struct_0(A_456) | ~m1_pre_topc(A_456, B_455) | ~l1_pre_topc(B_455) | ~m1_pre_topc(B_455, A_456) | ~l1_pre_topc(A_456))), inference(resolution, [status(thm)], [c_146, c_518])).
% 4.12/1.68  tff(c_532, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_473, c_530])).
% 4.12/1.68  tff(c_551, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_101, c_532])).
% 4.12/1.68  tff(c_571, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_551])).
% 4.12/1.68  tff(c_574, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_338, c_571])).
% 4.12/1.68  tff(c_577, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_574])).
% 4.12/1.68  tff(c_587, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_577])).
% 4.12/1.68  tff(c_591, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_587])).
% 4.12/1.68  tff(c_592, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_551])).
% 4.12/1.68  tff(c_22, plain, (![A_18, B_19]: (m1_connsp_2('#skF_1'(A_18, B_19), A_18, B_19) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.12/1.68  tff(c_748, plain, (![C_457, A_458, B_459]: (m1_subset_1(C_457, k1_zfmisc_1(u1_struct_0(A_458))) | ~m1_connsp_2(C_457, A_458, B_459) | ~m1_subset_1(B_459, u1_struct_0(A_458)) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458) | v2_struct_0(A_458))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.12/1.68  tff(c_1446, plain, (![A_490, B_491]: (m1_subset_1('#skF_1'(A_490, B_491), k1_zfmisc_1(u1_struct_0(A_490))) | ~m1_subset_1(B_491, u1_struct_0(A_490)) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(resolution, [status(thm)], [c_22, c_748])).
% 4.12/1.68  tff(c_1452, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_5', B_491), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_491, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_592, c_1446])).
% 4.12/1.68  tff(c_1455, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_5', B_491), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_491, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_104, c_592, c_1452])).
% 4.12/1.68  tff(c_1674, plain, (![B_493]: (m1_subset_1('#skF_1'('#skF_5', B_493), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_493, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1455])).
% 4.12/1.68  tff(c_1682, plain, (![B_494]: (r1_tarski('#skF_1'('#skF_5', B_494), u1_struct_0('#skF_4')) | ~m1_subset_1(B_494, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1674, c_8])).
% 4.12/1.68  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.12/1.68  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_682, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_592, c_50])).
% 4.12/1.68  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_38, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 4.12/1.68  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_683, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_592, c_52])).
% 4.12/1.68  tff(c_593, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_551])).
% 4.12/1.68  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_222])).
% 4.12/1.68  tff(c_757, plain, (![A_460, C_465, D_466, B_461, E_463, H_464, F_462]: (r1_tmap_1(D_466, B_461, E_463, H_464) | ~r1_tmap_1(C_465, B_461, k3_tmap_1(A_460, B_461, D_466, C_465, E_463), H_464) | ~m1_connsp_2(F_462, D_466, H_464) | ~r1_tarski(F_462, u1_struct_0(C_465)) | ~m1_subset_1(H_464, u1_struct_0(C_465)) | ~m1_subset_1(H_464, u1_struct_0(D_466)) | ~m1_subset_1(F_462, k1_zfmisc_1(u1_struct_0(D_466))) | ~m1_pre_topc(C_465, D_466) | ~m1_subset_1(E_463, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_466), u1_struct_0(B_461)))) | ~v1_funct_2(E_463, u1_struct_0(D_466), u1_struct_0(B_461)) | ~v1_funct_1(E_463) | ~m1_pre_topc(D_466, A_460) | v2_struct_0(D_466) | ~m1_pre_topc(C_465, A_460) | v2_struct_0(C_465) | ~l1_pre_topc(B_461) | ~v2_pre_topc(B_461) | v2_struct_0(B_461) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(cnfTransformation, [status(thm)], [f_173])).
% 4.12/1.68  tff(c_759, plain, (![F_462]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_462, '#skF_5', '#skF_8') | ~r1_tarski(F_462, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_462, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_757])).
% 4.12/1.68  tff(c_762, plain, (![F_462]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_462, '#skF_5', '#skF_8') | ~r1_tarski(F_462, u1_struct_0('#skF_4')) | ~m1_subset_1(F_462, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_683, c_592, c_592, c_593, c_592, c_44, c_592, c_44, c_759])).
% 4.12/1.68  tff(c_763, plain, (![F_462]: (~m1_connsp_2(F_462, '#skF_5', '#skF_8') | ~r1_tarski(F_462, u1_struct_0('#skF_4')) | ~m1_subset_1(F_462, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3')))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_76, c_762])).
% 4.12/1.68  tff(c_919, plain, (![F_477]: (~m1_connsp_2(F_477, '#skF_5', '#skF_8') | ~r1_tarski(F_477, u1_struct_0('#skF_4')) | ~m1_subset_1(F_477, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(demodulation, [status(thm), theory('equality')], [c_682, c_763])).
% 4.12/1.68  tff(c_941, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_919])).
% 4.12/1.68  tff(c_1772, plain, (![B_497]: (~m1_connsp_2('#skF_1'('#skF_5', B_497), '#skF_5', '#skF_8') | ~m1_subset_1(B_497, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1682, c_941])).
% 4.12/1.68  tff(c_1776, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1772])).
% 4.12/1.68  tff(c_1779, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_104, c_44, c_592, c_44, c_1776])).
% 4.12/1.68  tff(c_1781, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1779])).
% 4.12/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.12/1.68  
% 4.12/1.68  Inference rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Ref     : 0
% 4.12/1.68  #Sup     : 334
% 4.12/1.68  #Fact    : 0
% 4.12/1.68  #Define  : 0
% 4.12/1.68  #Split   : 6
% 4.12/1.68  #Chain   : 0
% 4.12/1.68  #Close   : 0
% 4.12/1.68  
% 4.12/1.68  Ordering : KBO
% 4.12/1.68  
% 4.12/1.68  Simplification rules
% 4.12/1.68  ----------------------
% 4.12/1.68  #Subsume      : 36
% 4.12/1.68  #Demod        : 565
% 4.12/1.68  #Tautology    : 146
% 4.12/1.68  #SimpNegUnit  : 3
% 4.12/1.68  #BackRed      : 8
% 4.12/1.68  
% 4.12/1.68  #Partial instantiations: 0
% 4.12/1.68  #Strategies tried      : 1
% 4.12/1.68  
% 4.12/1.68  Timing (in seconds)
% 4.12/1.68  ----------------------
% 4.12/1.68  Preprocessing        : 0.38
% 4.12/1.68  Parsing              : 0.19
% 4.12/1.68  CNF conversion       : 0.06
% 4.12/1.68  Main loop            : 0.50
% 4.12/1.68  Inferencing          : 0.16
% 4.12/1.68  Reduction            : 0.18
% 4.12/1.68  Demodulation         : 0.14
% 4.12/1.68  BG Simplification    : 0.02
% 4.12/1.68  Subsumption          : 0.10
% 4.12/1.68  Abstraction          : 0.02
% 4.12/1.68  MUC search           : 0.00
% 4.12/1.68  Cooper               : 0.00
% 4.12/1.68  Total                : 0.93
% 4.12/1.68  Index Insertion      : 0.00
% 4.12/1.68  Index Deletion       : 0.00
% 4.12/1.68  Index Matching       : 0.00
% 4.12/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
