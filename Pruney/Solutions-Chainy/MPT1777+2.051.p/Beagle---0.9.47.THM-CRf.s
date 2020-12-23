%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:39 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 5.15s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 755 expanded)
%              Number of leaves         :   39 ( 280 expanded)
%              Depth                    :   17
%              Number of atoms          :  265 (4010 expanded)
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

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_106,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_tmap_1)).

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

tff(c_28,plain,(
    ! [A_24] :
      ( m1_pre_topc(A_24,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_269,plain,(
    ! [A_438,B_439] :
      ( m1_pre_topc(A_438,g1_pre_topc(u1_struct_0(B_439),u1_pre_topc(B_439)))
      | ~ m1_pre_topc(A_438,B_439)
      | ~ l1_pre_topc(B_439)
      | ~ l1_pre_topc(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_288,plain,(
    ! [A_438] :
      ( m1_pre_topc(A_438,'#skF_5')
      | ~ m1_pre_topc(A_438,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_269])).

tff(c_298,plain,(
    ! [A_438] :
      ( m1_pre_topc(A_438,'#skF_5')
      | ~ m1_pre_topc(A_438,'#skF_4')
      | ~ l1_pre_topc(A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_288])).

tff(c_400,plain,(
    ! [A_445,B_446] :
      ( m1_pre_topc(A_445,B_446)
      | ~ m1_pre_topc(A_445,g1_pre_topc(u1_struct_0(B_446),u1_pre_topc(B_446)))
      | ~ l1_pre_topc(B_446)
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_418,plain,(
    ! [A_445] :
      ( m1_pre_topc(A_445,'#skF_4')
      | ~ m1_pre_topc(A_445,'#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_400])).

tff(c_434,plain,(
    ! [A_447] :
      ( m1_pre_topc(A_447,'#skF_4')
      | ~ m1_pre_topc(A_447,'#skF_5')
      | ~ l1_pre_topc(A_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_418])).

tff(c_453,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_434])).

tff(c_466,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_453])).

tff(c_30,plain,(
    ! [B_27,A_25] :
      ( r1_tarski(u1_struct_0(B_27),u1_struct_0(A_25))
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_142,plain,(
    ! [B_422,A_423] :
      ( r1_tarski(u1_struct_0(B_422),u1_struct_0(A_423))
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_513,plain,(
    ! [B_449,A_450] :
      ( u1_struct_0(B_449) = u1_struct_0(A_450)
      | ~ r1_tarski(u1_struct_0(A_450),u1_struct_0(B_449))
      | ~ m1_pre_topc(B_449,A_450)
      | ~ l1_pre_topc(A_450) ) ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_524,plain,(
    ! [B_451,A_452] :
      ( u1_struct_0(B_451) = u1_struct_0(A_452)
      | ~ m1_pre_topc(A_452,B_451)
      | ~ l1_pre_topc(B_451)
      | ~ m1_pre_topc(B_451,A_452)
      | ~ l1_pre_topc(A_452) ) ),
    inference(resolution,[status(thm)],[c_30,c_513])).

tff(c_526,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_466,c_524])).

tff(c_545,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_101,c_526])).

tff(c_566,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_545])).

tff(c_569,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_298,c_566])).

tff(c_572,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_569])).

tff(c_575,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_572])).

tff(c_579,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_575])).

tff(c_580,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( m1_connsp_2('#skF_1'(A_18,B_19),A_18,B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_736,plain,(
    ! [C_455,A_456,B_457] :
      ( m1_subset_1(C_455,k1_zfmisc_1(u1_struct_0(A_456)))
      | ~ m1_connsp_2(C_455,A_456,B_457)
      | ~ m1_subset_1(B_457,u1_struct_0(A_456))
      | ~ l1_pre_topc(A_456)
      | ~ v2_pre_topc(A_456)
      | v2_struct_0(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1581,plain,(
    ! [A_490,B_491] :
      ( m1_subset_1('#skF_1'(A_490,B_491),k1_zfmisc_1(u1_struct_0(A_490)))
      | ~ m1_subset_1(B_491,u1_struct_0(A_490))
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(resolution,[status(thm)],[c_22,c_736])).

tff(c_1587,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_5',B_491),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_580,c_1581])).

tff(c_1590,plain,(
    ! [B_491] :
      ( m1_subset_1('#skF_1'('#skF_5',B_491),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_104,c_580,c_1587])).

tff(c_1739,plain,(
    ! [B_492] :
      ( m1_subset_1('#skF_1'('#skF_5',B_492),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_492,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1590])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1746,plain,(
    ! [B_493] :
      ( r1_tarski('#skF_1'('#skF_5',B_493),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_493,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1739,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

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

tff(c_678,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_677,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_580,c_50])).

tff(c_581,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_545])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_222])).

tff(c_748,plain,(
    ! [D_464,F_460,C_463,A_458,B_459,E_461,H_462] :
      ( r1_tmap_1(D_464,B_459,E_461,H_462)
      | ~ r1_tmap_1(C_463,B_459,k3_tmap_1(A_458,B_459,D_464,C_463,E_461),H_462)
      | ~ m1_connsp_2(F_460,D_464,H_462)
      | ~ r1_tarski(F_460,u1_struct_0(C_463))
      | ~ m1_subset_1(H_462,u1_struct_0(C_463))
      | ~ m1_subset_1(H_462,u1_struct_0(D_464))
      | ~ m1_subset_1(F_460,k1_zfmisc_1(u1_struct_0(D_464)))
      | ~ m1_pre_topc(C_463,D_464)
      | ~ m1_subset_1(E_461,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_464),u1_struct_0(B_459))))
      | ~ v1_funct_2(E_461,u1_struct_0(D_464),u1_struct_0(B_459))
      | ~ v1_funct_1(E_461)
      | ~ m1_pre_topc(D_464,A_458)
      | v2_struct_0(D_464)
      | ~ m1_pre_topc(C_463,A_458)
      | v2_struct_0(C_463)
      | ~ l1_pre_topc(B_459)
      | ~ v2_pre_topc(B_459)
      | v2_struct_0(B_459)
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458)
      | v2_struct_0(A_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_750,plain,(
    ! [F_460] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_460,'#skF_5','#skF_8')
      | ~ r1_tarski(F_460,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_460,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_40,c_748])).

tff(c_753,plain,(
    ! [F_460] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_460,'#skF_5','#skF_8')
      | ~ r1_tarski(F_460,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_460,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_678,c_580,c_677,c_580,c_581,c_580,c_44,c_580,c_44,c_750])).

tff(c_759,plain,(
    ! [F_465] :
      ( ~ m1_connsp_2(F_465,'#skF_5','#skF_8')
      | ~ r1_tarski(F_465,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_465,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_76,c_753])).

tff(c_764,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_759])).

tff(c_2531,plain,(
    ! [B_510] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_510),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_510,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1746,c_764])).

tff(c_2535,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_2531])).

tff(c_2538,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_104,c_44,c_580,c_44,c_2535])).

tff(c_2540,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_2538])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 17:08:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.89  
% 4.77/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.77/1.89  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.77/1.89  
% 4.77/1.89  %Foreground sorts:
% 4.77/1.89  
% 4.77/1.89  
% 4.77/1.89  %Background operators:
% 4.77/1.89  
% 4.77/1.89  
% 4.77/1.89  %Foreground operators:
% 4.77/1.89  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.77/1.89  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.77/1.89  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.77/1.89  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.77/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.77/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.77/1.89  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.77/1.89  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.77/1.89  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.77/1.89  tff('#skF_7', type, '#skF_7': $i).
% 4.77/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.77/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.77/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.77/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.77/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.77/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.77/1.89  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.77/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.77/1.89  tff('#skF_8', type, '#skF_8': $i).
% 4.77/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.77/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.77/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.77/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.77/1.89  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.77/1.89  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.77/1.89  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.77/1.89  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.77/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.77/1.89  
% 5.15/1.92  tff(f_222, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.15/1.92  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.15/1.92  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.15/1.92  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.15/1.92  tff(f_60, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.15/1.92  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 5.15/1.92  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.15/1.92  tff(f_86, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 5.15/1.92  tff(f_74, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 5.15/1.92  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.15/1.92  tff(f_173, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 5.15/1.92  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_125, plain, (![B_420, A_421]: (v2_pre_topc(B_420) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.15/1.92  tff(c_134, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_125])).
% 5.15/1.92  tff(c_141, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_134])).
% 5.15/1.92  tff(c_88, plain, (![B_412, A_413]: (l1_pre_topc(B_412) | ~m1_pre_topc(B_412, A_413) | ~l1_pre_topc(A_413))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.15/1.92  tff(c_97, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_88])).
% 5.15/1.92  tff(c_104, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 5.15/1.92  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_94, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_88])).
% 5.15/1.92  tff(c_101, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_94])).
% 5.15/1.92  tff(c_28, plain, (![A_24]: (m1_pre_topc(A_24, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 5.15/1.92  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_269, plain, (![A_438, B_439]: (m1_pre_topc(A_438, g1_pre_topc(u1_struct_0(B_439), u1_pre_topc(B_439))) | ~m1_pre_topc(A_438, B_439) | ~l1_pre_topc(B_439) | ~l1_pre_topc(A_438))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.15/1.92  tff(c_288, plain, (![A_438]: (m1_pre_topc(A_438, '#skF_5') | ~m1_pre_topc(A_438, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_438))), inference(superposition, [status(thm), theory('equality')], [c_48, c_269])).
% 5.15/1.92  tff(c_298, plain, (![A_438]: (m1_pre_topc(A_438, '#skF_5') | ~m1_pre_topc(A_438, '#skF_4') | ~l1_pre_topc(A_438))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_288])).
% 5.15/1.92  tff(c_400, plain, (![A_445, B_446]: (m1_pre_topc(A_445, B_446) | ~m1_pre_topc(A_445, g1_pre_topc(u1_struct_0(B_446), u1_pre_topc(B_446))) | ~l1_pre_topc(B_446) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.15/1.92  tff(c_418, plain, (![A_445]: (m1_pre_topc(A_445, '#skF_4') | ~m1_pre_topc(A_445, '#skF_5') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_445))), inference(superposition, [status(thm), theory('equality')], [c_48, c_400])).
% 5.15/1.92  tff(c_434, plain, (![A_447]: (m1_pre_topc(A_447, '#skF_4') | ~m1_pre_topc(A_447, '#skF_5') | ~l1_pre_topc(A_447))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_418])).
% 5.15/1.92  tff(c_453, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_28, c_434])).
% 5.15/1.92  tff(c_466, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_453])).
% 5.15/1.92  tff(c_30, plain, (![B_27, A_25]: (r1_tarski(u1_struct_0(B_27), u1_struct_0(A_25)) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.15/1.92  tff(c_142, plain, (![B_422, A_423]: (r1_tarski(u1_struct_0(B_422), u1_struct_0(A_423)) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_106])).
% 5.15/1.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.15/1.92  tff(c_513, plain, (![B_449, A_450]: (u1_struct_0(B_449)=u1_struct_0(A_450) | ~r1_tarski(u1_struct_0(A_450), u1_struct_0(B_449)) | ~m1_pre_topc(B_449, A_450) | ~l1_pre_topc(A_450))), inference(resolution, [status(thm)], [c_142, c_2])).
% 5.15/1.92  tff(c_524, plain, (![B_451, A_452]: (u1_struct_0(B_451)=u1_struct_0(A_452) | ~m1_pre_topc(A_452, B_451) | ~l1_pre_topc(B_451) | ~m1_pre_topc(B_451, A_452) | ~l1_pre_topc(A_452))), inference(resolution, [status(thm)], [c_30, c_513])).
% 5.15/1.92  tff(c_526, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_466, c_524])).
% 5.15/1.92  tff(c_545, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_101, c_526])).
% 5.15/1.92  tff(c_566, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_545])).
% 5.15/1.92  tff(c_569, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_298, c_566])).
% 5.15/1.92  tff(c_572, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_101, c_569])).
% 5.15/1.92  tff(c_575, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_572])).
% 5.15/1.92  tff(c_579, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_575])).
% 5.15/1.92  tff(c_580, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_545])).
% 5.15/1.92  tff(c_22, plain, (![A_18, B_19]: (m1_connsp_2('#skF_1'(A_18, B_19), A_18, B_19) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_86])).
% 5.15/1.92  tff(c_736, plain, (![C_455, A_456, B_457]: (m1_subset_1(C_455, k1_zfmisc_1(u1_struct_0(A_456))) | ~m1_connsp_2(C_455, A_456, B_457) | ~m1_subset_1(B_457, u1_struct_0(A_456)) | ~l1_pre_topc(A_456) | ~v2_pre_topc(A_456) | v2_struct_0(A_456))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.15/1.92  tff(c_1581, plain, (![A_490, B_491]: (m1_subset_1('#skF_1'(A_490, B_491), k1_zfmisc_1(u1_struct_0(A_490))) | ~m1_subset_1(B_491, u1_struct_0(A_490)) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(resolution, [status(thm)], [c_22, c_736])).
% 5.15/1.92  tff(c_1587, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_5', B_491), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_491, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_580, c_1581])).
% 5.15/1.92  tff(c_1590, plain, (![B_491]: (m1_subset_1('#skF_1'('#skF_5', B_491), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_491, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_141, c_104, c_580, c_1587])).
% 5.15/1.92  tff(c_1739, plain, (![B_492]: (m1_subset_1('#skF_1'('#skF_5', B_492), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_492, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1590])).
% 5.15/1.92  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.15/1.92  tff(c_1746, plain, (![B_493]: (r1_tarski('#skF_1'('#skF_5', B_493), u1_struct_0('#skF_4')) | ~m1_subset_1(B_493, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1739, c_8])).
% 5.15/1.92  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.15/1.92  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_38, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 5.15/1.92  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_678, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_52])).
% 5.15/1.92  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_677, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_580, c_50])).
% 5.15/1.92  tff(c_581, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_545])).
% 5.15/1.92  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_222])).
% 5.15/1.92  tff(c_748, plain, (![D_464, F_460, C_463, A_458, B_459, E_461, H_462]: (r1_tmap_1(D_464, B_459, E_461, H_462) | ~r1_tmap_1(C_463, B_459, k3_tmap_1(A_458, B_459, D_464, C_463, E_461), H_462) | ~m1_connsp_2(F_460, D_464, H_462) | ~r1_tarski(F_460, u1_struct_0(C_463)) | ~m1_subset_1(H_462, u1_struct_0(C_463)) | ~m1_subset_1(H_462, u1_struct_0(D_464)) | ~m1_subset_1(F_460, k1_zfmisc_1(u1_struct_0(D_464))) | ~m1_pre_topc(C_463, D_464) | ~m1_subset_1(E_461, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_464), u1_struct_0(B_459)))) | ~v1_funct_2(E_461, u1_struct_0(D_464), u1_struct_0(B_459)) | ~v1_funct_1(E_461) | ~m1_pre_topc(D_464, A_458) | v2_struct_0(D_464) | ~m1_pre_topc(C_463, A_458) | v2_struct_0(C_463) | ~l1_pre_topc(B_459) | ~v2_pre_topc(B_459) | v2_struct_0(B_459) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458) | v2_struct_0(A_458))), inference(cnfTransformation, [status(thm)], [f_173])).
% 5.15/1.92  tff(c_750, plain, (![F_460]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_460, '#skF_5', '#skF_8') | ~r1_tarski(F_460, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_460, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_748])).
% 5.15/1.92  tff(c_753, plain, (![F_460]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_460, '#skF_5', '#skF_8') | ~r1_tarski(F_460, u1_struct_0('#skF_4')) | ~m1_subset_1(F_460, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_678, c_580, c_677, c_580, c_581, c_580, c_44, c_580, c_44, c_750])).
% 5.15/1.92  tff(c_759, plain, (![F_465]: (~m1_connsp_2(F_465, '#skF_5', '#skF_8') | ~r1_tarski(F_465, u1_struct_0('#skF_4')) | ~m1_subset_1(F_465, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_76, c_753])).
% 5.15/1.92  tff(c_764, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_759])).
% 5.15/1.92  tff(c_2531, plain, (![B_510]: (~m1_connsp_2('#skF_1'('#skF_5', B_510), '#skF_5', '#skF_8') | ~m1_subset_1(B_510, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1746, c_764])).
% 5.15/1.92  tff(c_2535, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_22, c_2531])).
% 5.15/1.92  tff(c_2538, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_104, c_44, c_580, c_44, c_2535])).
% 5.15/1.92  tff(c_2540, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_2538])).
% 5.15/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.15/1.92  
% 5.15/1.92  Inference rules
% 5.15/1.92  ----------------------
% 5.15/1.92  #Ref     : 0
% 5.15/1.92  #Sup     : 484
% 5.15/1.92  #Fact    : 0
% 5.15/1.92  #Define  : 0
% 5.15/1.92  #Split   : 4
% 5.15/1.92  #Chain   : 0
% 5.15/1.92  #Close   : 0
% 5.15/1.92  
% 5.15/1.92  Ordering : KBO
% 5.15/1.92  
% 5.15/1.92  Simplification rules
% 5.15/1.92  ----------------------
% 5.15/1.92  #Subsume      : 56
% 5.15/1.92  #Demod        : 845
% 5.15/1.92  #Tautology    : 196
% 5.15/1.92  #SimpNegUnit  : 3
% 5.15/1.92  #BackRed      : 8
% 5.15/1.92  
% 5.15/1.92  #Partial instantiations: 0
% 5.15/1.92  #Strategies tried      : 1
% 5.15/1.92  
% 5.15/1.92  Timing (in seconds)
% 5.15/1.92  ----------------------
% 5.15/1.92  Preprocessing        : 0.40
% 5.15/1.92  Parsing              : 0.21
% 5.15/1.92  CNF conversion       : 0.06
% 5.15/1.92  Main loop            : 0.68
% 5.15/1.92  Inferencing          : 0.21
% 5.15/1.92  Reduction            : 0.27
% 5.15/1.92  Demodulation         : 0.20
% 5.15/1.92  BG Simplification    : 0.03
% 5.15/1.92  Subsumption          : 0.14
% 5.15/1.92  Abstraction          : 0.03
% 5.15/1.92  MUC search           : 0.00
% 5.15/1.92  Cooper               : 0.00
% 5.15/1.92  Total                : 1.12
% 5.15/1.92  Index Insertion      : 0.00
% 5.15/1.92  Index Deletion       : 0.00
% 5.15/1.92  Index Matching       : 0.00
% 5.15/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
