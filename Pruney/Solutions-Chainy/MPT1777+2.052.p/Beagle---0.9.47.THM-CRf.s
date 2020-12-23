%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:39 EST 2020

% Result     : Theorem 3.65s
% Output     : CNFRefutation 3.65s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 820 expanded)
%              Number of leaves         :   39 ( 301 expanded)
%              Depth                    :   17
%              Number of atoms          :  268 (4120 expanded)
%              Number of equality atoms :   12 ( 365 expanded)
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

tff(f_104,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_100,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_81,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_tmap_1)).

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
    ! [B_420,A_421] :
      ( v2_pre_topc(B_420)
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421)
      | ~ v2_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_123])).

tff(c_136,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_129])).

tff(c_96,plain,(
    ! [B_416,A_417] :
      ( l1_pre_topc(B_416)
      | ~ m1_pre_topc(B_416,A_417)
      | ~ l1_pre_topc(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_54,c_96])).

tff(c_109,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_102])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_105,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_96])).

tff(c_112,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_105])).

tff(c_28,plain,(
    ! [A_27] :
      ( m1_pre_topc(A_27,A_27)
      | ~ l1_pre_topc(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_254,plain,(
    ! [A_435,B_436] :
      ( m1_pre_topc(A_435,g1_pre_topc(u1_struct_0(B_436),u1_pre_topc(B_436)))
      | ~ m1_pre_topc(A_435,B_436)
      | ~ l1_pre_topc(B_436)
      | ~ l1_pre_topc(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_272,plain,(
    ! [A_435] :
      ( m1_pre_topc(A_435,'#skF_5')
      | ~ m1_pre_topc(A_435,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_435) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_254])).

tff(c_281,plain,(
    ! [A_435] :
      ( m1_pre_topc(A_435,'#skF_5')
      | ~ m1_pre_topc(A_435,'#skF_4')
      | ~ l1_pre_topc(A_435) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_272])).

tff(c_149,plain,(
    ! [B_426,A_427] :
      ( m1_pre_topc(B_426,A_427)
      | ~ m1_pre_topc(B_426,g1_pre_topc(u1_struct_0(A_427),u1_pre_topc(A_427)))
      | ~ l1_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_152,plain,(
    ! [B_426] :
      ( m1_pre_topc(B_426,'#skF_4')
      | ~ m1_pre_topc(B_426,'#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_149])).

tff(c_160,plain,(
    ! [B_428] :
      ( m1_pre_topc(B_428,'#skF_4')
      | ~ m1_pre_topc(B_428,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_152])).

tff(c_164,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_160])).

tff(c_167,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_164])).

tff(c_140,plain,(
    ! [B_422,A_423] :
      ( m1_subset_1(u1_struct_0(B_422),k1_zfmisc_1(u1_struct_0(A_423)))
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_144,plain,(
    ! [B_422,A_423] :
      ( r1_tarski(u1_struct_0(B_422),u1_struct_0(A_423))
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_145,plain,(
    ! [B_424,A_425] :
      ( r1_tarski(u1_struct_0(B_424),u1_struct_0(A_425))
      | ~ m1_pre_topc(B_424,A_425)
      | ~ l1_pre_topc(A_425) ) ),
    inference(resolution,[status(thm)],[c_140,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_339,plain,(
    ! [B_441,A_442] :
      ( u1_struct_0(B_441) = u1_struct_0(A_442)
      | ~ r1_tarski(u1_struct_0(A_442),u1_struct_0(B_441))
      | ~ m1_pre_topc(B_441,A_442)
      | ~ l1_pre_topc(A_442) ) ),
    inference(resolution,[status(thm)],[c_145,c_2])).

tff(c_407,plain,(
    ! [B_446,A_447] :
      ( u1_struct_0(B_446) = u1_struct_0(A_447)
      | ~ m1_pre_topc(A_447,B_446)
      | ~ l1_pre_topc(B_446)
      | ~ m1_pre_topc(B_446,A_447)
      | ~ l1_pre_topc(A_447) ) ),
    inference(resolution,[status(thm)],[c_144,c_339])).

tff(c_417,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_167,c_407])).

tff(c_436,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_112,c_417])).

tff(c_445,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_436])).

tff(c_448,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_281,c_445])).

tff(c_451,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_448])).

tff(c_458,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_451])).

tff(c_462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_458])).

tff(c_463,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( m1_connsp_2('#skF_1'(A_21,B_22),A_21,B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_582,plain,(
    ! [C_451,A_452,B_453] :
      ( m1_subset_1(C_451,k1_zfmisc_1(u1_struct_0(A_452)))
      | ~ m1_connsp_2(C_451,A_452,B_453)
      | ~ m1_subset_1(B_453,u1_struct_0(A_452))
      | ~ l1_pre_topc(A_452)
      | ~ v2_pre_topc(A_452)
      | v2_struct_0(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1172,plain,(
    ! [A_487,B_488] :
      ( m1_subset_1('#skF_1'(A_487,B_488),k1_zfmisc_1(u1_struct_0(A_487)))
      | ~ m1_subset_1(B_488,u1_struct_0(A_487))
      | ~ l1_pre_topc(A_487)
      | ~ v2_pre_topc(A_487)
      | v2_struct_0(A_487) ) ),
    inference(resolution,[status(thm)],[c_24,c_582])).

tff(c_1178,plain,(
    ! [B_488] :
      ( m1_subset_1('#skF_1'('#skF_5',B_488),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_488,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_1172])).

tff(c_1181,plain,(
    ! [B_488] :
      ( m1_subset_1('#skF_1'('#skF_5',B_488),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_488,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_463,c_1178])).

tff(c_1183,plain,(
    ! [B_489] :
      ( m1_subset_1('#skF_1'('#skF_5',B_489),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_489,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1181])).

tff(c_1188,plain,(
    ! [B_490] :
      ( r1_tarski('#skF_1'('#skF_5',B_490),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_490,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1183,c_8])).

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

tff(c_536,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_535,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_48])).

tff(c_464,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_436])).

tff(c_38,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_683,plain,(
    ! [D_463,E_460,F_459,H_461,B_458,A_457,C_462] :
      ( r1_tmap_1(D_463,B_458,E_460,H_461)
      | ~ r1_tmap_1(C_462,B_458,k3_tmap_1(A_457,B_458,D_463,C_462,E_460),H_461)
      | ~ m1_connsp_2(F_459,D_463,H_461)
      | ~ r1_tarski(F_459,u1_struct_0(C_462))
      | ~ m1_subset_1(H_461,u1_struct_0(C_462))
      | ~ m1_subset_1(H_461,u1_struct_0(D_463))
      | ~ m1_subset_1(F_459,k1_zfmisc_1(u1_struct_0(D_463)))
      | ~ m1_pre_topc(C_462,D_463)
      | ~ m1_subset_1(E_460,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_463),u1_struct_0(B_458))))
      | ~ v1_funct_2(E_460,u1_struct_0(D_463),u1_struct_0(B_458))
      | ~ v1_funct_1(E_460)
      | ~ m1_pre_topc(D_463,A_457)
      | v2_struct_0(D_463)
      | ~ m1_pre_topc(C_462,A_457)
      | v2_struct_0(C_462)
      | ~ l1_pre_topc(B_458)
      | ~ v2_pre_topc(B_458)
      | v2_struct_0(B_458)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_685,plain,(
    ! [F_459] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_459,'#skF_5','#skF_8')
      | ~ r1_tarski(F_459,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_459,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_38,c_683])).

tff(c_688,plain,(
    ! [F_459] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_459,'#skF_5','#skF_8')
      | ~ r1_tarski(F_459,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_459,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_536,c_463,c_535,c_463,c_464,c_463,c_42,c_463,c_42,c_685])).

tff(c_771,plain,(
    ! [F_467] :
      ( ~ m1_connsp_2(F_467,'#skF_5','#skF_8')
      | ~ r1_tarski(F_467,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_467,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_74,c_688])).

tff(c_793,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_771])).

tff(c_1196,plain,(
    ! [B_491] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_491),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_491,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1188,c_793])).

tff(c_1200,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1196])).

tff(c_1203,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_42,c_463,c_42,c_1200])).

tff(c_1205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1203])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n015.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 20:35:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.65/1.55  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.56  
% 3.65/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.56  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.65/1.56  
% 3.65/1.56  %Foreground sorts:
% 3.65/1.56  
% 3.65/1.56  
% 3.65/1.56  %Background operators:
% 3.65/1.56  
% 3.65/1.56  
% 3.65/1.56  %Foreground operators:
% 3.65/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.65/1.56  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.65/1.56  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.65/1.56  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.65/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.65/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.65/1.56  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.65/1.56  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.65/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.65/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.65/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.65/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.65/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.65/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.65/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.65/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.65/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.65/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.65/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.65/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.65/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.65/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.65/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.65/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.65/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.65/1.56  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.65/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.65/1.56  
% 3.65/1.59  tff(f_220, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.65/1.59  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.65/1.59  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.65/1.59  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.65/1.59  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.65/1.59  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.65/1.59  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.65/1.59  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.65/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.65/1.59  tff(f_93, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.65/1.59  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.65/1.59  tff(f_171, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.65/1.59  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_123, plain, (![B_420, A_421]: (v2_pre_topc(B_420) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.65/1.59  tff(c_129, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_123])).
% 3.65/1.59  tff(c_136, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_129])).
% 3.65/1.59  tff(c_96, plain, (![B_416, A_417]: (l1_pre_topc(B_416) | ~m1_pre_topc(B_416, A_417) | ~l1_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.65/1.59  tff(c_102, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_96])).
% 3.65/1.59  tff(c_109, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102])).
% 3.65/1.59  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_105, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_96])).
% 3.65/1.59  tff(c_112, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_105])).
% 3.65/1.59  tff(c_28, plain, (![A_27]: (m1_pre_topc(A_27, A_27) | ~l1_pre_topc(A_27))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.65/1.59  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_254, plain, (![A_435, B_436]: (m1_pre_topc(A_435, g1_pre_topc(u1_struct_0(B_436), u1_pre_topc(B_436))) | ~m1_pre_topc(A_435, B_436) | ~l1_pre_topc(B_436) | ~l1_pre_topc(A_435))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.65/1.59  tff(c_272, plain, (![A_435]: (m1_pre_topc(A_435, '#skF_5') | ~m1_pre_topc(A_435, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_435))), inference(superposition, [status(thm), theory('equality')], [c_46, c_254])).
% 3.65/1.59  tff(c_281, plain, (![A_435]: (m1_pre_topc(A_435, '#skF_5') | ~m1_pre_topc(A_435, '#skF_4') | ~l1_pre_topc(A_435))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_272])).
% 3.65/1.59  tff(c_149, plain, (![B_426, A_427]: (m1_pre_topc(B_426, A_427) | ~m1_pre_topc(B_426, g1_pre_topc(u1_struct_0(A_427), u1_pre_topc(A_427))) | ~l1_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.65/1.59  tff(c_152, plain, (![B_426]: (m1_pre_topc(B_426, '#skF_4') | ~m1_pre_topc(B_426, '#skF_5') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_149])).
% 3.65/1.59  tff(c_160, plain, (![B_428]: (m1_pre_topc(B_428, '#skF_4') | ~m1_pre_topc(B_428, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_152])).
% 3.65/1.59  tff(c_164, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_28, c_160])).
% 3.65/1.59  tff(c_167, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_164])).
% 3.65/1.59  tff(c_140, plain, (![B_422, A_423]: (m1_subset_1(u1_struct_0(B_422), k1_zfmisc_1(u1_struct_0(A_423))) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.65/1.59  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.59  tff(c_144, plain, (![B_422, A_423]: (r1_tarski(u1_struct_0(B_422), u1_struct_0(A_423)) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423))), inference(resolution, [status(thm)], [c_140, c_8])).
% 3.65/1.59  tff(c_145, plain, (![B_424, A_425]: (r1_tarski(u1_struct_0(B_424), u1_struct_0(A_425)) | ~m1_pre_topc(B_424, A_425) | ~l1_pre_topc(A_425))), inference(resolution, [status(thm)], [c_140, c_8])).
% 3.65/1.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.65/1.59  tff(c_339, plain, (![B_441, A_442]: (u1_struct_0(B_441)=u1_struct_0(A_442) | ~r1_tarski(u1_struct_0(A_442), u1_struct_0(B_441)) | ~m1_pre_topc(B_441, A_442) | ~l1_pre_topc(A_442))), inference(resolution, [status(thm)], [c_145, c_2])).
% 3.65/1.59  tff(c_407, plain, (![B_446, A_447]: (u1_struct_0(B_446)=u1_struct_0(A_447) | ~m1_pre_topc(A_447, B_446) | ~l1_pre_topc(B_446) | ~m1_pre_topc(B_446, A_447) | ~l1_pre_topc(A_447))), inference(resolution, [status(thm)], [c_144, c_339])).
% 3.65/1.59  tff(c_417, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_167, c_407])).
% 3.65/1.59  tff(c_436, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_112, c_417])).
% 3.65/1.59  tff(c_445, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_436])).
% 3.65/1.59  tff(c_448, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_281, c_445])).
% 3.65/1.59  tff(c_451, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_448])).
% 3.65/1.59  tff(c_458, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_451])).
% 3.65/1.59  tff(c_462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_458])).
% 3.65/1.59  tff(c_463, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_436])).
% 3.65/1.59  tff(c_24, plain, (![A_21, B_22]: (m1_connsp_2('#skF_1'(A_21, B_22), A_21, B_22) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.65/1.59  tff(c_582, plain, (![C_451, A_452, B_453]: (m1_subset_1(C_451, k1_zfmisc_1(u1_struct_0(A_452))) | ~m1_connsp_2(C_451, A_452, B_453) | ~m1_subset_1(B_453, u1_struct_0(A_452)) | ~l1_pre_topc(A_452) | ~v2_pre_topc(A_452) | v2_struct_0(A_452))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.65/1.59  tff(c_1172, plain, (![A_487, B_488]: (m1_subset_1('#skF_1'(A_487, B_488), k1_zfmisc_1(u1_struct_0(A_487))) | ~m1_subset_1(B_488, u1_struct_0(A_487)) | ~l1_pre_topc(A_487) | ~v2_pre_topc(A_487) | v2_struct_0(A_487))), inference(resolution, [status(thm)], [c_24, c_582])).
% 3.65/1.59  tff(c_1178, plain, (![B_488]: (m1_subset_1('#skF_1'('#skF_5', B_488), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_488, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_463, c_1172])).
% 3.65/1.59  tff(c_1181, plain, (![B_488]: (m1_subset_1('#skF_1'('#skF_5', B_488), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_488, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_463, c_1178])).
% 3.65/1.59  tff(c_1183, plain, (![B_489]: (m1_subset_1('#skF_1'('#skF_5', B_489), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_489, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1181])).
% 3.65/1.59  tff(c_1188, plain, (![B_490]: (r1_tarski('#skF_1'('#skF_5', B_490), u1_struct_0('#skF_4')) | ~m1_subset_1(B_490, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1183, c_8])).
% 3.65/1.59  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.65/1.59  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_40, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_36, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_74, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.65/1.59  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_50, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_536, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_50])).
% 3.65/1.59  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_535, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_463, c_48])).
% 3.65/1.59  tff(c_464, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_436])).
% 3.65/1.59  tff(c_38, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.65/1.59  tff(c_683, plain, (![D_463, E_460, F_459, H_461, B_458, A_457, C_462]: (r1_tmap_1(D_463, B_458, E_460, H_461) | ~r1_tmap_1(C_462, B_458, k3_tmap_1(A_457, B_458, D_463, C_462, E_460), H_461) | ~m1_connsp_2(F_459, D_463, H_461) | ~r1_tarski(F_459, u1_struct_0(C_462)) | ~m1_subset_1(H_461, u1_struct_0(C_462)) | ~m1_subset_1(H_461, u1_struct_0(D_463)) | ~m1_subset_1(F_459, k1_zfmisc_1(u1_struct_0(D_463))) | ~m1_pre_topc(C_462, D_463) | ~m1_subset_1(E_460, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_463), u1_struct_0(B_458)))) | ~v1_funct_2(E_460, u1_struct_0(D_463), u1_struct_0(B_458)) | ~v1_funct_1(E_460) | ~m1_pre_topc(D_463, A_457) | v2_struct_0(D_463) | ~m1_pre_topc(C_462, A_457) | v2_struct_0(C_462) | ~l1_pre_topc(B_458) | ~v2_pre_topc(B_458) | v2_struct_0(B_458) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.65/1.59  tff(c_685, plain, (![F_459]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_459, '#skF_5', '#skF_8') | ~r1_tarski(F_459, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_459, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_683])).
% 3.65/1.59  tff(c_688, plain, (![F_459]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_459, '#skF_5', '#skF_8') | ~r1_tarski(F_459, u1_struct_0('#skF_4')) | ~m1_subset_1(F_459, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_536, c_463, c_535, c_463, c_464, c_463, c_42, c_463, c_42, c_685])).
% 3.65/1.59  tff(c_771, plain, (![F_467]: (~m1_connsp_2(F_467, '#skF_5', '#skF_8') | ~r1_tarski(F_467, u1_struct_0('#skF_4')) | ~m1_subset_1(F_467, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_74, c_688])).
% 3.65/1.59  tff(c_793, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_771])).
% 3.65/1.59  tff(c_1196, plain, (![B_491]: (~m1_connsp_2('#skF_1'('#skF_5', B_491), '#skF_5', '#skF_8') | ~m1_subset_1(B_491, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1188, c_793])).
% 3.65/1.59  tff(c_1200, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1196])).
% 3.65/1.59  tff(c_1203, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_42, c_463, c_42, c_1200])).
% 3.65/1.59  tff(c_1205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1203])).
% 3.65/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.65/1.59  
% 3.65/1.59  Inference rules
% 3.65/1.59  ----------------------
% 3.65/1.59  #Ref     : 0
% 3.65/1.59  #Sup     : 214
% 3.65/1.59  #Fact    : 0
% 3.65/1.59  #Define  : 0
% 3.65/1.59  #Split   : 7
% 3.65/1.59  #Chain   : 0
% 3.65/1.59  #Close   : 0
% 3.65/1.59  
% 3.65/1.59  Ordering : KBO
% 3.65/1.59  
% 3.65/1.59  Simplification rules
% 3.65/1.59  ----------------------
% 3.65/1.59  #Subsume      : 49
% 3.65/1.59  #Demod        : 320
% 3.65/1.59  #Tautology    : 81
% 3.65/1.59  #SimpNegUnit  : 3
% 3.65/1.59  #BackRed      : 5
% 3.65/1.59  
% 3.65/1.59  #Partial instantiations: 0
% 3.65/1.59  #Strategies tried      : 1
% 3.65/1.59  
% 3.65/1.59  Timing (in seconds)
% 3.65/1.59  ----------------------
% 3.65/1.59  Preprocessing        : 0.39
% 3.65/1.59  Parsing              : 0.20
% 3.65/1.59  CNF conversion       : 0.06
% 3.65/1.59  Main loop            : 0.44
% 3.65/1.59  Inferencing          : 0.15
% 3.65/1.59  Reduction            : 0.15
% 3.65/1.59  Demodulation         : 0.11
% 3.65/1.59  BG Simplification    : 0.02
% 3.65/1.59  Subsumption          : 0.09
% 3.65/1.59  Abstraction          : 0.02
% 3.65/1.59  MUC search           : 0.00
% 3.65/1.59  Cooper               : 0.00
% 3.65/1.59  Total                : 0.87
% 3.65/1.59  Index Insertion      : 0.00
% 3.65/1.59  Index Deletion       : 0.00
% 3.65/1.59  Index Matching       : 0.00
% 3.65/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
