%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:40 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 754 expanded)
%              Number of leaves         :   39 ( 279 expanded)
%              Depth                    :   17
%              Number of atoms          :  265 (3966 expanded)
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

tff(f_97,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_67,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_104,axiom,(
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

tff(f_93,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_81,axiom,(
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

tff(c_26,plain,(
    ! [A_24] :
      ( m1_pre_topc(A_24,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_249,plain,(
    ! [A_433,B_434] :
      ( m1_pre_topc(A_433,g1_pre_topc(u1_struct_0(B_434),u1_pre_topc(B_434)))
      | ~ m1_pre_topc(A_433,B_434)
      | ~ l1_pre_topc(B_434)
      | ~ l1_pre_topc(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_267,plain,(
    ! [A_433] :
      ( m1_pre_topc(A_433,'#skF_5')
      | ~ m1_pre_topc(A_433,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_433) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_249])).

tff(c_276,plain,(
    ! [A_433] :
      ( m1_pre_topc(A_433,'#skF_5')
      | ~ m1_pre_topc(A_433,'#skF_4')
      | ~ l1_pre_topc(A_433) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_267])).

tff(c_144,plain,(
    ! [B_424,A_425] :
      ( m1_pre_topc(B_424,A_425)
      | ~ m1_pre_topc(B_424,g1_pre_topc(u1_struct_0(A_425),u1_pre_topc(A_425)))
      | ~ l1_pre_topc(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_147,plain,(
    ! [B_424] :
      ( m1_pre_topc(B_424,'#skF_4')
      | ~ m1_pre_topc(B_424,'#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_144])).

tff(c_155,plain,(
    ! [B_426] :
      ( m1_pre_topc(B_426,'#skF_4')
      | ~ m1_pre_topc(B_426,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_147])).

tff(c_159,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_26,c_155])).

tff(c_162,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_159])).

tff(c_28,plain,(
    ! [B_27,A_25] :
      ( r1_tarski(u1_struct_0(B_27),u1_struct_0(A_25))
      | ~ m1_pre_topc(B_27,A_25)
      | ~ l1_pre_topc(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_140,plain,(
    ! [B_422,A_423] :
      ( r1_tarski(u1_struct_0(B_422),u1_struct_0(A_423))
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_334,plain,(
    ! [B_439,A_440] :
      ( u1_struct_0(B_439) = u1_struct_0(A_440)
      | ~ r1_tarski(u1_struct_0(A_440),u1_struct_0(B_439))
      | ~ m1_pre_topc(B_439,A_440)
      | ~ l1_pre_topc(A_440) ) ),
    inference(resolution,[status(thm)],[c_140,c_2])).

tff(c_345,plain,(
    ! [B_441,A_442] :
      ( u1_struct_0(B_441) = u1_struct_0(A_442)
      | ~ m1_pre_topc(A_442,B_441)
      | ~ l1_pre_topc(B_441)
      | ~ m1_pre_topc(B_441,A_442)
      | ~ l1_pre_topc(A_442) ) ),
    inference(resolution,[status(thm)],[c_28,c_334])).

tff(c_355,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_162,c_345])).

tff(c_374,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_112,c_355])).

tff(c_390,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_374])).

tff(c_393,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_276,c_390])).

tff(c_396,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_393])).

tff(c_399,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_396])).

tff(c_403,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_399])).

tff(c_404,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( m1_connsp_2('#skF_1'(A_21,B_22),A_21,B_22)
      | ~ m1_subset_1(B_22,u1_struct_0(A_21))
      | ~ l1_pre_topc(A_21)
      | ~ v2_pre_topc(A_21)
      | v2_struct_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_430,plain,(
    ! [C_443,A_444,B_445] :
      ( m1_subset_1(C_443,k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ m1_connsp_2(C_443,A_444,B_445)
      | ~ m1_subset_1(B_445,u1_struct_0(A_444))
      | ~ l1_pre_topc(A_444)
      | ~ v2_pre_topc(A_444)
      | v2_struct_0(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1061,plain,(
    ! [A_480,B_481] :
      ( m1_subset_1('#skF_1'(A_480,B_481),k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ m1_subset_1(B_481,u1_struct_0(A_480))
      | ~ l1_pre_topc(A_480)
      | ~ v2_pre_topc(A_480)
      | v2_struct_0(A_480) ) ),
    inference(resolution,[status(thm)],[c_24,c_430])).

tff(c_1067,plain,(
    ! [B_481] :
      ( m1_subset_1('#skF_1'('#skF_5',B_481),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_481,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_1061])).

tff(c_1070,plain,(
    ! [B_481] :
      ( m1_subset_1('#skF_1'('#skF_5',B_481),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_481,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_404,c_1067])).

tff(c_1072,plain,(
    ! [B_482] :
      ( m1_subset_1('#skF_1'('#skF_5',B_482),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_482,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1070])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1077,plain,(
    ! [B_483] :
      ( r1_tarski('#skF_1'('#skF_5',B_483),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_483,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1072,c_8])).

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

tff(c_464,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_50])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_463,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_404,c_48])).

tff(c_405,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_374])).

tff(c_38,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_220])).

tff(c_802,plain,(
    ! [B_464,D_469,C_468,H_467,E_466,F_465,A_463] :
      ( r1_tmap_1(D_469,B_464,E_466,H_467)
      | ~ r1_tmap_1(C_468,B_464,k3_tmap_1(A_463,B_464,D_469,C_468,E_466),H_467)
      | ~ m1_connsp_2(F_465,D_469,H_467)
      | ~ r1_tarski(F_465,u1_struct_0(C_468))
      | ~ m1_subset_1(H_467,u1_struct_0(C_468))
      | ~ m1_subset_1(H_467,u1_struct_0(D_469))
      | ~ m1_subset_1(F_465,k1_zfmisc_1(u1_struct_0(D_469)))
      | ~ m1_pre_topc(C_468,D_469)
      | ~ m1_subset_1(E_466,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_469),u1_struct_0(B_464))))
      | ~ v1_funct_2(E_466,u1_struct_0(D_469),u1_struct_0(B_464))
      | ~ v1_funct_1(E_466)
      | ~ m1_pre_topc(D_469,A_463)
      | v2_struct_0(D_469)
      | ~ m1_pre_topc(C_468,A_463)
      | v2_struct_0(C_468)
      | ~ l1_pre_topc(B_464)
      | ~ v2_pre_topc(B_464)
      | v2_struct_0(B_464)
      | ~ l1_pre_topc(A_463)
      | ~ v2_pre_topc(A_463)
      | v2_struct_0(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_804,plain,(
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
    inference(resolution,[status(thm)],[c_38,c_802])).

tff(c_807,plain,(
    ! [F_465] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_465,'#skF_5','#skF_8')
      | ~ r1_tarski(F_465,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_465,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_464,c_404,c_463,c_404,c_405,c_404,c_42,c_404,c_42,c_804])).

tff(c_809,plain,(
    ! [F_470] :
      ( ~ m1_connsp_2(F_470,'#skF_5','#skF_8')
      | ~ r1_tarski(F_470,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_470,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_74,c_807])).

tff(c_814,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_809])).

tff(c_1085,plain,(
    ! [B_484] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_484),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_484,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1077,c_814])).

tff(c_1089,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_1085])).

tff(c_1092,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_42,c_404,c_42,c_1089])).

tff(c_1094,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_1092])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:23:27 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.56  
% 3.80/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.57  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.80/1.57  
% 3.80/1.57  %Foreground sorts:
% 3.80/1.57  
% 3.80/1.57  
% 3.80/1.57  %Background operators:
% 3.80/1.57  
% 3.80/1.57  
% 3.80/1.57  %Foreground operators:
% 3.80/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.80/1.57  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.80/1.57  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.80/1.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.80/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.57  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.80/1.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.80/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.80/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.80/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.57  tff('#skF_8', type, '#skF_8': $i).
% 3.80/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.80/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.80/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/1.57  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.80/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.57  
% 3.80/1.59  tff(f_220, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.80/1.59  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.80/1.59  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.80/1.59  tff(f_97, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.80/1.59  tff(f_67, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.80/1.59  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.80/1.59  tff(f_104, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.80/1.59  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.80/1.59  tff(f_93, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 3.80/1.59  tff(f_81, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 3.80/1.59  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.80/1.59  tff(f_171, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 3.80/1.59  tff(c_56, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_70, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_68, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_54, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_123, plain, (![B_420, A_421]: (v2_pre_topc(B_420) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421) | ~v2_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.80/1.59  tff(c_129, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_123])).
% 3.80/1.59  tff(c_136, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_129])).
% 3.80/1.59  tff(c_96, plain, (![B_416, A_417]: (l1_pre_topc(B_416) | ~m1_pre_topc(B_416, A_417) | ~l1_pre_topc(A_417))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.80/1.59  tff(c_102, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_54, c_96])).
% 3.80/1.59  tff(c_109, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_102])).
% 3.80/1.59  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_105, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_96])).
% 3.80/1.59  tff(c_112, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_105])).
% 3.80/1.59  tff(c_26, plain, (![A_24]: (m1_pre_topc(A_24, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_97])).
% 3.80/1.59  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_249, plain, (![A_433, B_434]: (m1_pre_topc(A_433, g1_pre_topc(u1_struct_0(B_434), u1_pre_topc(B_434))) | ~m1_pre_topc(A_433, B_434) | ~l1_pre_topc(B_434) | ~l1_pre_topc(A_433))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.80/1.59  tff(c_267, plain, (![A_433]: (m1_pre_topc(A_433, '#skF_5') | ~m1_pre_topc(A_433, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_433))), inference(superposition, [status(thm), theory('equality')], [c_46, c_249])).
% 3.80/1.59  tff(c_276, plain, (![A_433]: (m1_pre_topc(A_433, '#skF_5') | ~m1_pre_topc(A_433, '#skF_4') | ~l1_pre_topc(A_433))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_267])).
% 3.80/1.59  tff(c_144, plain, (![B_424, A_425]: (m1_pre_topc(B_424, A_425) | ~m1_pre_topc(B_424, g1_pre_topc(u1_struct_0(A_425), u1_pre_topc(A_425))) | ~l1_pre_topc(A_425))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.59  tff(c_147, plain, (![B_424]: (m1_pre_topc(B_424, '#skF_4') | ~m1_pre_topc(B_424, '#skF_5') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_46, c_144])).
% 3.80/1.59  tff(c_155, plain, (![B_426]: (m1_pre_topc(B_426, '#skF_4') | ~m1_pre_topc(B_426, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_147])).
% 3.80/1.59  tff(c_159, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_26, c_155])).
% 3.80/1.59  tff(c_162, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_159])).
% 3.80/1.59  tff(c_28, plain, (![B_27, A_25]: (r1_tarski(u1_struct_0(B_27), u1_struct_0(A_25)) | ~m1_pre_topc(B_27, A_25) | ~l1_pre_topc(A_25))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.80/1.59  tff(c_140, plain, (![B_422, A_423]: (r1_tarski(u1_struct_0(B_422), u1_struct_0(A_423)) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.80/1.59  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.80/1.59  tff(c_334, plain, (![B_439, A_440]: (u1_struct_0(B_439)=u1_struct_0(A_440) | ~r1_tarski(u1_struct_0(A_440), u1_struct_0(B_439)) | ~m1_pre_topc(B_439, A_440) | ~l1_pre_topc(A_440))), inference(resolution, [status(thm)], [c_140, c_2])).
% 3.80/1.59  tff(c_345, plain, (![B_441, A_442]: (u1_struct_0(B_441)=u1_struct_0(A_442) | ~m1_pre_topc(A_442, B_441) | ~l1_pre_topc(B_441) | ~m1_pre_topc(B_441, A_442) | ~l1_pre_topc(A_442))), inference(resolution, [status(thm)], [c_28, c_334])).
% 3.80/1.59  tff(c_355, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_162, c_345])).
% 3.80/1.59  tff(c_374, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_112, c_355])).
% 3.80/1.59  tff(c_390, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_374])).
% 3.80/1.59  tff(c_393, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_276, c_390])).
% 3.80/1.59  tff(c_396, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_393])).
% 3.80/1.59  tff(c_399, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_396])).
% 3.80/1.59  tff(c_403, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_399])).
% 3.80/1.59  tff(c_404, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_374])).
% 3.80/1.59  tff(c_24, plain, (![A_21, B_22]: (m1_connsp_2('#skF_1'(A_21, B_22), A_21, B_22) | ~m1_subset_1(B_22, u1_struct_0(A_21)) | ~l1_pre_topc(A_21) | ~v2_pre_topc(A_21) | v2_struct_0(A_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.80/1.59  tff(c_430, plain, (![C_443, A_444, B_445]: (m1_subset_1(C_443, k1_zfmisc_1(u1_struct_0(A_444))) | ~m1_connsp_2(C_443, A_444, B_445) | ~m1_subset_1(B_445, u1_struct_0(A_444)) | ~l1_pre_topc(A_444) | ~v2_pre_topc(A_444) | v2_struct_0(A_444))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.80/1.59  tff(c_1061, plain, (![A_480, B_481]: (m1_subset_1('#skF_1'(A_480, B_481), k1_zfmisc_1(u1_struct_0(A_480))) | ~m1_subset_1(B_481, u1_struct_0(A_480)) | ~l1_pre_topc(A_480) | ~v2_pre_topc(A_480) | v2_struct_0(A_480))), inference(resolution, [status(thm)], [c_24, c_430])).
% 3.80/1.59  tff(c_1067, plain, (![B_481]: (m1_subset_1('#skF_1'('#skF_5', B_481), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_481, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_404, c_1061])).
% 3.80/1.59  tff(c_1070, plain, (![B_481]: (m1_subset_1('#skF_1'('#skF_5', B_481), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_481, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_404, c_1067])).
% 3.80/1.59  tff(c_1072, plain, (![B_482]: (m1_subset_1('#skF_1'('#skF_5', B_482), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_482, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_56, c_1070])).
% 3.80/1.59  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.80/1.59  tff(c_1077, plain, (![B_483]: (r1_tarski('#skF_1'('#skF_5', B_483), u1_struct_0('#skF_4')) | ~m1_subset_1(B_483, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1072, c_8])).
% 3.80/1.59  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.80/1.59  tff(c_72, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_66, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_40, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_36, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_74, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_36])).
% 3.80/1.59  tff(c_64, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_62, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_52, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_50, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_464, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_50])).
% 3.80/1.59  tff(c_48, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_463, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_404, c_48])).
% 3.80/1.59  tff(c_405, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_374])).
% 3.80/1.59  tff(c_38, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_220])).
% 3.80/1.59  tff(c_802, plain, (![B_464, D_469, C_468, H_467, E_466, F_465, A_463]: (r1_tmap_1(D_469, B_464, E_466, H_467) | ~r1_tmap_1(C_468, B_464, k3_tmap_1(A_463, B_464, D_469, C_468, E_466), H_467) | ~m1_connsp_2(F_465, D_469, H_467) | ~r1_tarski(F_465, u1_struct_0(C_468)) | ~m1_subset_1(H_467, u1_struct_0(C_468)) | ~m1_subset_1(H_467, u1_struct_0(D_469)) | ~m1_subset_1(F_465, k1_zfmisc_1(u1_struct_0(D_469))) | ~m1_pre_topc(C_468, D_469) | ~m1_subset_1(E_466, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_469), u1_struct_0(B_464)))) | ~v1_funct_2(E_466, u1_struct_0(D_469), u1_struct_0(B_464)) | ~v1_funct_1(E_466) | ~m1_pre_topc(D_469, A_463) | v2_struct_0(D_469) | ~m1_pre_topc(C_468, A_463) | v2_struct_0(C_468) | ~l1_pre_topc(B_464) | ~v2_pre_topc(B_464) | v2_struct_0(B_464) | ~l1_pre_topc(A_463) | ~v2_pre_topc(A_463) | v2_struct_0(A_463))), inference(cnfTransformation, [status(thm)], [f_171])).
% 3.80/1.59  tff(c_804, plain, (![F_465]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_465, '#skF_5', '#skF_8') | ~r1_tarski(F_465, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_465, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_38, c_802])).
% 3.80/1.59  tff(c_807, plain, (![F_465]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_465, '#skF_5', '#skF_8') | ~r1_tarski(F_465, u1_struct_0('#skF_4')) | ~m1_subset_1(F_465, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_464, c_404, c_463, c_404, c_405, c_404, c_42, c_404, c_42, c_804])).
% 3.80/1.59  tff(c_809, plain, (![F_470]: (~m1_connsp_2(F_470, '#skF_5', '#skF_8') | ~r1_tarski(F_470, u1_struct_0('#skF_4')) | ~m1_subset_1(F_470, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_74, c_807])).
% 3.80/1.59  tff(c_814, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_809])).
% 3.80/1.59  tff(c_1085, plain, (![B_484]: (~m1_connsp_2('#skF_1'('#skF_5', B_484), '#skF_5', '#skF_8') | ~m1_subset_1(B_484, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1077, c_814])).
% 3.80/1.59  tff(c_1089, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_1085])).
% 3.80/1.59  tff(c_1092, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_42, c_404, c_42, c_1089])).
% 3.80/1.59  tff(c_1094, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_1092])).
% 3.80/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.59  
% 3.80/1.59  Inference rules
% 3.80/1.59  ----------------------
% 3.80/1.59  #Ref     : 0
% 3.80/1.59  #Sup     : 192
% 3.80/1.59  #Fact    : 0
% 3.80/1.59  #Define  : 0
% 3.80/1.59  #Split   : 6
% 3.80/1.59  #Chain   : 0
% 3.80/1.59  #Close   : 0
% 3.80/1.59  
% 3.80/1.59  Ordering : KBO
% 3.80/1.59  
% 3.80/1.59  Simplification rules
% 3.80/1.59  ----------------------
% 3.80/1.59  #Subsume      : 47
% 3.80/1.59  #Demod        : 312
% 3.80/1.59  #Tautology    : 69
% 3.80/1.59  #SimpNegUnit  : 3
% 3.80/1.59  #BackRed      : 5
% 3.80/1.59  
% 3.80/1.59  #Partial instantiations: 0
% 3.80/1.59  #Strategies tried      : 1
% 3.80/1.59  
% 3.80/1.59  Timing (in seconds)
% 3.80/1.59  ----------------------
% 3.80/1.59  Preprocessing        : 0.39
% 3.80/1.59  Parsing              : 0.19
% 3.80/1.59  CNF conversion       : 0.06
% 3.80/1.59  Main loop            : 0.44
% 3.80/1.59  Inferencing          : 0.14
% 3.80/1.59  Reduction            : 0.15
% 3.80/1.59  Demodulation         : 0.11
% 3.80/1.59  BG Simplification    : 0.02
% 3.80/1.59  Subsumption          : 0.10
% 3.80/1.59  Abstraction          : 0.02
% 3.80/1.59  MUC search           : 0.00
% 3.80/1.59  Cooper               : 0.00
% 3.80/1.59  Total                : 0.87
% 3.80/1.59  Index Insertion      : 0.00
% 3.80/1.59  Index Deletion       : 0.00
% 3.80/1.59  Index Matching       : 0.00
% 3.80/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
