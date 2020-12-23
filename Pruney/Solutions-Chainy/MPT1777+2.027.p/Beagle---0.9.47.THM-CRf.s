%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:36 EST 2020

% Result     : Theorem 7.32s
% Output     : CNFRefutation 7.32s
% Verified   : 
% Statistics : Number of formulae       :  135 ( 707 expanded)
%              Number of leaves         :   45 ( 267 expanded)
%              Depth                    :   35
%              Number of atoms          :  387 (4052 expanded)
%              Number of equality atoms :   32 ( 579 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1

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

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(g1_pre_topc,type,(
    g1_pre_topc: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

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

tff(f_254,negated_conjecture,(
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

tff(f_99,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_123,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,u1_struct_0(A))
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( m1_connsp_2(C,A,B)
              <=> ? [D] :
                    ( m1_subset_1(D,k1_zfmisc_1(u1_struct_0(A)))
                    & v3_pre_topc(D,A)
                    & r1_tarski(D,C)
                    & r2_hidden(B,D) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_connsp_2)).

tff(f_136,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_132,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_55,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_64,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_73,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_205,axiom,(
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
                                   => ( ( v3_pre_topc(F,D)
                                        & r2_hidden(G,F)
                                        & r1_tarski(F,u1_struct_0(C))
                                        & G = H )
                                     => ( r1_tmap_1(D,B,E,G)
                                      <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),H) ) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_tmap_1)).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_82,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_80,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_66,plain,(
    m1_pre_topc('#skF_6','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_123,plain,(
    ! [B_442,A_443] :
      ( v2_pre_topc(B_442)
      | ~ m1_pre_topc(B_442,A_443)
      | ~ l1_pre_topc(A_443)
      | ~ v2_pre_topc(A_443) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_129,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_136,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_129])).

tff(c_96,plain,(
    ! [B_436,A_437] :
      ( l1_pre_topc(B_436)
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_102,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_66,c_96])).

tff(c_109,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_102])).

tff(c_56,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_24,plain,(
    ! [A_24,B_25] :
      ( m1_connsp_2('#skF_1'(A_24,B_25),A_24,B_25)
      | ~ m1_subset_1(B_25,u1_struct_0(A_24))
      | ~ l1_pre_topc(A_24)
      | ~ v2_pre_topc(A_24)
      | v2_struct_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_1061,plain,(
    ! [C_499,A_500,B_501] :
      ( m1_subset_1(C_499,k1_zfmisc_1(u1_struct_0(A_500)))
      | ~ m1_connsp_2(C_499,A_500,B_501)
      | ~ m1_subset_1(B_501,u1_struct_0(A_500))
      | ~ l1_pre_topc(A_500)
      | ~ v2_pre_topc(A_500)
      | v2_struct_0(A_500) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1776,plain,(
    ! [A_539,B_540] :
      ( m1_subset_1('#skF_1'(A_539,B_540),k1_zfmisc_1(u1_struct_0(A_539)))
      | ~ m1_subset_1(B_540,u1_struct_0(A_539))
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(resolution,[status(thm)],[c_24,c_1061])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1806,plain,(
    ! [A_539,B_540] :
      ( r1_tarski('#skF_1'(A_539,B_540),u1_struct_0(A_539))
      | ~ m1_subset_1(B_540,u1_struct_0(A_539))
      | ~ l1_pre_topc(A_539)
      | ~ v2_pre_topc(A_539)
      | v2_struct_0(A_539) ) ),
    inference(resolution,[status(thm)],[c_1776,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1713,plain,(
    ! [B_535,A_536,C_537] :
      ( r2_hidden(B_535,'#skF_2'(A_536,B_535,C_537))
      | ~ m1_connsp_2(C_537,A_536,B_535)
      | ~ m1_subset_1(C_537,k1_zfmisc_1(u1_struct_0(A_536)))
      | ~ m1_subset_1(B_535,u1_struct_0(A_536))
      | ~ l1_pre_topc(A_536)
      | ~ v2_pre_topc(A_536)
      | v2_struct_0(A_536) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1722,plain,(
    ! [B_535,A_536,A_1] :
      ( r2_hidden(B_535,'#skF_2'(A_536,B_535,A_1))
      | ~ m1_connsp_2(A_1,A_536,B_535)
      | ~ m1_subset_1(B_535,u1_struct_0(A_536))
      | ~ l1_pre_topc(A_536)
      | ~ v2_pre_topc(A_536)
      | v2_struct_0(A_536)
      | ~ r1_tarski(A_1,u1_struct_0(A_536)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1713])).

tff(c_1472,plain,(
    ! [A_524,B_525,C_526] :
      ( v3_pre_topc('#skF_2'(A_524,B_525,C_526),A_524)
      | ~ m1_connsp_2(C_526,A_524,B_525)
      | ~ m1_subset_1(C_526,k1_zfmisc_1(u1_struct_0(A_524)))
      | ~ m1_subset_1(B_525,u1_struct_0(A_524))
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_1481,plain,(
    ! [A_524,B_525,A_1] :
      ( v3_pre_topc('#skF_2'(A_524,B_525,A_1),A_524)
      | ~ m1_connsp_2(A_1,A_524,B_525)
      | ~ m1_subset_1(B_525,u1_struct_0(A_524))
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524)
      | ~ r1_tarski(A_1,u1_struct_0(A_524)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1472])).

tff(c_2067,plain,(
    ! [A_549,B_550,C_551] :
      ( m1_subset_1('#skF_2'(A_549,B_550,C_551),k1_zfmisc_1(u1_struct_0(A_549)))
      | ~ m1_connsp_2(C_551,A_549,B_550)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(u1_struct_0(A_549)))
      | ~ m1_subset_1(B_550,u1_struct_0(A_549))
      | ~ l1_pre_topc(A_549)
      | ~ v2_pre_topc(A_549)
      | v2_struct_0(A_549) ) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_5332,plain,(
    ! [A_685,B_686,C_687] :
      ( r1_tarski('#skF_2'(A_685,B_686,C_687),u1_struct_0(A_685))
      | ~ m1_connsp_2(C_687,A_685,B_686)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(u1_struct_0(A_685)))
      | ~ m1_subset_1(B_686,u1_struct_0(A_685))
      | ~ l1_pre_topc(A_685)
      | ~ v2_pre_topc(A_685)
      | v2_struct_0(A_685) ) ),
    inference(resolution,[status(thm)],[c_2067,c_2])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_76,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_74,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_70,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_64,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_62,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_60,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_105,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_96])).

tff(c_112,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_105])).

tff(c_40,plain,(
    ! [A_52] :
      ( m1_pre_topc(A_52,A_52)
      | ~ l1_pre_topc(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')) = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_166,plain,(
    ! [B_447,A_448] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(B_447),u1_pre_topc(B_447)))
      | ~ m1_pre_topc(B_447,A_448)
      | ~ l1_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_172,plain,
    ( v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_5')))
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_166])).

tff(c_179,plain,(
    v1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_58,c_172])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10] :
      ( m1_subset_1(u1_pre_topc(A_10),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10))))
      | ~ l1_pre_topc(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_275,plain,(
    ! [D_455,B_456,C_457,A_458] :
      ( D_455 = B_456
      | g1_pre_topc(C_457,D_455) != g1_pre_topc(A_458,B_456)
      | ~ m1_subset_1(B_456,k1_zfmisc_1(k1_zfmisc_1(A_458))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_283,plain,(
    ! [D_455,C_457] :
      ( u1_pre_topc('#skF_5') = D_455
      | g1_pre_topc(C_457,D_455) != '#skF_6'
      | ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_275])).

tff(c_308,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_311,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_12,c_308])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_311])).

tff(c_321,plain,(
    ! [D_464,C_465] :
      ( u1_pre_topc('#skF_5') = D_464
      | g1_pre_topc(C_465,D_464) != '#skF_6' ) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_335,plain,(
    ! [A_466] :
      ( u1_pre_topc(A_466) = u1_pre_topc('#skF_5')
      | A_466 != '#skF_6'
      | ~ v1_pre_topc(A_466)
      | ~ l1_pre_topc(A_466) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_321])).

tff(c_344,plain,
    ( u1_pre_topc('#skF_5') = u1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_179,c_335])).

tff(c_351,plain,(
    u1_pre_topc('#skF_5') = u1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_344])).

tff(c_320,plain,(
    m1_subset_1(u1_pre_topc('#skF_5'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_370,plain,(
    m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_320])).

tff(c_372,plain,(
    g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_351,c_58])).

tff(c_456,plain,(
    ! [C_473,A_474,D_475,B_476] :
      ( C_473 = A_474
      | g1_pre_topc(C_473,D_475) != g1_pre_topc(A_474,B_476)
      | ~ m1_subset_1(B_476,k1_zfmisc_1(k1_zfmisc_1(A_474))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_460,plain,(
    ! [C_473,D_475] :
      ( u1_struct_0('#skF_5') = C_473
      | g1_pre_topc(C_473,D_475) != '#skF_6'
      | ~ m1_subset_1(u1_pre_topc('#skF_6'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_372,c_456])).

tff(c_468,plain,(
    ! [C_477,D_478] :
      ( u1_struct_0('#skF_5') = C_477
      | g1_pre_topc(C_477,D_478) != '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_370,c_460])).

tff(c_524,plain,(
    ! [A_481] :
      ( u1_struct_0(A_481) = u1_struct_0('#skF_5')
      | A_481 != '#skF_6'
      | ~ v1_pre_topc(A_481)
      | ~ l1_pre_topc(A_481) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_468])).

tff(c_533,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_6') ),
    inference(resolution,[status(thm)],[c_179,c_524])).

tff(c_540,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_533])).

tff(c_544,plain,(
    g1_pre_topc(u1_struct_0('#skF_6'),u1_pre_topc('#skF_6')) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_372])).

tff(c_748,plain,(
    ! [A_488,B_489] :
      ( m1_pre_topc(A_488,g1_pre_topc(u1_struct_0(B_489),u1_pre_topc(B_489)))
      | ~ m1_pre_topc(A_488,B_489)
      | ~ l1_pre_topc(B_489)
      | ~ l1_pre_topc(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_776,plain,(
    ! [A_488] :
      ( m1_pre_topc(A_488,g1_pre_topc(u1_struct_0('#skF_5'),u1_pre_topc('#skF_6')))
      | ~ m1_pre_topc(A_488,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ l1_pre_topc(A_488) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_351,c_748])).

tff(c_795,plain,(
    ! [A_490] :
      ( m1_pre_topc(A_490,'#skF_6')
      | ~ m1_pre_topc(A_490,'#skF_5')
      | ~ l1_pre_topc(A_490) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_544,c_540,c_776])).

tff(c_817,plain,
    ( m1_pre_topc('#skF_5','#skF_6')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_795])).

tff(c_833,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_817])).

tff(c_52,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_50,plain,(
    r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_254])).

tff(c_86,plain,(
    r1_tmap_1('#skF_5','#skF_4',k3_tmap_1('#skF_3','#skF_4','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50])).

tff(c_2588,plain,(
    ! [H_593,A_592,E_594,F_589,B_591,C_590,D_595] :
      ( r1_tmap_1(D_595,B_591,E_594,H_593)
      | ~ r1_tmap_1(C_590,B_591,k3_tmap_1(A_592,B_591,D_595,C_590,E_594),H_593)
      | ~ r1_tarski(F_589,u1_struct_0(C_590))
      | ~ r2_hidden(H_593,F_589)
      | ~ v3_pre_topc(F_589,D_595)
      | ~ m1_subset_1(H_593,u1_struct_0(C_590))
      | ~ m1_subset_1(H_593,u1_struct_0(D_595))
      | ~ m1_subset_1(F_589,k1_zfmisc_1(u1_struct_0(D_595)))
      | ~ m1_pre_topc(C_590,D_595)
      | ~ m1_subset_1(E_594,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_595),u1_struct_0(B_591))))
      | ~ v1_funct_2(E_594,u1_struct_0(D_595),u1_struct_0(B_591))
      | ~ v1_funct_1(E_594)
      | ~ m1_pre_topc(D_595,A_592)
      | v2_struct_0(D_595)
      | ~ m1_pre_topc(C_590,A_592)
      | v2_struct_0(C_590)
      | ~ l1_pre_topc(B_591)
      | ~ v2_pre_topc(B_591)
      | v2_struct_0(B_591)
      | ~ l1_pre_topc(A_592)
      | ~ v2_pre_topc(A_592)
      | v2_struct_0(A_592) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_2590,plain,(
    ! [F_589] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
      | ~ r1_tarski(F_589,u1_struct_0('#skF_5'))
      | ~ r2_hidden('#skF_8',F_589)
      | ~ v3_pre_topc(F_589,'#skF_6')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ m1_subset_1(F_589,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc('#skF_5','#skF_6')
      | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_4'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc('#skF_6','#skF_3')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc('#skF_5','#skF_3')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_86,c_2588])).

tff(c_2593,plain,(
    ! [F_589] :
      ( r1_tmap_1('#skF_6','#skF_4','#skF_7','#skF_8')
      | ~ r1_tarski(F_589,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',F_589)
      | ~ v3_pre_topc(F_589,'#skF_6')
      | ~ m1_subset_1(F_589,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_70,c_66,c_64,c_62,c_60,c_833,c_56,c_56,c_540,c_540,c_2590])).

tff(c_2707,plain,(
    ! [F_599] :
      ( ~ r1_tarski(F_599,u1_struct_0('#skF_6'))
      | ~ r2_hidden('#skF_8',F_599)
      | ~ v3_pre_topc(F_599,'#skF_6')
      | ~ m1_subset_1(F_599,k1_zfmisc_1(u1_struct_0('#skF_6'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_72,c_68,c_48,c_2593])).

tff(c_2736,plain,(
    ! [A_1] :
      ( ~ r2_hidden('#skF_8',A_1)
      | ~ v3_pre_topc(A_1,'#skF_6')
      | ~ r1_tarski(A_1,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_4,c_2707])).

tff(c_5336,plain,(
    ! [B_686,C_687] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_6',B_686,C_687))
      | ~ v3_pre_topc('#skF_2'('#skF_6',B_686,C_687),'#skF_6')
      | ~ m1_connsp_2(C_687,'#skF_6',B_686)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_686,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_5332,c_2736])).

tff(c_5344,plain,(
    ! [B_686,C_687] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_6',B_686,C_687))
      | ~ v3_pre_topc('#skF_2'('#skF_6',B_686,C_687),'#skF_6')
      | ~ m1_connsp_2(C_687,'#skF_6',B_686)
      | ~ m1_subset_1(C_687,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_686,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_5336])).

tff(c_7002,plain,(
    ! [B_724,C_725] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_6',B_724,C_725))
      | ~ v3_pre_topc('#skF_2'('#skF_6',B_724,C_725),'#skF_6')
      | ~ m1_connsp_2(C_725,'#skF_6',B_724)
      | ~ m1_subset_1(C_725,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_subset_1(B_724,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_5344])).

tff(c_7010,plain,(
    ! [B_525,A_1] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_6',B_525,A_1))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_1,'#skF_6',B_525)
      | ~ m1_subset_1(B_525,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_1,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1481,c_7002])).

tff(c_7018,plain,(
    ! [B_525,A_1] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_6',B_525,A_1))
      | ~ m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_1,'#skF_6',B_525)
      | ~ m1_subset_1(B_525,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_1,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_7010])).

tff(c_7689,plain,(
    ! [B_744,A_745] :
      ( ~ r2_hidden('#skF_8','#skF_2'('#skF_6',B_744,A_745))
      | ~ m1_subset_1(A_745,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_745,'#skF_6',B_744)
      | ~ m1_subset_1(B_744,u1_struct_0('#skF_6'))
      | ~ r1_tarski(A_745,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7018])).

tff(c_7698,plain,(
    ! [A_1] :
      ( ~ m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_1,'#skF_6','#skF_8')
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_1,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1722,c_7689])).

tff(c_7708,plain,(
    ! [A_1] :
      ( ~ m1_subset_1(A_1,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_1,'#skF_6','#skF_8')
      | v2_struct_0('#skF_6')
      | ~ r1_tarski(A_1,u1_struct_0('#skF_6')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_56,c_7698])).

tff(c_7710,plain,(
    ! [A_746] :
      ( ~ m1_subset_1(A_746,k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_connsp_2(A_746,'#skF_6','#skF_8')
      | ~ r1_tarski(A_746,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7708])).

tff(c_7740,plain,(
    ! [A_747] :
      ( ~ m1_connsp_2(A_747,'#skF_6','#skF_8')
      | ~ r1_tarski(A_747,u1_struct_0('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_4,c_7710])).

tff(c_7759,plain,(
    ! [B_540] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_540),'#skF_6','#skF_8')
      | ~ m1_subset_1(B_540,u1_struct_0('#skF_6'))
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_1806,c_7740])).

tff(c_7772,plain,(
    ! [B_540] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_540),'#skF_6','#skF_8')
      | ~ m1_subset_1(B_540,u1_struct_0('#skF_6'))
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_7759])).

tff(c_7775,plain,(
    ! [B_748] :
      ( ~ m1_connsp_2('#skF_1'('#skF_6',B_748),'#skF_6','#skF_8')
      | ~ m1_subset_1(B_748,u1_struct_0('#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7772])).

tff(c_7779,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_24,c_7775])).

tff(c_7782,plain,(
    v2_struct_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_136,c_109,c_56,c_7779])).

tff(c_7784,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_7782])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:53:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.32/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.45  
% 7.32/2.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.45  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 7.32/2.45  
% 7.32/2.45  %Foreground sorts:
% 7.32/2.45  
% 7.32/2.45  
% 7.32/2.45  %Background operators:
% 7.32/2.45  
% 7.32/2.45  
% 7.32/2.45  %Foreground operators:
% 7.32/2.45  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 7.32/2.45  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 7.32/2.45  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 7.32/2.45  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 7.32/2.45  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 7.32/2.45  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 7.32/2.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.32/2.45  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 7.32/2.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.32/2.45  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 7.32/2.45  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 7.32/2.45  tff('#skF_7', type, '#skF_7': $i).
% 7.32/2.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.32/2.45  tff('#skF_5', type, '#skF_5': $i).
% 7.32/2.45  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 7.32/2.45  tff('#skF_6', type, '#skF_6': $i).
% 7.32/2.45  tff('#skF_3', type, '#skF_3': $i).
% 7.32/2.45  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.32/2.45  tff('#skF_9', type, '#skF_9': $i).
% 7.32/2.45  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 7.32/2.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 7.32/2.45  tff('#skF_8', type, '#skF_8': $i).
% 7.32/2.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.32/2.45  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.32/2.45  tff('#skF_4', type, '#skF_4': $i).
% 7.32/2.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.32/2.45  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 7.32/2.45  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 7.32/2.45  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 7.32/2.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.32/2.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.32/2.45  
% 7.32/2.47  tff(f_254, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 7.32/2.47  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 7.32/2.47  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 7.32/2.47  tff(f_99, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 7.32/2.47  tff(f_87, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 7.32/2.47  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.32/2.47  tff(f_123, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, u1_struct_0(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => (m1_connsp_2(C, A, B) <=> (?[D]: (((m1_subset_1(D, k1_zfmisc_1(u1_struct_0(A))) & v3_pre_topc(D, A)) & r1_tarski(D, C)) & r2_hidden(B, D)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_connsp_2)).
% 7.32/2.47  tff(f_136, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 7.32/2.47  tff(f_132, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_tmap_1)).
% 7.32/2.47  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 7.32/2.47  tff(f_55, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 7.32/2.47  tff(f_64, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 7.32/2.47  tff(f_73, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 7.32/2.47  tff(f_205, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_tmap_1)).
% 7.32/2.47  tff(c_68, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_82, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_80, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_66, plain, (m1_pre_topc('#skF_6', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_123, plain, (![B_442, A_443]: (v2_pre_topc(B_442) | ~m1_pre_topc(B_442, A_443) | ~l1_pre_topc(A_443) | ~v2_pre_topc(A_443))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.32/2.47  tff(c_129, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_123])).
% 7.32/2.47  tff(c_136, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_129])).
% 7.32/2.47  tff(c_96, plain, (![B_436, A_437]: (l1_pre_topc(B_436) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.32/2.47  tff(c_102, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_66, c_96])).
% 7.32/2.47  tff(c_109, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_102])).
% 7.32/2.47  tff(c_56, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_24, plain, (![A_24, B_25]: (m1_connsp_2('#skF_1'(A_24, B_25), A_24, B_25) | ~m1_subset_1(B_25, u1_struct_0(A_24)) | ~l1_pre_topc(A_24) | ~v2_pre_topc(A_24) | v2_struct_0(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 7.32/2.47  tff(c_1061, plain, (![C_499, A_500, B_501]: (m1_subset_1(C_499, k1_zfmisc_1(u1_struct_0(A_500))) | ~m1_connsp_2(C_499, A_500, B_501) | ~m1_subset_1(B_501, u1_struct_0(A_500)) | ~l1_pre_topc(A_500) | ~v2_pre_topc(A_500) | v2_struct_0(A_500))), inference(cnfTransformation, [status(thm)], [f_87])).
% 7.32/2.47  tff(c_1776, plain, (![A_539, B_540]: (m1_subset_1('#skF_1'(A_539, B_540), k1_zfmisc_1(u1_struct_0(A_539))) | ~m1_subset_1(B_540, u1_struct_0(A_539)) | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(resolution, [status(thm)], [c_24, c_1061])).
% 7.32/2.47  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.32/2.47  tff(c_1806, plain, (![A_539, B_540]: (r1_tarski('#skF_1'(A_539, B_540), u1_struct_0(A_539)) | ~m1_subset_1(B_540, u1_struct_0(A_539)) | ~l1_pre_topc(A_539) | ~v2_pre_topc(A_539) | v2_struct_0(A_539))), inference(resolution, [status(thm)], [c_1776, c_2])).
% 7.32/2.47  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.32/2.47  tff(c_1713, plain, (![B_535, A_536, C_537]: (r2_hidden(B_535, '#skF_2'(A_536, B_535, C_537)) | ~m1_connsp_2(C_537, A_536, B_535) | ~m1_subset_1(C_537, k1_zfmisc_1(u1_struct_0(A_536))) | ~m1_subset_1(B_535, u1_struct_0(A_536)) | ~l1_pre_topc(A_536) | ~v2_pre_topc(A_536) | v2_struct_0(A_536))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.32/2.47  tff(c_1722, plain, (![B_535, A_536, A_1]: (r2_hidden(B_535, '#skF_2'(A_536, B_535, A_1)) | ~m1_connsp_2(A_1, A_536, B_535) | ~m1_subset_1(B_535, u1_struct_0(A_536)) | ~l1_pre_topc(A_536) | ~v2_pre_topc(A_536) | v2_struct_0(A_536) | ~r1_tarski(A_1, u1_struct_0(A_536)))), inference(resolution, [status(thm)], [c_4, c_1713])).
% 7.32/2.47  tff(c_1472, plain, (![A_524, B_525, C_526]: (v3_pre_topc('#skF_2'(A_524, B_525, C_526), A_524) | ~m1_connsp_2(C_526, A_524, B_525) | ~m1_subset_1(C_526, k1_zfmisc_1(u1_struct_0(A_524))) | ~m1_subset_1(B_525, u1_struct_0(A_524)) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.32/2.47  tff(c_1481, plain, (![A_524, B_525, A_1]: (v3_pre_topc('#skF_2'(A_524, B_525, A_1), A_524) | ~m1_connsp_2(A_1, A_524, B_525) | ~m1_subset_1(B_525, u1_struct_0(A_524)) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524) | ~r1_tarski(A_1, u1_struct_0(A_524)))), inference(resolution, [status(thm)], [c_4, c_1472])).
% 7.32/2.47  tff(c_2067, plain, (![A_549, B_550, C_551]: (m1_subset_1('#skF_2'(A_549, B_550, C_551), k1_zfmisc_1(u1_struct_0(A_549))) | ~m1_connsp_2(C_551, A_549, B_550) | ~m1_subset_1(C_551, k1_zfmisc_1(u1_struct_0(A_549))) | ~m1_subset_1(B_550, u1_struct_0(A_549)) | ~l1_pre_topc(A_549) | ~v2_pre_topc(A_549) | v2_struct_0(A_549))), inference(cnfTransformation, [status(thm)], [f_123])).
% 7.32/2.47  tff(c_5332, plain, (![A_685, B_686, C_687]: (r1_tarski('#skF_2'(A_685, B_686, C_687), u1_struct_0(A_685)) | ~m1_connsp_2(C_687, A_685, B_686) | ~m1_subset_1(C_687, k1_zfmisc_1(u1_struct_0(A_685))) | ~m1_subset_1(B_686, u1_struct_0(A_685)) | ~l1_pre_topc(A_685) | ~v2_pre_topc(A_685) | v2_struct_0(A_685))), inference(resolution, [status(thm)], [c_2067, c_2])).
% 7.32/2.47  tff(c_84, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_78, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_72, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_48, plain, (~r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_76, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_74, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_70, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_64, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_62, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_60, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_105, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_96])).
% 7.32/2.47  tff(c_112, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_105])).
% 7.32/2.47  tff(c_40, plain, (![A_52]: (m1_pre_topc(A_52, A_52) | ~l1_pre_topc(A_52))), inference(cnfTransformation, [status(thm)], [f_136])).
% 7.32/2.47  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))='#skF_6'), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_166, plain, (![B_447, A_448]: (v1_pre_topc(g1_pre_topc(u1_struct_0(B_447), u1_pre_topc(B_447))) | ~m1_pre_topc(B_447, A_448) | ~l1_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_132])).
% 7.32/2.47  tff(c_172, plain, (v1_pre_topc(g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_5'))) | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_70, c_166])).
% 7.32/2.47  tff(c_179, plain, (v1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_58, c_172])).
% 7.32/2.47  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.32/2.47  tff(c_12, plain, (![A_10]: (m1_subset_1(u1_pre_topc(A_10), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_10)))) | ~l1_pre_topc(A_10))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.32/2.47  tff(c_275, plain, (![D_455, B_456, C_457, A_458]: (D_455=B_456 | g1_pre_topc(C_457, D_455)!=g1_pre_topc(A_458, B_456) | ~m1_subset_1(B_456, k1_zfmisc_1(k1_zfmisc_1(A_458))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.32/2.47  tff(c_283, plain, (![D_455, C_457]: (u1_pre_topc('#skF_5')=D_455 | g1_pre_topc(C_457, D_455)!='#skF_6' | ~m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_58, c_275])).
% 7.32/2.47  tff(c_308, plain, (~m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(splitLeft, [status(thm)], [c_283])).
% 7.32/2.47  tff(c_311, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_12, c_308])).
% 7.32/2.47  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_112, c_311])).
% 7.32/2.47  tff(c_321, plain, (![D_464, C_465]: (u1_pre_topc('#skF_5')=D_464 | g1_pre_topc(C_465, D_464)!='#skF_6')), inference(splitRight, [status(thm)], [c_283])).
% 7.32/2.47  tff(c_335, plain, (![A_466]: (u1_pre_topc(A_466)=u1_pre_topc('#skF_5') | A_466!='#skF_6' | ~v1_pre_topc(A_466) | ~l1_pre_topc(A_466))), inference(superposition, [status(thm), theory('equality')], [c_6, c_321])).
% 7.32/2.47  tff(c_344, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_179, c_335])).
% 7.32/2.47  tff(c_351, plain, (u1_pre_topc('#skF_5')=u1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_344])).
% 7.32/2.47  tff(c_320, plain, (m1_subset_1(u1_pre_topc('#skF_5'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(splitRight, [status(thm)], [c_283])).
% 7.32/2.47  tff(c_370, plain, (m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_351, c_320])).
% 7.32/2.47  tff(c_372, plain, (g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_351, c_58])).
% 7.32/2.47  tff(c_456, plain, (![C_473, A_474, D_475, B_476]: (C_473=A_474 | g1_pre_topc(C_473, D_475)!=g1_pre_topc(A_474, B_476) | ~m1_subset_1(B_476, k1_zfmisc_1(k1_zfmisc_1(A_474))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.32/2.47  tff(c_460, plain, (![C_473, D_475]: (u1_struct_0('#skF_5')=C_473 | g1_pre_topc(C_473, D_475)!='#skF_6' | ~m1_subset_1(u1_pre_topc('#skF_6'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_5')))))), inference(superposition, [status(thm), theory('equality')], [c_372, c_456])).
% 7.32/2.47  tff(c_468, plain, (![C_477, D_478]: (u1_struct_0('#skF_5')=C_477 | g1_pre_topc(C_477, D_478)!='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_370, c_460])).
% 7.32/2.47  tff(c_524, plain, (![A_481]: (u1_struct_0(A_481)=u1_struct_0('#skF_5') | A_481!='#skF_6' | ~v1_pre_topc(A_481) | ~l1_pre_topc(A_481))), inference(superposition, [status(thm), theory('equality')], [c_6, c_468])).
% 7.32/2.47  tff(c_533, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6') | ~l1_pre_topc('#skF_6')), inference(resolution, [status(thm)], [c_179, c_524])).
% 7.32/2.47  tff(c_540, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_109, c_533])).
% 7.32/2.47  tff(c_544, plain, (g1_pre_topc(u1_struct_0('#skF_6'), u1_pre_topc('#skF_6'))='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_540, c_372])).
% 7.32/2.47  tff(c_748, plain, (![A_488, B_489]: (m1_pre_topc(A_488, g1_pre_topc(u1_struct_0(B_489), u1_pre_topc(B_489))) | ~m1_pre_topc(A_488, B_489) | ~l1_pre_topc(B_489) | ~l1_pre_topc(A_488))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.32/2.47  tff(c_776, plain, (![A_488]: (m1_pre_topc(A_488, g1_pre_topc(u1_struct_0('#skF_5'), u1_pre_topc('#skF_6'))) | ~m1_pre_topc(A_488, '#skF_5') | ~l1_pre_topc('#skF_5') | ~l1_pre_topc(A_488))), inference(superposition, [status(thm), theory('equality')], [c_351, c_748])).
% 7.32/2.47  tff(c_795, plain, (![A_490]: (m1_pre_topc(A_490, '#skF_6') | ~m1_pre_topc(A_490, '#skF_5') | ~l1_pre_topc(A_490))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_544, c_540, c_776])).
% 7.32/2.47  tff(c_817, plain, (m1_pre_topc('#skF_5', '#skF_6') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_40, c_795])).
% 7.32/2.47  tff(c_833, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_112, c_817])).
% 7.32/2.47  tff(c_52, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_50, plain, (r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_254])).
% 7.32/2.47  tff(c_86, plain, (r1_tmap_1('#skF_5', '#skF_4', k3_tmap_1('#skF_3', '#skF_4', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50])).
% 7.32/2.47  tff(c_2588, plain, (![H_593, A_592, E_594, F_589, B_591, C_590, D_595]: (r1_tmap_1(D_595, B_591, E_594, H_593) | ~r1_tmap_1(C_590, B_591, k3_tmap_1(A_592, B_591, D_595, C_590, E_594), H_593) | ~r1_tarski(F_589, u1_struct_0(C_590)) | ~r2_hidden(H_593, F_589) | ~v3_pre_topc(F_589, D_595) | ~m1_subset_1(H_593, u1_struct_0(C_590)) | ~m1_subset_1(H_593, u1_struct_0(D_595)) | ~m1_subset_1(F_589, k1_zfmisc_1(u1_struct_0(D_595))) | ~m1_pre_topc(C_590, D_595) | ~m1_subset_1(E_594, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_595), u1_struct_0(B_591)))) | ~v1_funct_2(E_594, u1_struct_0(D_595), u1_struct_0(B_591)) | ~v1_funct_1(E_594) | ~m1_pre_topc(D_595, A_592) | v2_struct_0(D_595) | ~m1_pre_topc(C_590, A_592) | v2_struct_0(C_590) | ~l1_pre_topc(B_591) | ~v2_pre_topc(B_591) | v2_struct_0(B_591) | ~l1_pre_topc(A_592) | ~v2_pre_topc(A_592) | v2_struct_0(A_592))), inference(cnfTransformation, [status(thm)], [f_205])).
% 7.32/2.47  tff(c_2590, plain, (![F_589]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~r1_tarski(F_589, u1_struct_0('#skF_5')) | ~r2_hidden('#skF_8', F_589) | ~v3_pre_topc(F_589, '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_subset_1(F_589, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_4')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_4')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_3') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_3') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_86, c_2588])).
% 7.32/2.47  tff(c_2593, plain, (![F_589]: (r1_tmap_1('#skF_6', '#skF_4', '#skF_7', '#skF_8') | ~r1_tarski(F_589, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', F_589) | ~v3_pre_topc(F_589, '#skF_6') | ~m1_subset_1(F_589, k1_zfmisc_1(u1_struct_0('#skF_6'))) | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_70, c_66, c_64, c_62, c_60, c_833, c_56, c_56, c_540, c_540, c_2590])).
% 7.32/2.47  tff(c_2707, plain, (![F_599]: (~r1_tarski(F_599, u1_struct_0('#skF_6')) | ~r2_hidden('#skF_8', F_599) | ~v3_pre_topc(F_599, '#skF_6') | ~m1_subset_1(F_599, k1_zfmisc_1(u1_struct_0('#skF_6'))))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_72, c_68, c_48, c_2593])).
% 7.32/2.47  tff(c_2736, plain, (![A_1]: (~r2_hidden('#skF_8', A_1) | ~v3_pre_topc(A_1, '#skF_6') | ~r1_tarski(A_1, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_4, c_2707])).
% 7.32/2.47  tff(c_5336, plain, (![B_686, C_687]: (~r2_hidden('#skF_8', '#skF_2'('#skF_6', B_686, C_687)) | ~v3_pre_topc('#skF_2'('#skF_6', B_686, C_687), '#skF_6') | ~m1_connsp_2(C_687, '#skF_6', B_686) | ~m1_subset_1(C_687, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_686, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_5332, c_2736])).
% 7.32/2.47  tff(c_5344, plain, (![B_686, C_687]: (~r2_hidden('#skF_8', '#skF_2'('#skF_6', B_686, C_687)) | ~v3_pre_topc('#skF_2'('#skF_6', B_686, C_687), '#skF_6') | ~m1_connsp_2(C_687, '#skF_6', B_686) | ~m1_subset_1(C_687, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_686, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_5336])).
% 7.32/2.47  tff(c_7002, plain, (![B_724, C_725]: (~r2_hidden('#skF_8', '#skF_2'('#skF_6', B_724, C_725)) | ~v3_pre_topc('#skF_2'('#skF_6', B_724, C_725), '#skF_6') | ~m1_connsp_2(C_725, '#skF_6', B_724) | ~m1_subset_1(C_725, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_subset_1(B_724, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_5344])).
% 7.32/2.47  tff(c_7010, plain, (![B_525, A_1]: (~r2_hidden('#skF_8', '#skF_2'('#skF_6', B_525, A_1)) | ~m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_1, '#skF_6', B_525) | ~m1_subset_1(B_525, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(A_1, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1481, c_7002])).
% 7.32/2.47  tff(c_7018, plain, (![B_525, A_1]: (~r2_hidden('#skF_8', '#skF_2'('#skF_6', B_525, A_1)) | ~m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_1, '#skF_6', B_525) | ~m1_subset_1(B_525, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6') | ~r1_tarski(A_1, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_7010])).
% 7.32/2.47  tff(c_7689, plain, (![B_744, A_745]: (~r2_hidden('#skF_8', '#skF_2'('#skF_6', B_744, A_745)) | ~m1_subset_1(A_745, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_745, '#skF_6', B_744) | ~m1_subset_1(B_744, u1_struct_0('#skF_6')) | ~r1_tarski(A_745, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_7018])).
% 7.32/2.47  tff(c_7698, plain, (![A_1]: (~m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_1, '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~r1_tarski(A_1, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_1722, c_7689])).
% 7.32/2.47  tff(c_7708, plain, (![A_1]: (~m1_subset_1(A_1, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_1, '#skF_6', '#skF_8') | v2_struct_0('#skF_6') | ~r1_tarski(A_1, u1_struct_0('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_56, c_7698])).
% 7.32/2.47  tff(c_7710, plain, (![A_746]: (~m1_subset_1(A_746, k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_connsp_2(A_746, '#skF_6', '#skF_8') | ~r1_tarski(A_746, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_7708])).
% 7.32/2.47  tff(c_7740, plain, (![A_747]: (~m1_connsp_2(A_747, '#skF_6', '#skF_8') | ~r1_tarski(A_747, u1_struct_0('#skF_6')))), inference(resolution, [status(thm)], [c_4, c_7710])).
% 7.32/2.47  tff(c_7759, plain, (![B_540]: (~m1_connsp_2('#skF_1'('#skF_6', B_540), '#skF_6', '#skF_8') | ~m1_subset_1(B_540, u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_1806, c_7740])).
% 7.32/2.47  tff(c_7772, plain, (![B_540]: (~m1_connsp_2('#skF_1'('#skF_6', B_540), '#skF_6', '#skF_8') | ~m1_subset_1(B_540, u1_struct_0('#skF_6')) | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_7759])).
% 7.32/2.47  tff(c_7775, plain, (![B_748]: (~m1_connsp_2('#skF_1'('#skF_6', B_748), '#skF_6', '#skF_8') | ~m1_subset_1(B_748, u1_struct_0('#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_68, c_7772])).
% 7.32/2.47  tff(c_7779, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6')), inference(resolution, [status(thm)], [c_24, c_7775])).
% 7.32/2.47  tff(c_7782, plain, (v2_struct_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_136, c_109, c_56, c_7779])).
% 7.32/2.47  tff(c_7784, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_7782])).
% 7.32/2.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.32/2.47  
% 7.32/2.47  Inference rules
% 7.32/2.47  ----------------------
% 7.32/2.47  #Ref     : 6
% 7.32/2.47  #Sup     : 1634
% 7.32/2.47  #Fact    : 0
% 7.32/2.47  #Define  : 0
% 7.32/2.47  #Split   : 4
% 7.32/2.47  #Chain   : 0
% 7.32/2.47  #Close   : 0
% 7.32/2.47  
% 7.32/2.47  Ordering : KBO
% 7.32/2.47  
% 7.32/2.47  Simplification rules
% 7.32/2.47  ----------------------
% 7.32/2.47  #Subsume      : 670
% 7.32/2.47  #Demod        : 3326
% 7.32/2.47  #Tautology    : 479
% 7.32/2.47  #SimpNegUnit  : 36
% 7.32/2.47  #BackRed      : 13
% 7.32/2.47  
% 7.32/2.47  #Partial instantiations: 0
% 7.32/2.47  #Strategies tried      : 1
% 7.32/2.47  
% 7.32/2.47  Timing (in seconds)
% 7.32/2.47  ----------------------
% 7.32/2.48  Preprocessing        : 0.40
% 7.32/2.48  Parsing              : 0.21
% 7.32/2.48  CNF conversion       : 0.06
% 7.32/2.48  Main loop            : 1.30
% 7.32/2.48  Inferencing          : 0.37
% 7.32/2.48  Reduction            : 0.49
% 7.32/2.48  Demodulation         : 0.37
% 7.32/2.48  BG Simplification    : 0.04
% 7.32/2.48  Subsumption          : 0.32
% 7.32/2.48  Abstraction          : 0.06
% 7.32/2.48  MUC search           : 0.00
% 7.32/2.48  Cooper               : 0.00
% 7.32/2.48  Total                : 1.75
% 7.32/2.48  Index Insertion      : 0.00
% 7.32/2.48  Index Deletion       : 0.00
% 7.32/2.48  Index Matching       : 0.00
% 7.32/2.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
