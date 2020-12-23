%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:35 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 4.00s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 776 expanded)
%              Number of leaves         :   41 ( 287 expanded)
%              Depth                    :   15
%              Number of atoms          :  266 (4204 expanded)
%              Number of equality atoms :   20 ( 568 expanded)
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

tff(f_225,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_61,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_subset_1(u1_pre_topc(A),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_u1_pre_topc)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( v1_pre_topc(g1_pre_topc(A,B))
        & l1_pre_topc(g1_pre_topc(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_g1_pre_topc)).

tff(f_35,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ( v1_pre_topc(A)
       => A = g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ! [C,D] :
          ( g1_pre_topc(A,B) = g1_pre_topc(C,D)
         => ( A = C
            & B = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',free_g1_pre_topc)).

tff(f_105,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_93,axiom,(
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

tff(f_109,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_79,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_176,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_72,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_70,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_119,plain,(
    ! [B_421,A_422] :
      ( v2_pre_topc(B_421)
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422)
      | ~ v2_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_135,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_128])).

tff(c_91,plain,(
    ! [B_415,A_416] :
      ( l1_pre_topc(B_415)
      | ~ m1_pre_topc(B_415,A_416)
      | ~ l1_pre_topc(A_416) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_91])).

tff(c_107,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_100])).

tff(c_44,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_60,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_91])).

tff(c_104,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_97])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_16,plain,(
    ! [A_12] :
      ( m1_subset_1(u1_pre_topc(A_12),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12))))
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_136,plain,(
    ! [A_423,B_424] :
      ( v1_pre_topc(g1_pre_topc(A_423,B_424))
      | ~ m1_subset_1(B_424,k1_zfmisc_1(k1_zfmisc_1(A_423))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    ! [A_425] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_425),u1_pre_topc(A_425)))
      | ~ l1_pre_topc(A_425) ) ),
    inference(resolution,[status(thm)],[c_16,c_136])).

tff(c_149,plain,
    ( v1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_146])).

tff(c_151,plain,(
    v1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_149])).

tff(c_6,plain,(
    ! [A_3] :
      ( g1_pre_topc(u1_struct_0(A_3),u1_pre_topc(A_3)) = A_3
      | ~ v1_pre_topc(A_3)
      | ~ l1_pre_topc(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_236,plain,(
    ! [C_442,A_443,D_444,B_445] :
      ( C_442 = A_443
      | g1_pre_topc(C_442,D_444) != g1_pre_topc(A_443,B_445)
      | ~ m1_subset_1(B_445,k1_zfmisc_1(k1_zfmisc_1(A_443))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_244,plain,(
    ! [C_442,D_444] :
      ( u1_struct_0('#skF_4') = C_442
      | g1_pre_topc(C_442,D_444) != '#skF_5'
      | ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_236])).

tff(c_271,plain,(
    ~ m1_subset_1(u1_pre_topc('#skF_4'),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))) ),
    inference(splitLeft,[status(thm)],[c_244])).

tff(c_274,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_271])).

tff(c_281,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_274])).

tff(c_284,plain,(
    ! [C_451,D_452] :
      ( u1_struct_0('#skF_4') = C_451
      | g1_pre_topc(C_451,D_452) != '#skF_5' ) ),
    inference(splitRight,[status(thm)],[c_244])).

tff(c_332,plain,(
    ! [A_453] :
      ( u1_struct_0(A_453) = u1_struct_0('#skF_4')
      | A_453 != '#skF_5'
      | ~ v1_pre_topc(A_453)
      | ~ l1_pre_topc(A_453) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_284])).

tff(c_335,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_151,c_332])).

tff(c_341,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_335])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( m1_connsp_2('#skF_1'(A_26,B_27),A_26,B_27)
      | ~ m1_subset_1(B_27,u1_struct_0(A_26))
      | ~ l1_pre_topc(A_26)
      | ~ v2_pre_topc(A_26)
      | v2_struct_0(A_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_899,plain,(
    ! [C_478,A_479,B_480] :
      ( m1_subset_1(C_478,k1_zfmisc_1(u1_struct_0(A_479)))
      | ~ m1_connsp_2(C_478,A_479,B_480)
      | ~ m1_subset_1(B_480,u1_struct_0(A_479))
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1170,plain,(
    ! [A_501,B_502] :
      ( m1_subset_1('#skF_1'(A_501,B_502),k1_zfmisc_1(u1_struct_0(A_501)))
      | ~ m1_subset_1(B_502,u1_struct_0(A_501))
      | ~ l1_pre_topc(A_501)
      | ~ v2_pre_topc(A_501)
      | v2_struct_0(A_501) ) ),
    inference(resolution,[status(thm)],[c_28,c_899])).

tff(c_1176,plain,(
    ! [B_502] :
      ( m1_subset_1('#skF_1'('#skF_5',B_502),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_502,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_341,c_1170])).

tff(c_1179,plain,(
    ! [B_502] :
      ( m1_subset_1('#skF_1'('#skF_5',B_502),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_502,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_341,c_1176])).

tff(c_1185,plain,(
    ! [B_510] :
      ( m1_subset_1('#skF_1'('#skF_5',B_510),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_510,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1179])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1190,plain,(
    ! [B_511] :
      ( r1_tarski('#skF_1'('#skF_5',B_511),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_511,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1185,c_2])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( m1_subset_1(A_1,k1_zfmisc_1(B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_29] :
      ( m1_pre_topc(A_29,A_29)
      | ~ l1_pre_topc(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_584,plain,(
    ! [A_463,B_464] :
      ( m1_pre_topc(A_463,g1_pre_topc(u1_struct_0(B_464),u1_pre_topc(B_464)))
      | ~ m1_pre_topc(A_463,B_464)
      | ~ l1_pre_topc(B_464)
      | ~ l1_pre_topc(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_611,plain,(
    ! [A_463] :
      ( m1_pre_topc(A_463,'#skF_5')
      | ~ m1_pre_topc(A_463,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ l1_pre_topc(A_463) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_584])).

tff(c_624,plain,(
    ! [A_463] :
      ( m1_pre_topc(A_463,'#skF_5')
      | ~ m1_pre_topc(A_463,'#skF_4')
      | ~ l1_pre_topc(A_463) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_611])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_42,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_76,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_38])).

tff(c_66,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_64,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_54,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_52,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_355,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_52])).

tff(c_50,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_354,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_50])).

tff(c_40,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_225])).

tff(c_1028,plain,(
    ! [D_497,F_496,E_493,B_494,A_492,H_495,C_491] :
      ( r1_tmap_1(D_497,B_494,E_493,H_495)
      | ~ r1_tmap_1(C_491,B_494,k3_tmap_1(A_492,B_494,D_497,C_491,E_493),H_495)
      | ~ m1_connsp_2(F_496,D_497,H_495)
      | ~ r1_tarski(F_496,u1_struct_0(C_491))
      | ~ m1_subset_1(H_495,u1_struct_0(C_491))
      | ~ m1_subset_1(H_495,u1_struct_0(D_497))
      | ~ m1_subset_1(F_496,k1_zfmisc_1(u1_struct_0(D_497)))
      | ~ m1_pre_topc(C_491,D_497)
      | ~ m1_subset_1(E_493,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_497),u1_struct_0(B_494))))
      | ~ v1_funct_2(E_493,u1_struct_0(D_497),u1_struct_0(B_494))
      | ~ v1_funct_1(E_493)
      | ~ m1_pre_topc(D_497,A_492)
      | v2_struct_0(D_497)
      | ~ m1_pre_topc(C_491,A_492)
      | v2_struct_0(C_491)
      | ~ l1_pre_topc(B_494)
      | ~ v2_pre_topc(B_494)
      | v2_struct_0(B_494)
      | ~ l1_pre_topc(A_492)
      | ~ v2_pre_topc(A_492)
      | v2_struct_0(A_492) ) ),
    inference(cnfTransformation,[status(thm)],[f_176])).

tff(c_1030,plain,(
    ! [F_496] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_496,'#skF_5','#skF_8')
      | ~ r1_tarski(F_496,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_496,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_40,c_1028])).

tff(c_1033,plain,(
    ! [F_496] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_496,'#skF_5','#skF_8')
      | ~ r1_tarski(F_496,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_496,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5')
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_355,c_341,c_354,c_341,c_341,c_44,c_341,c_44,c_1030])).

tff(c_1034,plain,(
    ! [F_496] :
      ( ~ m1_connsp_2(F_496,'#skF_5','#skF_8')
      | ~ r1_tarski(F_496,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_496,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_4','#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_76,c_1033])).

tff(c_1035,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1034])).

tff(c_1038,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_624,c_1035])).

tff(c_1041,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1038])).

tff(c_1044,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_1041])).

tff(c_1048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_1044])).

tff(c_1163,plain,(
    ! [F_499] :
      ( ~ m1_connsp_2(F_499,'#skF_5','#skF_8')
      | ~ r1_tarski(F_499,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_499,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(splitRight,[status(thm)],[c_1034])).

tff(c_1168,plain,(
    ! [A_1] :
      ( ~ m1_connsp_2(A_1,'#skF_5','#skF_8')
      | ~ r1_tarski(A_1,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_4,c_1163])).

tff(c_1195,plain,(
    ! [B_512] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_512),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_512,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1190,c_1168])).

tff(c_1199,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_1195])).

tff(c_1202,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_107,c_44,c_341,c_44,c_1199])).

tff(c_1204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n017.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 15:21:01 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.60  
% 3.61/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.61/1.60  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 3.61/1.60  
% 3.61/1.60  %Foreground sorts:
% 3.61/1.60  
% 3.61/1.60  
% 3.61/1.60  %Background operators:
% 3.61/1.60  
% 3.61/1.60  
% 3.61/1.60  %Foreground operators:
% 3.61/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.61/1.60  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.61/1.60  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.60  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.61/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.60  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.61/1.60  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.61/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.61/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.61/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.60  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.61/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.60  tff('#skF_8', type, '#skF_8': $i).
% 3.61/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.61/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.61/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.61/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.60  
% 4.00/1.62  tff(f_225, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.00/1.62  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.00/1.62  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.00/1.62  tff(f_61, axiom, (![A]: (l1_pre_topc(A) => m1_subset_1(u1_pre_topc(A), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_u1_pre_topc)).
% 4.00/1.62  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (v1_pre_topc(g1_pre_topc(A, B)) & l1_pre_topc(g1_pre_topc(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_g1_pre_topc)).
% 4.00/1.62  tff(f_35, axiom, (![A]: (l1_pre_topc(A) => (v1_pre_topc(A) => (A = g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', abstractness_v1_pre_topc)).
% 4.00/1.62  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C, D]: ((g1_pre_topc(A, B) = g1_pre_topc(C, D)) => ((A = C) & (B = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', free_g1_pre_topc)).
% 4.00/1.62  tff(f_105, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.00/1.62  tff(f_93, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.00/1.62  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.00/1.62  tff(f_109, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.00/1.62  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.00/1.62  tff(f_176, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.00/1.62  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_72, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_70, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_119, plain, (![B_421, A_422]: (v2_pre_topc(B_421) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422) | ~v2_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.00/1.62  tff(c_128, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_119])).
% 4.00/1.62  tff(c_135, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_128])).
% 4.00/1.62  tff(c_91, plain, (![B_415, A_416]: (l1_pre_topc(B_415) | ~m1_pre_topc(B_415, A_416) | ~l1_pre_topc(A_416))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.00/1.62  tff(c_100, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_56, c_91])).
% 4.00/1.62  tff(c_107, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_100])).
% 4.00/1.62  tff(c_44, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_60, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_97, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_91])).
% 4.00/1.62  tff(c_104, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_97])).
% 4.00/1.62  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_16, plain, (![A_12]: (m1_subset_1(u1_pre_topc(A_12), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(A_12)))) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.00/1.62  tff(c_136, plain, (![A_423, B_424]: (v1_pre_topc(g1_pre_topc(A_423, B_424)) | ~m1_subset_1(B_424, k1_zfmisc_1(k1_zfmisc_1(A_423))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.00/1.62  tff(c_146, plain, (![A_425]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_425), u1_pre_topc(A_425))) | ~l1_pre_topc(A_425))), inference(resolution, [status(thm)], [c_16, c_136])).
% 4.00/1.62  tff(c_149, plain, (v1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_48, c_146])).
% 4.00/1.62  tff(c_151, plain, (v1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_149])).
% 4.00/1.62  tff(c_6, plain, (![A_3]: (g1_pre_topc(u1_struct_0(A_3), u1_pre_topc(A_3))=A_3 | ~v1_pre_topc(A_3) | ~l1_pre_topc(A_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.00/1.62  tff(c_236, plain, (![C_442, A_443, D_444, B_445]: (C_442=A_443 | g1_pre_topc(C_442, D_444)!=g1_pre_topc(A_443, B_445) | ~m1_subset_1(B_445, k1_zfmisc_1(k1_zfmisc_1(A_443))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.00/1.62  tff(c_244, plain, (![C_442, D_444]: (u1_struct_0('#skF_4')=C_442 | g1_pre_topc(C_442, D_444)!='#skF_5' | ~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4')))))), inference(superposition, [status(thm), theory('equality')], [c_48, c_236])).
% 4.00/1.62  tff(c_271, plain, (~m1_subset_1(u1_pre_topc('#skF_4'), k1_zfmisc_1(k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitLeft, [status(thm)], [c_244])).
% 4.00/1.62  tff(c_274, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_271])).
% 4.00/1.62  tff(c_281, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_274])).
% 4.00/1.62  tff(c_284, plain, (![C_451, D_452]: (u1_struct_0('#skF_4')=C_451 | g1_pre_topc(C_451, D_452)!='#skF_5')), inference(splitRight, [status(thm)], [c_244])).
% 4.00/1.62  tff(c_332, plain, (![A_453]: (u1_struct_0(A_453)=u1_struct_0('#skF_4') | A_453!='#skF_5' | ~v1_pre_topc(A_453) | ~l1_pre_topc(A_453))), inference(superposition, [status(thm), theory('equality')], [c_6, c_284])).
% 4.00/1.62  tff(c_335, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_151, c_332])).
% 4.00/1.62  tff(c_341, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_107, c_335])).
% 4.00/1.62  tff(c_28, plain, (![A_26, B_27]: (m1_connsp_2('#skF_1'(A_26, B_27), A_26, B_27) | ~m1_subset_1(B_27, u1_struct_0(A_26)) | ~l1_pre_topc(A_26) | ~v2_pre_topc(A_26) | v2_struct_0(A_26))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.00/1.62  tff(c_899, plain, (![C_478, A_479, B_480]: (m1_subset_1(C_478, k1_zfmisc_1(u1_struct_0(A_479))) | ~m1_connsp_2(C_478, A_479, B_480) | ~m1_subset_1(B_480, u1_struct_0(A_479)) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.00/1.62  tff(c_1170, plain, (![A_501, B_502]: (m1_subset_1('#skF_1'(A_501, B_502), k1_zfmisc_1(u1_struct_0(A_501))) | ~m1_subset_1(B_502, u1_struct_0(A_501)) | ~l1_pre_topc(A_501) | ~v2_pre_topc(A_501) | v2_struct_0(A_501))), inference(resolution, [status(thm)], [c_28, c_899])).
% 4.00/1.62  tff(c_1176, plain, (![B_502]: (m1_subset_1('#skF_1'('#skF_5', B_502), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_502, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_341, c_1170])).
% 4.00/1.62  tff(c_1179, plain, (![B_502]: (m1_subset_1('#skF_1'('#skF_5', B_502), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_502, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_341, c_1176])).
% 4.00/1.62  tff(c_1185, plain, (![B_510]: (m1_subset_1('#skF_1'('#skF_5', B_510), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_510, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_58, c_1179])).
% 4.00/1.62  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.00/1.62  tff(c_1190, plain, (![B_511]: (r1_tarski('#skF_1'('#skF_5', B_511), u1_struct_0('#skF_4')) | ~m1_subset_1(B_511, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1185, c_2])).
% 4.00/1.62  tff(c_4, plain, (![A_1, B_2]: (m1_subset_1(A_1, k1_zfmisc_1(B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.00/1.62  tff(c_30, plain, (![A_29]: (m1_pre_topc(A_29, A_29) | ~l1_pre_topc(A_29))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.00/1.62  tff(c_584, plain, (![A_463, B_464]: (m1_pre_topc(A_463, g1_pre_topc(u1_struct_0(B_464), u1_pre_topc(B_464))) | ~m1_pre_topc(A_463, B_464) | ~l1_pre_topc(B_464) | ~l1_pre_topc(A_463))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.00/1.62  tff(c_611, plain, (![A_463]: (m1_pre_topc(A_463, '#skF_5') | ~m1_pre_topc(A_463, '#skF_4') | ~l1_pre_topc('#skF_4') | ~l1_pre_topc(A_463))), inference(superposition, [status(thm), theory('equality')], [c_48, c_584])).
% 4.00/1.62  tff(c_624, plain, (![A_463]: (m1_pre_topc(A_463, '#skF_5') | ~m1_pre_topc(A_463, '#skF_4') | ~l1_pre_topc(A_463))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_611])).
% 4.00/1.62  tff(c_74, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_68, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_62, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_42, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_38, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_76, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_38])).
% 4.00/1.62  tff(c_66, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_64, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_54, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_52, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_355, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_52])).
% 4.00/1.62  tff(c_50, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_354, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_341, c_50])).
% 4.00/1.62  tff(c_40, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_225])).
% 4.00/1.62  tff(c_1028, plain, (![D_497, F_496, E_493, B_494, A_492, H_495, C_491]: (r1_tmap_1(D_497, B_494, E_493, H_495) | ~r1_tmap_1(C_491, B_494, k3_tmap_1(A_492, B_494, D_497, C_491, E_493), H_495) | ~m1_connsp_2(F_496, D_497, H_495) | ~r1_tarski(F_496, u1_struct_0(C_491)) | ~m1_subset_1(H_495, u1_struct_0(C_491)) | ~m1_subset_1(H_495, u1_struct_0(D_497)) | ~m1_subset_1(F_496, k1_zfmisc_1(u1_struct_0(D_497))) | ~m1_pre_topc(C_491, D_497) | ~m1_subset_1(E_493, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_497), u1_struct_0(B_494)))) | ~v1_funct_2(E_493, u1_struct_0(D_497), u1_struct_0(B_494)) | ~v1_funct_1(E_493) | ~m1_pre_topc(D_497, A_492) | v2_struct_0(D_497) | ~m1_pre_topc(C_491, A_492) | v2_struct_0(C_491) | ~l1_pre_topc(B_494) | ~v2_pre_topc(B_494) | v2_struct_0(B_494) | ~l1_pre_topc(A_492) | ~v2_pre_topc(A_492) | v2_struct_0(A_492))), inference(cnfTransformation, [status(thm)], [f_176])).
% 4.00/1.62  tff(c_1030, plain, (![F_496]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_496, '#skF_5', '#skF_8') | ~r1_tarski(F_496, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_496, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_40, c_1028])).
% 4.00/1.62  tff(c_1033, plain, (![F_496]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_496, '#skF_5', '#skF_8') | ~r1_tarski(F_496, u1_struct_0('#skF_4')) | ~m1_subset_1(F_496, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_355, c_341, c_354, c_341, c_341, c_44, c_341, c_44, c_1030])).
% 4.00/1.62  tff(c_1034, plain, (![F_496]: (~m1_connsp_2(F_496, '#skF_5', '#skF_8') | ~r1_tarski(F_496, u1_struct_0('#skF_4')) | ~m1_subset_1(F_496, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_76, c_1033])).
% 4.00/1.62  tff(c_1035, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_1034])).
% 4.00/1.62  tff(c_1038, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_624, c_1035])).
% 4.00/1.62  tff(c_1041, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_104, c_1038])).
% 4.00/1.62  tff(c_1044, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_1041])).
% 4.00/1.62  tff(c_1048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_104, c_1044])).
% 4.00/1.62  tff(c_1163, plain, (![F_499]: (~m1_connsp_2(F_499, '#skF_5', '#skF_8') | ~r1_tarski(F_499, u1_struct_0('#skF_4')) | ~m1_subset_1(F_499, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(splitRight, [status(thm)], [c_1034])).
% 4.00/1.62  tff(c_1168, plain, (![A_1]: (~m1_connsp_2(A_1, '#skF_5', '#skF_8') | ~r1_tarski(A_1, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_4, c_1163])).
% 4.00/1.62  tff(c_1195, plain, (![B_512]: (~m1_connsp_2('#skF_1'('#skF_5', B_512), '#skF_5', '#skF_8') | ~m1_subset_1(B_512, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1190, c_1168])).
% 4.00/1.62  tff(c_1199, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_28, c_1195])).
% 4.00/1.62  tff(c_1202, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_107, c_44, c_341, c_44, c_1199])).
% 4.00/1.62  tff(c_1204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1202])).
% 4.00/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.00/1.62  
% 4.00/1.62  Inference rules
% 4.00/1.62  ----------------------
% 4.00/1.62  #Ref     : 4
% 4.00/1.62  #Sup     : 220
% 4.00/1.62  #Fact    : 0
% 4.00/1.62  #Define  : 0
% 4.00/1.62  #Split   : 5
% 4.00/1.62  #Chain   : 0
% 4.00/1.62  #Close   : 0
% 4.00/1.62  
% 4.00/1.62  Ordering : KBO
% 4.00/1.62  
% 4.00/1.62  Simplification rules
% 4.00/1.62  ----------------------
% 4.00/1.62  #Subsume      : 48
% 4.00/1.62  #Demod        : 370
% 4.00/1.62  #Tautology    : 105
% 4.00/1.62  #SimpNegUnit  : 3
% 4.00/1.62  #BackRed      : 6
% 4.00/1.62  
% 4.00/1.62  #Partial instantiations: 0
% 4.00/1.62  #Strategies tried      : 1
% 4.00/1.62  
% 4.00/1.62  Timing (in seconds)
% 4.00/1.62  ----------------------
% 4.00/1.62  Preprocessing        : 0.42
% 4.00/1.62  Parsing              : 0.21
% 4.00/1.62  CNF conversion       : 0.06
% 4.00/1.62  Main loop            : 0.41
% 4.00/1.62  Inferencing          : 0.14
% 4.00/1.62  Reduction            : 0.14
% 4.00/1.62  Demodulation         : 0.11
% 4.00/1.62  BG Simplification    : 0.02
% 4.00/1.62  Subsumption          : 0.08
% 4.00/1.62  Abstraction          : 0.02
% 4.00/1.62  MUC search           : 0.00
% 4.00/1.62  Cooper               : 0.00
% 4.00/1.62  Total                : 0.87
% 4.00/1.62  Index Insertion      : 0.00
% 4.00/1.62  Index Deletion       : 0.00
% 4.00/1.62  Index Matching       : 0.00
% 4.00/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
