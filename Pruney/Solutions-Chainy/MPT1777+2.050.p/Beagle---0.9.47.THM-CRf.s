%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:39 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.47s
% Verified   : 
% Statistics : Number of formulae       :  121 (1119 expanded)
%              Number of leaves         :   43 ( 424 expanded)
%              Depth                    :   17
%              Number of atoms          :  329 (6619 expanded)
%              Number of equality atoms :   17 ( 579 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(m1_connsp_2,type,(
    m1_connsp_2: ( $i * $i * $i ) > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff(f_263,negated_conjecture,(
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

tff(f_147,axiom,(
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

tff(f_86,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_159,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,B)
             => m1_pre_topc(C,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tsep_1)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_122,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_107,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => m1_pre_topc(B,k1_tsep_1(A,B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_65,axiom,(
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

tff(f_214,axiom,(
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

tff(c_62,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_60,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_129,plain,(
    ! [B_434,A_435] :
      ( v2_pre_topc(B_434)
      | ~ m1_pre_topc(B_434,A_435)
      | ~ l1_pre_topc(A_435)
      | ~ v2_pre_topc(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_138,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_129])).

tff(c_145,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_138])).

tff(c_92,plain,(
    ! [B_426,A_427] :
      ( l1_pre_topc(B_426)
      | ~ m1_pre_topc(B_426,A_427)
      | ~ l1_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_101,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_92])).

tff(c_108,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_101])).

tff(c_48,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_64,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_98,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_105,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_98])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_345,plain,(
    ! [B_461,C_462,A_463] :
      ( m1_pre_topc(B_461,C_462)
      | ~ r1_tarski(u1_struct_0(B_461),u1_struct_0(C_462))
      | ~ m1_pre_topc(C_462,A_463)
      | ~ m1_pre_topc(B_461,A_463)
      | ~ l1_pre_topc(A_463)
      | ~ v2_pre_topc(A_463) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_382,plain,(
    ! [B_466,A_467] :
      ( m1_pre_topc(B_466,B_466)
      | ~ m1_pre_topc(B_466,A_467)
      | ~ l1_pre_topc(A_467)
      | ~ v2_pre_topc(A_467) ) ),
    inference(resolution,[status(thm)],[c_6,c_345])).

tff(c_392,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_382])).

tff(c_401,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_392])).

tff(c_135,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_129])).

tff(c_142,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_135])).

tff(c_52,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_164,plain,(
    ! [B_440,A_441] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_440),u1_pre_topc(B_440)),A_441)
      | ~ m1_pre_topc(B_440,A_441)
      | ~ l1_pre_topc(A_441) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_175,plain,(
    ! [A_441] :
      ( m1_pre_topc('#skF_5',A_441)
      | ~ m1_pre_topc('#skF_4',A_441)
      | ~ l1_pre_topc(A_441) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_164])).

tff(c_227,plain,(
    ! [C_447,A_448,B_449] :
      ( m1_pre_topc(C_447,A_448)
      | ~ m1_pre_topc(C_447,B_449)
      | ~ m1_pre_topc(B_449,A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_159])).

tff(c_238,plain,(
    ! [A_448,A_441] :
      ( m1_pre_topc('#skF_5',A_448)
      | ~ m1_pre_topc(A_441,A_448)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | ~ m1_pre_topc('#skF_4',A_441)
      | ~ l1_pre_topc(A_441) ) ),
    inference(resolution,[status(thm)],[c_175,c_227])).

tff(c_408,plain,
    ( m1_pre_topc('#skF_5','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_401,c_238])).

tff(c_430,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_401,c_142,c_408])).

tff(c_30,plain,(
    ! [B_34,A_32] :
      ( r1_tarski(u1_struct_0(B_34),u1_struct_0(A_32))
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_146,plain,(
    ! [B_436,A_437] :
      ( r1_tarski(u1_struct_0(B_436),u1_struct_0(A_437))
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_306,plain,(
    ! [B_457,A_458] :
      ( u1_struct_0(B_457) = u1_struct_0(A_458)
      | ~ r1_tarski(u1_struct_0(A_458),u1_struct_0(B_457))
      | ~ m1_pre_topc(B_457,A_458)
      | ~ l1_pre_topc(A_458) ) ),
    inference(resolution,[status(thm)],[c_146,c_2])).

tff(c_314,plain,(
    ! [B_34,A_32] :
      ( u1_struct_0(B_34) = u1_struct_0(A_32)
      | ~ m1_pre_topc(A_32,B_34)
      | ~ l1_pre_topc(B_34)
      | ~ m1_pre_topc(B_34,A_32)
      | ~ l1_pre_topc(A_32) ) ),
    inference(resolution,[status(thm)],[c_30,c_306])).

tff(c_502,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_430,c_314])).

tff(c_525,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_105,c_502])).

tff(c_580,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_525])).

tff(c_776,plain,(
    ! [A_482,B_483] :
      ( k1_tsep_1(A_482,B_483,B_483) = g1_pre_topc(u1_struct_0(B_483),u1_pre_topc(B_483))
      | ~ m1_pre_topc(B_483,A_482)
      | v2_struct_0(B_483)
      | ~ l1_pre_topc(A_482)
      | ~ v2_pre_topc(A_482)
      | v2_struct_0(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_782,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_4','#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_401,c_776])).

tff(c_805,plain,
    ( k1_tsep_1('#skF_4','#skF_4','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_105,c_52,c_782])).

tff(c_806,plain,(
    k1_tsep_1('#skF_4','#skF_4','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_805])).

tff(c_863,plain,(
    ! [B_484,A_485,C_486] :
      ( m1_pre_topc(B_484,k1_tsep_1(A_485,B_484,C_486))
      | ~ m1_pre_topc(C_486,A_485)
      | v2_struct_0(C_486)
      | ~ m1_pre_topc(B_484,A_485)
      | v2_struct_0(B_484)
      | ~ l1_pre_topc(A_485)
      | ~ v2_pre_topc(A_485)
      | v2_struct_0(A_485) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_903,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_806,c_863])).

tff(c_931,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_105,c_401,c_401,c_903])).

tff(c_933,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_580,c_931])).

tff(c_934,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_connsp_2('#skF_1'(A_15,B_16),A_15,B_16)
      | ~ m1_subset_1(B_16,u1_struct_0(A_15))
      | ~ l1_pre_topc(A_15)
      | ~ v2_pre_topc(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1041,plain,(
    ! [C_487,A_488,B_489] :
      ( m1_subset_1(C_487,k1_zfmisc_1(u1_struct_0(A_488)))
      | ~ m1_connsp_2(C_487,A_488,B_489)
      | ~ m1_subset_1(B_489,u1_struct_0(A_488))
      | ~ l1_pre_topc(A_488)
      | ~ v2_pre_topc(A_488)
      | v2_struct_0(A_488) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1964,plain,(
    ! [A_528,B_529] :
      ( m1_subset_1('#skF_1'(A_528,B_529),k1_zfmisc_1(u1_struct_0(A_528)))
      | ~ m1_subset_1(B_529,u1_struct_0(A_528))
      | ~ l1_pre_topc(A_528)
      | ~ v2_pre_topc(A_528)
      | v2_struct_0(A_528) ) ),
    inference(resolution,[status(thm)],[c_18,c_1041])).

tff(c_1973,plain,(
    ! [B_529] :
      ( m1_subset_1('#skF_1'('#skF_5',B_529),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_529,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_934,c_1964])).

tff(c_1978,plain,(
    ! [B_529] :
      ( m1_subset_1('#skF_1'('#skF_5',B_529),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_529,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_108,c_934,c_1973])).

tff(c_1980,plain,(
    ! [B_530] :
      ( m1_subset_1('#skF_1'('#skF_5',B_530),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_530,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_1978])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1985,plain,(
    ! [B_531] :
      ( r1_tarski('#skF_1'('#skF_5',B_531),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_531,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1980,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_46,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_42,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_80,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_42])).

tff(c_70,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_68,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_58,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_56,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_992,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_56])).

tff(c_54,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_991,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_934,c_54])).

tff(c_935,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_525])).

tff(c_44,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_263])).

tff(c_1424,plain,(
    ! [F_505,C_500,A_503,D_501,E_504,B_502,H_499] :
      ( r1_tmap_1(D_501,B_502,E_504,H_499)
      | ~ r1_tmap_1(C_500,B_502,k3_tmap_1(A_503,B_502,D_501,C_500,E_504),H_499)
      | ~ m1_connsp_2(F_505,D_501,H_499)
      | ~ r1_tarski(F_505,u1_struct_0(C_500))
      | ~ m1_subset_1(H_499,u1_struct_0(C_500))
      | ~ m1_subset_1(H_499,u1_struct_0(D_501))
      | ~ m1_subset_1(F_505,k1_zfmisc_1(u1_struct_0(D_501)))
      | ~ m1_pre_topc(C_500,D_501)
      | ~ m1_subset_1(E_504,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_501),u1_struct_0(B_502))))
      | ~ v1_funct_2(E_504,u1_struct_0(D_501),u1_struct_0(B_502))
      | ~ v1_funct_1(E_504)
      | ~ m1_pre_topc(D_501,A_503)
      | v2_struct_0(D_501)
      | ~ m1_pre_topc(C_500,A_503)
      | v2_struct_0(C_500)
      | ~ l1_pre_topc(B_502)
      | ~ v2_pre_topc(B_502)
      | v2_struct_0(B_502)
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_214])).

tff(c_1426,plain,(
    ! [F_505] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_505,'#skF_5','#skF_8')
      | ~ r1_tarski(F_505,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_505,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_44,c_1424])).

tff(c_1429,plain,(
    ! [F_505] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_505,'#skF_5','#skF_8')
      | ~ r1_tarski(F_505,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_505,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_70,c_68,c_64,c_60,c_58,c_992,c_934,c_991,c_934,c_935,c_934,c_48,c_934,c_48,c_1426])).

tff(c_1469,plain,(
    ! [F_507] :
      ( ~ m1_connsp_2(F_507,'#skF_5','#skF_8')
      | ~ r1_tarski(F_507,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_507,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_72,c_66,c_62,c_80,c_1429])).

tff(c_1474,plain,(
    ! [A_3] :
      ( ~ m1_connsp_2(A_3,'#skF_5','#skF_8')
      | ~ r1_tarski(A_3,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1469])).

tff(c_1993,plain,(
    ! [B_532] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_532),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_532,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1985,c_1474])).

tff(c_1997,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_18,c_1993])).

tff(c_2000,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_108,c_48,c_934,c_48,c_1997])).

tff(c_2002,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_2000])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:16:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.76  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.77  
% 4.47/1.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.77  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.47/1.77  
% 4.47/1.77  %Foreground sorts:
% 4.47/1.77  
% 4.47/1.77  
% 4.47/1.77  %Background operators:
% 4.47/1.77  
% 4.47/1.77  
% 4.47/1.77  %Foreground operators:
% 4.47/1.77  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.47/1.77  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.47/1.77  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.47/1.77  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.47/1.77  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.47/1.77  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.47/1.77  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.47/1.77  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.47/1.77  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.47/1.77  tff('#skF_7', type, '#skF_7': $i).
% 4.47/1.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.47/1.77  tff('#skF_5', type, '#skF_5': $i).
% 4.47/1.77  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.47/1.77  tff('#skF_6', type, '#skF_6': $i).
% 4.47/1.77  tff('#skF_2', type, '#skF_2': $i).
% 4.47/1.77  tff('#skF_3', type, '#skF_3': $i).
% 4.47/1.77  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 4.47/1.77  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.47/1.77  tff('#skF_8', type, '#skF_8': $i).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.47/1.77  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.47/1.77  tff('#skF_4', type, '#skF_4': $i).
% 4.47/1.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.47/1.77  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.47/1.77  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.47/1.77  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.47/1.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.47/1.77  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.47/1.77  
% 4.47/1.79  tff(f_263, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.47/1.79  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.47/1.79  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.47/1.79  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.47/1.79  tff(f_147, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.47/1.79  tff(f_86, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 4.47/1.79  tff(f_159, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, B) => m1_pre_topc(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tsep_1)).
% 4.47/1.79  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.47/1.79  tff(f_122, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 4.47/1.79  tff(f_107, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 4.47/1.79  tff(f_77, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.47/1.79  tff(f_65, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.47/1.79  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.47/1.79  tff(f_214, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.47/1.79  tff(c_62, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_60, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_129, plain, (![B_434, A_435]: (v2_pre_topc(B_434) | ~m1_pre_topc(B_434, A_435) | ~l1_pre_topc(A_435) | ~v2_pre_topc(A_435))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.47/1.79  tff(c_138, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_129])).
% 4.47/1.79  tff(c_145, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_138])).
% 4.47/1.79  tff(c_92, plain, (![B_426, A_427]: (l1_pre_topc(B_426) | ~m1_pre_topc(B_426, A_427) | ~l1_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.47/1.79  tff(c_101, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_60, c_92])).
% 4.47/1.79  tff(c_108, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_101])).
% 4.47/1.79  tff(c_48, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_66, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_64, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_98, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_92])).
% 4.47/1.79  tff(c_105, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_98])).
% 4.47/1.79  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.47/1.79  tff(c_345, plain, (![B_461, C_462, A_463]: (m1_pre_topc(B_461, C_462) | ~r1_tarski(u1_struct_0(B_461), u1_struct_0(C_462)) | ~m1_pre_topc(C_462, A_463) | ~m1_pre_topc(B_461, A_463) | ~l1_pre_topc(A_463) | ~v2_pre_topc(A_463))), inference(cnfTransformation, [status(thm)], [f_147])).
% 4.47/1.79  tff(c_382, plain, (![B_466, A_467]: (m1_pre_topc(B_466, B_466) | ~m1_pre_topc(B_466, A_467) | ~l1_pre_topc(A_467) | ~v2_pre_topc(A_467))), inference(resolution, [status(thm)], [c_6, c_345])).
% 4.47/1.79  tff(c_392, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_382])).
% 4.47/1.79  tff(c_401, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_392])).
% 4.47/1.79  tff(c_135, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_64, c_129])).
% 4.47/1.79  tff(c_142, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_135])).
% 4.47/1.79  tff(c_52, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_164, plain, (![B_440, A_441]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_440), u1_pre_topc(B_440)), A_441) | ~m1_pre_topc(B_440, A_441) | ~l1_pre_topc(A_441))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.47/1.79  tff(c_175, plain, (![A_441]: (m1_pre_topc('#skF_5', A_441) | ~m1_pre_topc('#skF_4', A_441) | ~l1_pre_topc(A_441))), inference(superposition, [status(thm), theory('equality')], [c_52, c_164])).
% 4.47/1.79  tff(c_227, plain, (![C_447, A_448, B_449]: (m1_pre_topc(C_447, A_448) | ~m1_pre_topc(C_447, B_449) | ~m1_pre_topc(B_449, A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448))), inference(cnfTransformation, [status(thm)], [f_159])).
% 4.47/1.79  tff(c_238, plain, (![A_448, A_441]: (m1_pre_topc('#skF_5', A_448) | ~m1_pre_topc(A_441, A_448) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | ~m1_pre_topc('#skF_4', A_441) | ~l1_pre_topc(A_441))), inference(resolution, [status(thm)], [c_175, c_227])).
% 4.47/1.79  tff(c_408, plain, (m1_pre_topc('#skF_5', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_401, c_238])).
% 4.47/1.79  tff(c_430, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_401, c_142, c_408])).
% 4.47/1.79  tff(c_30, plain, (![B_34, A_32]: (r1_tarski(u1_struct_0(B_34), u1_struct_0(A_32)) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.47/1.79  tff(c_146, plain, (![B_436, A_437]: (r1_tarski(u1_struct_0(B_436), u1_struct_0(A_437)) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437))), inference(cnfTransformation, [status(thm)], [f_133])).
% 4.47/1.79  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.47/1.79  tff(c_306, plain, (![B_457, A_458]: (u1_struct_0(B_457)=u1_struct_0(A_458) | ~r1_tarski(u1_struct_0(A_458), u1_struct_0(B_457)) | ~m1_pre_topc(B_457, A_458) | ~l1_pre_topc(A_458))), inference(resolution, [status(thm)], [c_146, c_2])).
% 4.47/1.79  tff(c_314, plain, (![B_34, A_32]: (u1_struct_0(B_34)=u1_struct_0(A_32) | ~m1_pre_topc(A_32, B_34) | ~l1_pre_topc(B_34) | ~m1_pre_topc(B_34, A_32) | ~l1_pre_topc(A_32))), inference(resolution, [status(thm)], [c_30, c_306])).
% 4.47/1.79  tff(c_502, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5') | ~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_430, c_314])).
% 4.47/1.79  tff(c_525, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_108, c_105, c_502])).
% 4.47/1.79  tff(c_580, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_525])).
% 4.47/1.79  tff(c_776, plain, (![A_482, B_483]: (k1_tsep_1(A_482, B_483, B_483)=g1_pre_topc(u1_struct_0(B_483), u1_pre_topc(B_483)) | ~m1_pre_topc(B_483, A_482) | v2_struct_0(B_483) | ~l1_pre_topc(A_482) | ~v2_pre_topc(A_482) | v2_struct_0(A_482))), inference(cnfTransformation, [status(thm)], [f_122])).
% 4.47/1.79  tff(c_782, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_4', '#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_401, c_776])).
% 4.47/1.79  tff(c_805, plain, (k1_tsep_1('#skF_4', '#skF_4', '#skF_4')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_105, c_52, c_782])).
% 4.47/1.79  tff(c_806, plain, (k1_tsep_1('#skF_4', '#skF_4', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_66, c_805])).
% 4.47/1.79  tff(c_863, plain, (![B_484, A_485, C_486]: (m1_pre_topc(B_484, k1_tsep_1(A_485, B_484, C_486)) | ~m1_pre_topc(C_486, A_485) | v2_struct_0(C_486) | ~m1_pre_topc(B_484, A_485) | v2_struct_0(B_484) | ~l1_pre_topc(A_485) | ~v2_pre_topc(A_485) | v2_struct_0(A_485))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.47/1.79  tff(c_903, plain, (m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_806, c_863])).
% 4.47/1.79  tff(c_931, plain, (m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_105, c_401, c_401, c_903])).
% 4.47/1.79  tff(c_933, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_580, c_931])).
% 4.47/1.79  tff(c_934, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_525])).
% 4.47/1.79  tff(c_18, plain, (![A_15, B_16]: (m1_connsp_2('#skF_1'(A_15, B_16), A_15, B_16) | ~m1_subset_1(B_16, u1_struct_0(A_15)) | ~l1_pre_topc(A_15) | ~v2_pre_topc(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.47/1.79  tff(c_1041, plain, (![C_487, A_488, B_489]: (m1_subset_1(C_487, k1_zfmisc_1(u1_struct_0(A_488))) | ~m1_connsp_2(C_487, A_488, B_489) | ~m1_subset_1(B_489, u1_struct_0(A_488)) | ~l1_pre_topc(A_488) | ~v2_pre_topc(A_488) | v2_struct_0(A_488))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.47/1.79  tff(c_1964, plain, (![A_528, B_529]: (m1_subset_1('#skF_1'(A_528, B_529), k1_zfmisc_1(u1_struct_0(A_528))) | ~m1_subset_1(B_529, u1_struct_0(A_528)) | ~l1_pre_topc(A_528) | ~v2_pre_topc(A_528) | v2_struct_0(A_528))), inference(resolution, [status(thm)], [c_18, c_1041])).
% 4.47/1.79  tff(c_1973, plain, (![B_529]: (m1_subset_1('#skF_1'('#skF_5', B_529), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_529, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_934, c_1964])).
% 4.47/1.79  tff(c_1978, plain, (![B_529]: (m1_subset_1('#skF_1'('#skF_5', B_529), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_529, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_145, c_108, c_934, c_1973])).
% 4.47/1.79  tff(c_1980, plain, (![B_530]: (m1_subset_1('#skF_1'('#skF_5', B_530), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_530, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_62, c_1978])).
% 4.47/1.79  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.79  tff(c_1985, plain, (![B_531]: (r1_tarski('#skF_1'('#skF_5', B_531), u1_struct_0('#skF_4')) | ~m1_subset_1(B_531, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1980, c_8])).
% 4.47/1.79  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.47/1.79  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_46, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_42, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_80, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_42])).
% 4.47/1.79  tff(c_70, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_68, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_58, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_56, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_992, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_56])).
% 4.47/1.79  tff(c_54, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_991, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_934, c_54])).
% 4.47/1.79  tff(c_935, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_525])).
% 4.47/1.79  tff(c_44, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_263])).
% 4.47/1.79  tff(c_1424, plain, (![F_505, C_500, A_503, D_501, E_504, B_502, H_499]: (r1_tmap_1(D_501, B_502, E_504, H_499) | ~r1_tmap_1(C_500, B_502, k3_tmap_1(A_503, B_502, D_501, C_500, E_504), H_499) | ~m1_connsp_2(F_505, D_501, H_499) | ~r1_tarski(F_505, u1_struct_0(C_500)) | ~m1_subset_1(H_499, u1_struct_0(C_500)) | ~m1_subset_1(H_499, u1_struct_0(D_501)) | ~m1_subset_1(F_505, k1_zfmisc_1(u1_struct_0(D_501))) | ~m1_pre_topc(C_500, D_501) | ~m1_subset_1(E_504, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_501), u1_struct_0(B_502)))) | ~v1_funct_2(E_504, u1_struct_0(D_501), u1_struct_0(B_502)) | ~v1_funct_1(E_504) | ~m1_pre_topc(D_501, A_503) | v2_struct_0(D_501) | ~m1_pre_topc(C_500, A_503) | v2_struct_0(C_500) | ~l1_pre_topc(B_502) | ~v2_pre_topc(B_502) | v2_struct_0(B_502) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(cnfTransformation, [status(thm)], [f_214])).
% 4.47/1.79  tff(c_1426, plain, (![F_505]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_505, '#skF_5', '#skF_8') | ~r1_tarski(F_505, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_505, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_44, c_1424])).
% 4.47/1.79  tff(c_1429, plain, (![F_505]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_505, '#skF_5', '#skF_8') | ~r1_tarski(F_505, u1_struct_0('#skF_4')) | ~m1_subset_1(F_505, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_70, c_68, c_64, c_60, c_58, c_992, c_934, c_991, c_934, c_935, c_934, c_48, c_934, c_48, c_1426])).
% 4.47/1.79  tff(c_1469, plain, (![F_507]: (~m1_connsp_2(F_507, '#skF_5', '#skF_8') | ~r1_tarski(F_507, u1_struct_0('#skF_4')) | ~m1_subset_1(F_507, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_78, c_72, c_66, c_62, c_80, c_1429])).
% 4.47/1.79  tff(c_1474, plain, (![A_3]: (~m1_connsp_2(A_3, '#skF_5', '#skF_8') | ~r1_tarski(A_3, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_1469])).
% 4.47/1.79  tff(c_1993, plain, (![B_532]: (~m1_connsp_2('#skF_1'('#skF_5', B_532), '#skF_5', '#skF_8') | ~m1_subset_1(B_532, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1985, c_1474])).
% 4.47/1.79  tff(c_1997, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_18, c_1993])).
% 4.47/1.79  tff(c_2000, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_108, c_48, c_934, c_48, c_1997])).
% 4.47/1.79  tff(c_2002, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_2000])).
% 4.47/1.79  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.47/1.79  
% 4.47/1.79  Inference rules
% 4.47/1.79  ----------------------
% 4.47/1.79  #Ref     : 0
% 4.47/1.79  #Sup     : 396
% 4.47/1.79  #Fact    : 0
% 4.47/1.79  #Define  : 0
% 4.47/1.79  #Split   : 5
% 4.47/1.79  #Chain   : 0
% 4.47/1.79  #Close   : 0
% 4.47/1.79  
% 4.47/1.79  Ordering : KBO
% 4.47/1.79  
% 4.47/1.79  Simplification rules
% 4.47/1.79  ----------------------
% 4.47/1.79  #Subsume      : 63
% 4.47/1.79  #Demod        : 557
% 4.47/1.79  #Tautology    : 184
% 4.47/1.79  #SimpNegUnit  : 43
% 4.47/1.79  #BackRed      : 14
% 4.47/1.79  
% 4.47/1.79  #Partial instantiations: 0
% 4.47/1.79  #Strategies tried      : 1
% 4.47/1.79  
% 4.47/1.79  Timing (in seconds)
% 4.47/1.79  ----------------------
% 4.47/1.79  Preprocessing        : 0.42
% 4.47/1.79  Parsing              : 0.21
% 4.47/1.79  CNF conversion       : 0.06
% 4.47/1.79  Main loop            : 0.61
% 4.47/1.79  Inferencing          : 0.18
% 4.47/1.79  Reduction            : 0.22
% 4.47/1.79  Demodulation         : 0.16
% 4.47/1.79  BG Simplification    : 0.03
% 4.47/1.79  Subsumption          : 0.14
% 4.47/1.79  Abstraction          : 0.03
% 4.47/1.79  MUC search           : 0.00
% 4.47/1.79  Cooper               : 0.00
% 4.47/1.79  Total                : 1.07
% 4.47/1.79  Index Insertion      : 0.00
% 4.47/1.79  Index Deletion       : 0.00
% 4.47/1.79  Index Matching       : 0.00
% 4.47/1.79  BG Taut test         : 0.00
%------------------------------------------------------------------------------
