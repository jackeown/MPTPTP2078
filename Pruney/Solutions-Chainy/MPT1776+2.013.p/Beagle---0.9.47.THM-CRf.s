%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:31 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :  114 ( 271 expanded)
%              Number of leaves         :   39 ( 120 expanded)
%              Depth                    :   12
%              Number of atoms          :  349 (2009 expanded)
%              Number of equality atoms :    5 (  84 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_258,negated_conjecture,(
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

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_49,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_88,axiom,(
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

tff(f_155,axiom,(
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

tff(f_64,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_1132,plain,(
    ! [B_578,A_579] :
      ( l1_pre_topc(B_578)
      | ~ m1_pre_topc(B_578,A_579)
      | ~ l1_pre_topc(A_579) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_1135,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1132])).

tff(c_1144,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1135])).

tff(c_22,plain,(
    ! [A_8] :
      ( l1_struct_0(A_8)
      | ~ l1_pre_topc(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_42,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_44,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_52,plain,(
    v1_tsep_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_118,plain,(
    ! [B_412,A_413] :
      ( l1_pre_topc(B_412)
      | ~ m1_pre_topc(B_412,A_413)
      | ~ l1_pre_topc(A_413) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_127,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_118])).

tff(c_134,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_127])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_32,plain,(
    ! [B_22,A_20] :
      ( m1_subset_1(u1_struct_0(B_22),k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_141,plain,(
    ! [B_416,A_417] :
      ( r2_hidden(B_416,A_417)
      | ~ m1_subset_1(B_416,A_417)
      | v1_xboole_0(A_417) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_167,plain,(
    ! [B_424,A_425] :
      ( r1_tarski(B_424,A_425)
      | ~ m1_subset_1(B_424,k1_zfmisc_1(A_425))
      | v1_xboole_0(k1_zfmisc_1(A_425)) ) ),
    inference(resolution,[status(thm)],[c_141,c_2])).

tff(c_182,plain,(
    ! [B_22,A_20] :
      ( r1_tarski(u1_struct_0(B_22),u1_struct_0(A_20))
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_20)))
      | ~ m1_pre_topc(B_22,A_20)
      | ~ l1_pre_topc(A_20) ) ),
    inference(resolution,[status(thm)],[c_32,c_167])).

tff(c_432,plain,(
    ! [B_469,C_470,A_471] :
      ( v1_tsep_1(B_469,C_470)
      | ~ r1_tarski(u1_struct_0(B_469),u1_struct_0(C_470))
      | ~ m1_pre_topc(C_470,A_471)
      | v2_struct_0(C_470)
      | ~ m1_pre_topc(B_469,A_471)
      | ~ v1_tsep_1(B_469,A_471)
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_483,plain,(
    ! [B_482,A_483,A_484] :
      ( v1_tsep_1(B_482,A_483)
      | ~ m1_pre_topc(A_483,A_484)
      | v2_struct_0(A_483)
      | ~ m1_pre_topc(B_482,A_484)
      | ~ v1_tsep_1(B_482,A_484)
      | ~ l1_pre_topc(A_484)
      | ~ v2_pre_topc(A_484)
      | v2_struct_0(A_484)
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_483)))
      | ~ m1_pre_topc(B_482,A_483)
      | ~ l1_pre_topc(A_483) ) ),
    inference(resolution,[status(thm)],[c_182,c_432])).

tff(c_495,plain,(
    ! [B_482] :
      ( v1_tsep_1(B_482,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_482,'#skF_4')
      | ~ v1_tsep_1(B_482,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_482,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_483])).

tff(c_518,plain,(
    ! [B_482] :
      ( v1_tsep_1(B_482,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_482,'#skF_4')
      | ~ v1_tsep_1(B_482,'#skF_4')
      | v2_struct_0('#skF_4')
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_482,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_70,c_68,c_495])).

tff(c_519,plain,(
    ! [B_482] :
      ( v1_tsep_1(B_482,'#skF_6')
      | ~ m1_pre_topc(B_482,'#skF_4')
      | ~ v1_tsep_1(B_482,'#skF_4')
      | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))
      | ~ m1_pre_topc(B_482,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_518])).

tff(c_546,plain,(
    v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_157,plain,(
    ! [B_420,A_421] :
      ( m1_subset_1(u1_struct_0(B_420),k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_20,plain,(
    ! [B_7,A_6] :
      ( v1_xboole_0(B_7)
      | ~ m1_subset_1(B_7,A_6)
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_161,plain,(
    ! [B_420,A_421] :
      ( v1_xboole_0(u1_struct_0(B_420))
      | ~ v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_421)))
      | ~ m1_pre_topc(B_420,A_421)
      | ~ l1_pre_topc(A_421) ) ),
    inference(resolution,[status(thm)],[c_157,c_20])).

tff(c_566,plain,(
    ! [B_420] :
      ( v1_xboole_0(u1_struct_0(B_420))
      | ~ m1_pre_topc(B_420,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_546,c_161])).

tff(c_570,plain,(
    ! [B_492] :
      ( v1_xboole_0(u1_struct_0(B_492))
      | ~ m1_pre_topc(B_492,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_566])).

tff(c_96,plain,(
    ! [B_405,A_406] :
      ( v1_xboole_0(B_405)
      | ~ m1_subset_1(B_405,A_406)
      | ~ v1_xboole_0(A_406) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_103,plain,
    ( v1_xboole_0('#skF_8')
    | ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(resolution,[status(thm)],[c_90,c_96])).

tff(c_110,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_576,plain,(
    ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_570,c_110])).

tff(c_584,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_576])).

tff(c_638,plain,(
    ! [B_497] :
      ( v1_tsep_1(B_497,'#skF_6')
      | ~ m1_pre_topc(B_497,'#skF_4')
      | ~ v1_tsep_1(B_497,'#skF_4')
      | ~ m1_pre_topc(B_497,'#skF_6') ) ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_187,plain,(
    r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_88])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_89,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_80])).

tff(c_237,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_89])).

tff(c_76,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_56,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_521,plain,(
    ! [C_488,D_487,A_489,B_490,G_486,E_485] :
      ( r1_tmap_1(D_487,B_490,E_485,G_486)
      | ~ r1_tmap_1(C_488,B_490,k3_tmap_1(A_489,B_490,D_487,C_488,E_485),G_486)
      | ~ m1_subset_1(G_486,u1_struct_0(C_488))
      | ~ m1_subset_1(G_486,u1_struct_0(D_487))
      | ~ m1_pre_topc(C_488,D_487)
      | ~ v1_tsep_1(C_488,D_487)
      | ~ m1_subset_1(E_485,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_487),u1_struct_0(B_490))))
      | ~ v1_funct_2(E_485,u1_struct_0(D_487),u1_struct_0(B_490))
      | ~ v1_funct_1(E_485)
      | ~ m1_pre_topc(D_487,A_489)
      | v2_struct_0(D_487)
      | ~ m1_pre_topc(C_488,A_489)
      | v2_struct_0(C_488)
      | ~ l1_pre_topc(B_490)
      | ~ v2_pre_topc(B_490)
      | v2_struct_0(B_490)
      | ~ l1_pre_topc(A_489)
      | ~ v2_pre_topc(A_489)
      | v2_struct_0(A_489) ) ),
    inference(cnfTransformation,[status(thm)],[f_205])).

tff(c_523,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | v2_struct_0('#skF_6')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_187,c_521])).

tff(c_526,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ v1_tsep_1('#skF_5','#skF_6')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_76,c_74,c_64,c_60,c_58,c_56,c_54,c_48,c_46,c_90,c_523])).

tff(c_527,plain,(
    ~ v1_tsep_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_78,c_66,c_62,c_237,c_526])).

tff(c_641,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_638,c_527])).

tff(c_645,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_64,c_641])).

tff(c_646,plain,(
    r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_953,plain,(
    ! [D_555,G_553,B_551,E_552,C_556,A_554] :
      ( r1_tmap_1(D_555,B_551,k3_tmap_1(A_554,B_551,C_556,D_555,E_552),G_553)
      | ~ r1_tmap_1(C_556,B_551,E_552,G_553)
      | ~ m1_pre_topc(D_555,C_556)
      | ~ m1_subset_1(G_553,u1_struct_0(D_555))
      | ~ m1_subset_1(G_553,u1_struct_0(C_556))
      | ~ m1_subset_1(E_552,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_556),u1_struct_0(B_551))))
      | ~ v1_funct_2(E_552,u1_struct_0(C_556),u1_struct_0(B_551))
      | ~ v1_funct_1(E_552)
      | ~ m1_pre_topc(D_555,A_554)
      | v2_struct_0(D_555)
      | ~ m1_pre_topc(C_556,A_554)
      | v2_struct_0(C_556)
      | ~ l1_pre_topc(B_551)
      | ~ v2_pre_topc(B_551)
      | v2_struct_0(B_551)
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(cnfTransformation,[status(thm)],[f_155])).

tff(c_970,plain,(
    ! [D_555,A_554,G_553] :
      ( r1_tmap_1(D_555,'#skF_3',k3_tmap_1(A_554,'#skF_3','#skF_6',D_555,'#skF_7'),G_553)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_553)
      | ~ m1_pre_topc(D_555,'#skF_6')
      | ~ m1_subset_1(G_553,u1_struct_0(D_555))
      | ~ m1_subset_1(G_553,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_555,A_554)
      | v2_struct_0(D_555)
      | ~ m1_pre_topc('#skF_6',A_554)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(resolution,[status(thm)],[c_54,c_953])).

tff(c_978,plain,(
    ! [D_555,A_554,G_553] :
      ( r1_tmap_1(D_555,'#skF_3',k3_tmap_1(A_554,'#skF_3','#skF_6',D_555,'#skF_7'),G_553)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_553)
      | ~ m1_pre_topc(D_555,'#skF_6')
      | ~ m1_subset_1(G_553,u1_struct_0(D_555))
      | ~ m1_subset_1(G_553,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_555,A_554)
      | v2_struct_0(D_555)
      | ~ m1_pre_topc('#skF_6',A_554)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_554)
      | ~ v2_pre_topc(A_554)
      | v2_struct_0(A_554) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_56,c_970])).

tff(c_1103,plain,(
    ! [D_569,A_570,G_571] :
      ( r1_tmap_1(D_569,'#skF_3',k3_tmap_1(A_570,'#skF_3','#skF_6',D_569,'#skF_7'),G_571)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_571)
      | ~ m1_pre_topc(D_569,'#skF_6')
      | ~ m1_subset_1(G_571,u1_struct_0(D_569))
      | ~ m1_subset_1(G_571,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_569,A_570)
      | v2_struct_0(D_569)
      | ~ m1_pre_topc('#skF_6',A_570)
      | ~ l1_pre_topc(A_570)
      | ~ v2_pre_topc(A_570)
      | v2_struct_0(A_570) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_62,c_978])).

tff(c_647,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_88])).

tff(c_1108,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | v2_struct_0('#skF_5')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_1103,c_647])).

tff(c_1115,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_64,c_46,c_90,c_48,c_646,c_1108])).

tff(c_1117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_1115])).

tff(c_1119,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_1149,plain,(
    ! [A_580] :
      ( ~ v1_xboole_0(u1_struct_0(A_580))
      | ~ l1_struct_0(A_580)
      | v2_struct_0(A_580) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1152,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1119,c_1149])).

tff(c_1155,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1152])).

tff(c_1158,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_22,c_1155])).

tff(c_1162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1144,c_1158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:04:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.61  
% 3.80/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.61  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 3.80/1.61  
% 3.80/1.61  %Foreground sorts:
% 3.80/1.61  
% 3.80/1.61  
% 3.80/1.61  %Background operators:
% 3.80/1.61  
% 3.80/1.61  
% 3.80/1.61  %Foreground operators:
% 3.80/1.61  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.80/1.61  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.80/1.61  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.61  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.61  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.80/1.61  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.80/1.61  tff('#skF_7', type, '#skF_7': $i).
% 3.80/1.61  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.61  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.61  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.80/1.61  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.61  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.61  tff('#skF_9', type, '#skF_9': $i).
% 3.80/1.61  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.80/1.61  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.80/1.61  tff('#skF_8', type, '#skF_8': $i).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.61  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.61  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.80/1.61  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.61  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.61  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.80/1.61  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.80/1.61  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.80/1.61  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.80/1.61  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.80/1.61  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.61  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.61  
% 3.80/1.63  tff(f_258, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.80/1.63  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.80/1.63  tff(f_49, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.80/1.63  tff(f_95, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.80/1.63  tff(f_45, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.80/1.63  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.80/1.63  tff(f_88, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 3.80/1.63  tff(f_205, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.80/1.63  tff(f_155, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.80/1.63  tff(f_64, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.80/1.63  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_1132, plain, (![B_578, A_579]: (l1_pre_topc(B_578) | ~m1_pre_topc(B_578, A_579) | ~l1_pre_topc(A_579))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.63  tff(c_1135, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1132])).
% 3.80/1.63  tff(c_1144, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1135])).
% 3.80/1.63  tff(c_22, plain, (![A_8]: (l1_struct_0(A_8) | ~l1_pre_topc(A_8))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.80/1.63  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_42, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_44, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_90, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 3.80/1.63  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_52, plain, (v1_tsep_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_118, plain, (![B_412, A_413]: (l1_pre_topc(B_412) | ~m1_pre_topc(B_412, A_413) | ~l1_pre_topc(A_413))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.63  tff(c_127, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_118])).
% 3.80/1.63  tff(c_134, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_127])).
% 3.80/1.63  tff(c_62, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_32, plain, (![B_22, A_20]: (m1_subset_1(u1_struct_0(B_22), k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.80/1.63  tff(c_141, plain, (![B_416, A_417]: (r2_hidden(B_416, A_417) | ~m1_subset_1(B_416, A_417) | v1_xboole_0(A_417))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.80/1.63  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.63  tff(c_167, plain, (![B_424, A_425]: (r1_tarski(B_424, A_425) | ~m1_subset_1(B_424, k1_zfmisc_1(A_425)) | v1_xboole_0(k1_zfmisc_1(A_425)))), inference(resolution, [status(thm)], [c_141, c_2])).
% 3.80/1.63  tff(c_182, plain, (![B_22, A_20]: (r1_tarski(u1_struct_0(B_22), u1_struct_0(A_20)) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_20))) | ~m1_pre_topc(B_22, A_20) | ~l1_pre_topc(A_20))), inference(resolution, [status(thm)], [c_32, c_167])).
% 3.80/1.63  tff(c_432, plain, (![B_469, C_470, A_471]: (v1_tsep_1(B_469, C_470) | ~r1_tarski(u1_struct_0(B_469), u1_struct_0(C_470)) | ~m1_pre_topc(C_470, A_471) | v2_struct_0(C_470) | ~m1_pre_topc(B_469, A_471) | ~v1_tsep_1(B_469, A_471) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.80/1.63  tff(c_483, plain, (![B_482, A_483, A_484]: (v1_tsep_1(B_482, A_483) | ~m1_pre_topc(A_483, A_484) | v2_struct_0(A_483) | ~m1_pre_topc(B_482, A_484) | ~v1_tsep_1(B_482, A_484) | ~l1_pre_topc(A_484) | ~v2_pre_topc(A_484) | v2_struct_0(A_484) | v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_483))) | ~m1_pre_topc(B_482, A_483) | ~l1_pre_topc(A_483))), inference(resolution, [status(thm)], [c_182, c_432])).
% 3.80/1.63  tff(c_495, plain, (![B_482]: (v1_tsep_1(B_482, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_482, '#skF_4') | ~v1_tsep_1(B_482, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_482, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_483])).
% 3.80/1.63  tff(c_518, plain, (![B_482]: (v1_tsep_1(B_482, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_482, '#skF_4') | ~v1_tsep_1(B_482, '#skF_4') | v2_struct_0('#skF_4') | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_482, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_70, c_68, c_495])).
% 3.80/1.63  tff(c_519, plain, (![B_482]: (v1_tsep_1(B_482, '#skF_6') | ~m1_pre_topc(B_482, '#skF_4') | ~v1_tsep_1(B_482, '#skF_4') | v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6'))) | ~m1_pre_topc(B_482, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_518])).
% 3.80/1.63  tff(c_546, plain, (v1_xboole_0(k1_zfmisc_1(u1_struct_0('#skF_6')))), inference(splitLeft, [status(thm)], [c_519])).
% 3.80/1.63  tff(c_157, plain, (![B_420, A_421]: (m1_subset_1(u1_struct_0(B_420), k1_zfmisc_1(u1_struct_0(A_421))) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421))), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.80/1.63  tff(c_20, plain, (![B_7, A_6]: (v1_xboole_0(B_7) | ~m1_subset_1(B_7, A_6) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.80/1.63  tff(c_161, plain, (![B_420, A_421]: (v1_xboole_0(u1_struct_0(B_420)) | ~v1_xboole_0(k1_zfmisc_1(u1_struct_0(A_421))) | ~m1_pre_topc(B_420, A_421) | ~l1_pre_topc(A_421))), inference(resolution, [status(thm)], [c_157, c_20])).
% 3.80/1.63  tff(c_566, plain, (![B_420]: (v1_xboole_0(u1_struct_0(B_420)) | ~m1_pre_topc(B_420, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_546, c_161])).
% 3.80/1.63  tff(c_570, plain, (![B_492]: (v1_xboole_0(u1_struct_0(B_492)) | ~m1_pre_topc(B_492, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_566])).
% 3.80/1.63  tff(c_96, plain, (![B_405, A_406]: (v1_xboole_0(B_405) | ~m1_subset_1(B_405, A_406) | ~v1_xboole_0(A_406))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.80/1.63  tff(c_103, plain, (v1_xboole_0('#skF_8') | ~v1_xboole_0(u1_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_90, c_96])).
% 3.80/1.63  tff(c_110, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_103])).
% 3.80/1.63  tff(c_576, plain, (~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_570, c_110])).
% 3.80/1.63  tff(c_584, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_576])).
% 3.80/1.63  tff(c_638, plain, (![B_497]: (v1_tsep_1(B_497, '#skF_6') | ~m1_pre_topc(B_497, '#skF_4') | ~v1_tsep_1(B_497, '#skF_4') | ~m1_pre_topc(B_497, '#skF_6'))), inference(splitRight, [status(thm)], [c_519])).
% 3.80/1.63  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_86, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_88, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_86])).
% 3.80/1.63  tff(c_187, plain, (r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitLeft, [status(thm)], [c_88])).
% 3.80/1.63  tff(c_80, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_89, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_80])).
% 3.80/1.63  tff(c_237, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_89])).
% 3.80/1.63  tff(c_76, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_56, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.80/1.63  tff(c_521, plain, (![C_488, D_487, A_489, B_490, G_486, E_485]: (r1_tmap_1(D_487, B_490, E_485, G_486) | ~r1_tmap_1(C_488, B_490, k3_tmap_1(A_489, B_490, D_487, C_488, E_485), G_486) | ~m1_subset_1(G_486, u1_struct_0(C_488)) | ~m1_subset_1(G_486, u1_struct_0(D_487)) | ~m1_pre_topc(C_488, D_487) | ~v1_tsep_1(C_488, D_487) | ~m1_subset_1(E_485, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_487), u1_struct_0(B_490)))) | ~v1_funct_2(E_485, u1_struct_0(D_487), u1_struct_0(B_490)) | ~v1_funct_1(E_485) | ~m1_pre_topc(D_487, A_489) | v2_struct_0(D_487) | ~m1_pre_topc(C_488, A_489) | v2_struct_0(C_488) | ~l1_pre_topc(B_490) | ~v2_pre_topc(B_490) | v2_struct_0(B_490) | ~l1_pre_topc(A_489) | ~v2_pre_topc(A_489) | v2_struct_0(A_489))), inference(cnfTransformation, [status(thm)], [f_205])).
% 3.80/1.63  tff(c_523, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_6') | ~v1_tsep_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_187, c_521])).
% 3.80/1.63  tff(c_526, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~v1_tsep_1('#skF_5', '#skF_6') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_76, c_74, c_64, c_60, c_58, c_56, c_54, c_48, c_46, c_90, c_523])).
% 3.80/1.63  tff(c_527, plain, (~v1_tsep_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_72, c_78, c_66, c_62, c_237, c_526])).
% 3.80/1.63  tff(c_641, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_tsep_1('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_638, c_527])).
% 3.80/1.63  tff(c_645, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_64, c_641])).
% 3.80/1.63  tff(c_646, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_88])).
% 3.80/1.63  tff(c_953, plain, (![D_555, G_553, B_551, E_552, C_556, A_554]: (r1_tmap_1(D_555, B_551, k3_tmap_1(A_554, B_551, C_556, D_555, E_552), G_553) | ~r1_tmap_1(C_556, B_551, E_552, G_553) | ~m1_pre_topc(D_555, C_556) | ~m1_subset_1(G_553, u1_struct_0(D_555)) | ~m1_subset_1(G_553, u1_struct_0(C_556)) | ~m1_subset_1(E_552, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_556), u1_struct_0(B_551)))) | ~v1_funct_2(E_552, u1_struct_0(C_556), u1_struct_0(B_551)) | ~v1_funct_1(E_552) | ~m1_pre_topc(D_555, A_554) | v2_struct_0(D_555) | ~m1_pre_topc(C_556, A_554) | v2_struct_0(C_556) | ~l1_pre_topc(B_551) | ~v2_pre_topc(B_551) | v2_struct_0(B_551) | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(cnfTransformation, [status(thm)], [f_155])).
% 3.80/1.63  tff(c_970, plain, (![D_555, A_554, G_553]: (r1_tmap_1(D_555, '#skF_3', k3_tmap_1(A_554, '#skF_3', '#skF_6', D_555, '#skF_7'), G_553) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_553) | ~m1_pre_topc(D_555, '#skF_6') | ~m1_subset_1(G_553, u1_struct_0(D_555)) | ~m1_subset_1(G_553, u1_struct_0('#skF_6')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_555, A_554) | v2_struct_0(D_555) | ~m1_pre_topc('#skF_6', A_554) | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(resolution, [status(thm)], [c_54, c_953])).
% 3.80/1.63  tff(c_978, plain, (![D_555, A_554, G_553]: (r1_tmap_1(D_555, '#skF_3', k3_tmap_1(A_554, '#skF_3', '#skF_6', D_555, '#skF_7'), G_553) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_553) | ~m1_pre_topc(D_555, '#skF_6') | ~m1_subset_1(G_553, u1_struct_0(D_555)) | ~m1_subset_1(G_553, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_555, A_554) | v2_struct_0(D_555) | ~m1_pre_topc('#skF_6', A_554) | v2_struct_0('#skF_6') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_554) | ~v2_pre_topc(A_554) | v2_struct_0(A_554))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_56, c_970])).
% 3.80/1.63  tff(c_1103, plain, (![D_569, A_570, G_571]: (r1_tmap_1(D_569, '#skF_3', k3_tmap_1(A_570, '#skF_3', '#skF_6', D_569, '#skF_7'), G_571) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_571) | ~m1_pre_topc(D_569, '#skF_6') | ~m1_subset_1(G_571, u1_struct_0(D_569)) | ~m1_subset_1(G_571, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_569, A_570) | v2_struct_0(D_569) | ~m1_pre_topc('#skF_6', A_570) | ~l1_pre_topc(A_570) | ~v2_pre_topc(A_570) | v2_struct_0(A_570))), inference(negUnitSimplification, [status(thm)], [c_78, c_62, c_978])).
% 3.80/1.63  tff(c_647, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_88])).
% 3.80/1.63  tff(c_1108, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_1103, c_647])).
% 3.80/1.63  tff(c_1115, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_60, c_64, c_46, c_90, c_48, c_646, c_1108])).
% 3.80/1.63  tff(c_1117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_1115])).
% 3.80/1.63  tff(c_1119, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_103])).
% 3.80/1.63  tff(c_1149, plain, (![A_580]: (~v1_xboole_0(u1_struct_0(A_580)) | ~l1_struct_0(A_580) | v2_struct_0(A_580))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.80/1.63  tff(c_1152, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1119, c_1149])).
% 3.80/1.63  tff(c_1155, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_66, c_1152])).
% 3.80/1.63  tff(c_1158, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_22, c_1155])).
% 3.80/1.63  tff(c_1162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1144, c_1158])).
% 3.80/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.80/1.63  
% 3.80/1.63  Inference rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Ref     : 0
% 3.80/1.63  #Sup     : 197
% 3.80/1.63  #Fact    : 0
% 3.80/1.63  #Define  : 0
% 3.80/1.63  #Split   : 12
% 3.80/1.63  #Chain   : 0
% 3.80/1.63  #Close   : 0
% 3.80/1.63  
% 3.80/1.63  Ordering : KBO
% 3.80/1.63  
% 3.80/1.63  Simplification rules
% 3.80/1.63  ----------------------
% 3.80/1.63  #Subsume      : 49
% 3.80/1.63  #Demod        : 196
% 3.80/1.63  #Tautology    : 62
% 3.80/1.63  #SimpNegUnit  : 29
% 3.80/1.63  #BackRed      : 0
% 3.80/1.63  
% 3.80/1.63  #Partial instantiations: 0
% 3.80/1.63  #Strategies tried      : 1
% 3.80/1.63  
% 3.80/1.63  Timing (in seconds)
% 3.80/1.63  ----------------------
% 4.18/1.63  Preprocessing        : 0.40
% 4.18/1.63  Parsing              : 0.21
% 4.18/1.63  CNF conversion       : 0.06
% 4.18/1.63  Main loop            : 0.46
% 4.18/1.64  Inferencing          : 0.17
% 4.18/1.64  Reduction            : 0.14
% 4.18/1.64  Demodulation         : 0.10
% 4.18/1.64  BG Simplification    : 0.03
% 4.18/1.64  Subsumption          : 0.10
% 4.18/1.64  Abstraction          : 0.02
% 4.18/1.64  MUC search           : 0.00
% 4.18/1.64  Cooper               : 0.00
% 4.18/1.64  Total                : 0.90
% 4.18/1.64  Index Insertion      : 0.00
% 4.18/1.64  Index Deletion       : 0.00
% 4.18/1.64  Index Matching       : 0.00
% 4.18/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
