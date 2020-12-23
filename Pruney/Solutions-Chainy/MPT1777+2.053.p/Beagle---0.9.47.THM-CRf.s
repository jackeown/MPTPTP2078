%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:39 EST 2020

% Result     : Theorem 4.15s
% Output     : CNFRefutation 4.28s
% Verified   : 
% Statistics : Number of formulae       :  121 (1118 expanded)
%              Number of leaves         :   40 ( 423 expanded)
%              Depth                    :   17
%              Number of atoms          :  326 (6982 expanded)
%              Number of equality atoms :   16 ( 612 expanded)
%              Maximal formula depth    :   29 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff(f_273,negated_conjecture,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_157,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ( r1_tarski(u1_struct_0(B),u1_struct_0(C))
              <=> m1_pre_topc(B,C) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_143,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_105,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ? [C] : m1_connsp_2(C,A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_connsp_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A)
        & m1_subset_1(B,u1_struct_0(A)) )
     => ! [C] :
          ( m1_connsp_2(C,A,B)
         => m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_connsp_2)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_224,axiom,(
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

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_122,plain,(
    ! [B_436,A_437] :
      ( v2_pre_topc(B_436)
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437)
      | ~ v2_pre_topc(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_128,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_122])).

tff(c_134,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_128])).

tff(c_89,plain,(
    ! [B_428,A_429] :
      ( l1_pre_topc(B_428)
      | ~ m1_pre_topc(B_428,A_429)
      | ~ l1_pre_topc(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_95,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_89])).

tff(c_101,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_95])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_241,plain,(
    ! [B_456,C_457,A_458] :
      ( m1_pre_topc(B_456,C_457)
      | ~ r1_tarski(u1_struct_0(B_456),u1_struct_0(C_457))
      | ~ m1_pre_topc(C_457,A_458)
      | ~ m1_pre_topc(B_456,A_458)
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_252,plain,(
    ! [B_459,A_460] :
      ( m1_pre_topc(B_459,B_459)
      | ~ m1_pre_topc(B_459,A_460)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460) ) ),
    inference(resolution,[status(thm)],[c_6,c_241])).

tff(c_258,plain,
    ( m1_pre_topc('#skF_5','#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_58,c_252])).

tff(c_265,plain,(
    m1_pre_topc('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_258])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_92,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_89])).

tff(c_98,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_92])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_135,plain,(
    ! [B_438,A_439] :
      ( m1_pre_topc(B_438,A_439)
      | ~ m1_pre_topc(B_438,g1_pre_topc(u1_struct_0(A_439),u1_pre_topc(A_439)))
      | ~ l1_pre_topc(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_138,plain,(
    ! [B_438] :
      ( m1_pre_topc(B_438,'#skF_4')
      | ~ m1_pre_topc(B_438,'#skF_5')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_135])).

tff(c_140,plain,(
    ! [B_438] :
      ( m1_pre_topc(B_438,'#skF_4')
      | ~ m1_pre_topc(B_438,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_138])).

tff(c_323,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_265,c_140])).

tff(c_30,plain,(
    ! [B_42,C_44,A_38] :
      ( r1_tarski(u1_struct_0(B_42),u1_struct_0(C_44))
      | ~ m1_pre_topc(B_42,C_44)
      | ~ m1_pre_topc(C_44,A_38)
      | ~ m1_pre_topc(B_42,A_38)
      | ~ l1_pre_topc(A_38)
      | ~ v2_pre_topc(A_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_299,plain,(
    ! [B_42] :
      ( r1_tarski(u1_struct_0(B_42),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_42,'#skF_5')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_265,c_30])).

tff(c_377,plain,(
    ! [B_462] :
      ( r1_tarski(u1_struct_0(B_462),u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(B_462,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_101,c_299])).

tff(c_195,plain,(
    ! [B_450,C_451,A_452] :
      ( r1_tarski(u1_struct_0(B_450),u1_struct_0(C_451))
      | ~ m1_pre_topc(B_450,C_451)
      | ~ m1_pre_topc(C_451,A_452)
      | ~ m1_pre_topc(B_450,A_452)
      | ~ l1_pre_topc(A_452)
      | ~ v2_pre_topc(A_452) ) ),
    inference(cnfTransformation,[status(thm)],[f_157])).

tff(c_199,plain,(
    ! [B_450] :
      ( r1_tarski(u1_struct_0(B_450),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_450,'#skF_4')
      | ~ m1_pre_topc(B_450,'#skF_2')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_62,c_195])).

tff(c_209,plain,(
    ! [B_453] :
      ( r1_tarski(u1_struct_0(B_453),u1_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_453,'#skF_4')
      | ~ m1_pre_topc(B_453,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_199])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_212,plain,(
    ! [B_453] :
      ( u1_struct_0(B_453) = u1_struct_0('#skF_4')
      | ~ r1_tarski(u1_struct_0('#skF_4'),u1_struct_0(B_453))
      | ~ m1_pre_topc(B_453,'#skF_4')
      | ~ m1_pre_topc(B_453,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_209,c_2])).

tff(c_383,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_2')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_377,c_212])).

tff(c_389,plain,
    ( u1_struct_0('#skF_5') = u1_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_323,c_383])).

tff(c_391,plain,(
    ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_125,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_122])).

tff(c_131,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_125])).

tff(c_256,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_252])).

tff(c_262,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_256])).

tff(c_489,plain,(
    ! [A_471,B_472] :
      ( k1_tsep_1(A_471,B_472,B_472) = g1_pre_topc(u1_struct_0(B_472),u1_pre_topc(B_472))
      | ~ m1_pre_topc(B_472,A_471)
      | v2_struct_0(B_472)
      | ~ l1_pre_topc(A_471)
      | ~ v2_pre_topc(A_471)
      | v2_struct_0(A_471) ) ),
    inference(cnfTransformation,[status(thm)],[f_143])).

tff(c_497,plain,
    ( g1_pre_topc(u1_struct_0('#skF_4'),u1_pre_topc('#skF_4')) = k1_tsep_1('#skF_4','#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_262,c_489])).

tff(c_517,plain,
    ( k1_tsep_1('#skF_4','#skF_4','#skF_4') = '#skF_5'
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_98,c_50,c_497])).

tff(c_518,plain,(
    k1_tsep_1('#skF_4','#skF_4','#skF_4') = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_517])).

tff(c_598,plain,(
    ! [B_475,A_476,C_477] :
      ( m1_pre_topc(B_475,k1_tsep_1(A_476,B_475,C_477))
      | ~ m1_pre_topc(C_477,A_476)
      | v2_struct_0(C_477)
      | ~ m1_pre_topc(B_475,A_476)
      | v2_struct_0(B_475)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_631,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_518,c_598])).

tff(c_656,plain,
    ( m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_98,c_262,c_262,c_631])).

tff(c_658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_391,c_656])).

tff(c_659,plain,(
    u1_struct_0('#skF_5') = u1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_connsp_2('#skF_1'(A_18,B_19),A_18,B_19)
      | ~ m1_subset_1(B_19,u1_struct_0(A_18))
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_756,plain,(
    ! [C_479,A_480,B_481] :
      ( m1_subset_1(C_479,k1_zfmisc_1(u1_struct_0(A_480)))
      | ~ m1_connsp_2(C_479,A_480,B_481)
      | ~ m1_subset_1(B_481,u1_struct_0(A_480))
      | ~ l1_pre_topc(A_480)
      | ~ v2_pre_topc(A_480)
      | v2_struct_0(A_480) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1128,plain,(
    ! [A_495,B_496] :
      ( m1_subset_1('#skF_1'(A_495,B_496),k1_zfmisc_1(u1_struct_0(A_495)))
      | ~ m1_subset_1(B_496,u1_struct_0(A_495))
      | ~ l1_pre_topc(A_495)
      | ~ v2_pre_topc(A_495)
      | v2_struct_0(A_495) ) ),
    inference(resolution,[status(thm)],[c_20,c_756])).

tff(c_1134,plain,(
    ! [B_496] :
      ( m1_subset_1('#skF_1'('#skF_5',B_496),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_496,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_659,c_1128])).

tff(c_1137,plain,(
    ! [B_496] :
      ( m1_subset_1('#skF_1'('#skF_5',B_496),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_496,u1_struct_0('#skF_4'))
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_101,c_659,c_1134])).

tff(c_1139,plain,(
    ! [B_497] :
      ( m1_subset_1('#skF_1'('#skF_5',B_497),k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1137])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1143,plain,(
    ! [B_497] :
      ( r1_tarski('#skF_1'('#skF_5',B_497),u1_struct_0('#skF_4'))
      | ~ m1_subset_1(B_497,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1139,c_8])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,k1_zfmisc_1(B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_44,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_78,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_40])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_700,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_4'),u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_54])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_699,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_3')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_659,c_52])).

tff(c_660,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_42,plain,(
    r1_tmap_1('#skF_4','#skF_3',k3_tmap_1('#skF_2','#skF_3','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_273])).

tff(c_1719,plain,(
    ! [E_528,F_532,D_527,B_531,H_533,C_530,A_529] :
      ( r1_tmap_1(D_527,B_531,E_528,H_533)
      | ~ r1_tmap_1(C_530,B_531,k3_tmap_1(A_529,B_531,D_527,C_530,E_528),H_533)
      | ~ m1_connsp_2(F_532,D_527,H_533)
      | ~ r1_tarski(F_532,u1_struct_0(C_530))
      | ~ m1_subset_1(H_533,u1_struct_0(C_530))
      | ~ m1_subset_1(H_533,u1_struct_0(D_527))
      | ~ m1_subset_1(F_532,k1_zfmisc_1(u1_struct_0(D_527)))
      | ~ m1_pre_topc(C_530,D_527)
      | ~ m1_subset_1(E_528,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_527),u1_struct_0(B_531))))
      | ~ v1_funct_2(E_528,u1_struct_0(D_527),u1_struct_0(B_531))
      | ~ v1_funct_1(E_528)
      | ~ m1_pre_topc(D_527,A_529)
      | v2_struct_0(D_527)
      | ~ m1_pre_topc(C_530,A_529)
      | v2_struct_0(C_530)
      | ~ l1_pre_topc(B_531)
      | ~ v2_pre_topc(B_531)
      | v2_struct_0(B_531)
      | ~ l1_pre_topc(A_529)
      | ~ v2_pre_topc(A_529)
      | v2_struct_0(A_529) ) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_1721,plain,(
    ! [F_532] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_532,'#skF_5','#skF_8')
      | ~ r1_tarski(F_532,u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
      | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
      | ~ m1_subset_1(F_532,k1_zfmisc_1(u1_struct_0('#skF_5')))
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
    inference(resolution,[status(thm)],[c_42,c_1719])).

tff(c_1724,plain,(
    ! [F_532] :
      ( r1_tmap_1('#skF_5','#skF_3','#skF_6','#skF_8')
      | ~ m1_connsp_2(F_532,'#skF_5','#skF_8')
      | ~ r1_tarski(F_532,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_532,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_700,c_659,c_699,c_659,c_660,c_659,c_46,c_659,c_46,c_1721])).

tff(c_1726,plain,(
    ! [F_534] :
      ( ~ m1_connsp_2(F_534,'#skF_5','#skF_8')
      | ~ r1_tarski(F_534,u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_534,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_78,c_1724])).

tff(c_1744,plain,(
    ! [A_535] :
      ( ~ m1_connsp_2(A_535,'#skF_5','#skF_8')
      | ~ r1_tarski(A_535,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_10,c_1726])).

tff(c_1783,plain,(
    ! [B_539] :
      ( ~ m1_connsp_2('#skF_1'('#skF_5',B_539),'#skF_5','#skF_8')
      | ~ m1_subset_1(B_539,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_1143,c_1744])).

tff(c_1787,plain,
    ( ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_20,c_1783])).

tff(c_1790,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_101,c_46,c_659,c_46,c_1787])).

tff(c_1792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1790])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.15/1.65  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.66  
% 4.15/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.15/1.66  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 4.15/1.66  
% 4.15/1.66  %Foreground sorts:
% 4.15/1.66  
% 4.15/1.66  
% 4.15/1.66  %Background operators:
% 4.15/1.66  
% 4.15/1.66  
% 4.15/1.66  %Foreground operators:
% 4.15/1.66  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.15/1.66  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 4.15/1.66  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 4.15/1.66  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.15/1.66  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 4.15/1.66  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.15/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.15/1.66  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 4.15/1.66  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.15/1.66  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.15/1.66  tff('#skF_7', type, '#skF_7': $i).
% 4.15/1.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.15/1.66  tff('#skF_5', type, '#skF_5': $i).
% 4.15/1.66  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.15/1.66  tff('#skF_6', type, '#skF_6': $i).
% 4.15/1.66  tff('#skF_2', type, '#skF_2': $i).
% 4.15/1.66  tff('#skF_3', type, '#skF_3': $i).
% 4.15/1.66  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.15/1.66  tff('#skF_8', type, '#skF_8': $i).
% 4.15/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.15/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.15/1.66  tff('#skF_4', type, '#skF_4': $i).
% 4.15/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.15/1.66  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.15/1.66  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.15/1.66  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.15/1.66  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.15/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.15/1.66  
% 4.28/1.68  tff(f_273, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.28/1.68  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.28/1.68  tff(f_51, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.28/1.68  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.28/1.68  tff(f_157, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_pre_topc(C, A) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) <=> m1_pre_topc(B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_tsep_1)).
% 4.28/1.68  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.28/1.68  tff(f_143, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_tmap_1)).
% 4.28/1.68  tff(f_105, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_tsep_1)).
% 4.28/1.68  tff(f_84, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (?[C]: m1_connsp_2(C, A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', existence_m1_connsp_2)).
% 4.28/1.68  tff(f_72, axiom, (![A, B]: ((((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) & m1_subset_1(B, u1_struct_0(A))) => (![C]: (m1_connsp_2(C, A, B) => m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_connsp_2)).
% 4.28/1.68  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 4.28/1.68  tff(f_224, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.28/1.68  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_122, plain, (![B_436, A_437]: (v2_pre_topc(B_436) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437) | ~v2_pre_topc(A_437))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.28/1.68  tff(c_128, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_122])).
% 4.28/1.68  tff(c_134, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_128])).
% 4.28/1.68  tff(c_89, plain, (![B_428, A_429]: (l1_pre_topc(B_428) | ~m1_pre_topc(B_428, A_429) | ~l1_pre_topc(A_429))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.28/1.68  tff(c_95, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_89])).
% 4.28/1.68  tff(c_101, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_95])).
% 4.28/1.68  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.68  tff(c_241, plain, (![B_456, C_457, A_458]: (m1_pre_topc(B_456, C_457) | ~r1_tarski(u1_struct_0(B_456), u1_struct_0(C_457)) | ~m1_pre_topc(C_457, A_458) | ~m1_pre_topc(B_456, A_458) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.28/1.68  tff(c_252, plain, (![B_459, A_460]: (m1_pre_topc(B_459, B_459) | ~m1_pre_topc(B_459, A_460) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460))), inference(resolution, [status(thm)], [c_6, c_241])).
% 4.28/1.68  tff(c_258, plain, (m1_pre_topc('#skF_5', '#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_58, c_252])).
% 4.28/1.68  tff(c_265, plain, (m1_pre_topc('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_258])).
% 4.28/1.68  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_92, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_89])).
% 4.28/1.68  tff(c_98, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_92])).
% 4.28/1.68  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))='#skF_5'), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_135, plain, (![B_438, A_439]: (m1_pre_topc(B_438, A_439) | ~m1_pre_topc(B_438, g1_pre_topc(u1_struct_0(A_439), u1_pre_topc(A_439))) | ~l1_pre_topc(A_439))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.28/1.68  tff(c_138, plain, (![B_438]: (m1_pre_topc(B_438, '#skF_4') | ~m1_pre_topc(B_438, '#skF_5') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_135])).
% 4.28/1.68  tff(c_140, plain, (![B_438]: (m1_pre_topc(B_438, '#skF_4') | ~m1_pre_topc(B_438, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_138])).
% 4.28/1.68  tff(c_323, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_265, c_140])).
% 4.28/1.68  tff(c_30, plain, (![B_42, C_44, A_38]: (r1_tarski(u1_struct_0(B_42), u1_struct_0(C_44)) | ~m1_pre_topc(B_42, C_44) | ~m1_pre_topc(C_44, A_38) | ~m1_pre_topc(B_42, A_38) | ~l1_pre_topc(A_38) | ~v2_pre_topc(A_38))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.28/1.68  tff(c_299, plain, (![B_42]: (r1_tarski(u1_struct_0(B_42), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_42, '#skF_5') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5'))), inference(resolution, [status(thm)], [c_265, c_30])).
% 4.28/1.68  tff(c_377, plain, (![B_462]: (r1_tarski(u1_struct_0(B_462), u1_struct_0('#skF_5')) | ~m1_pre_topc(B_462, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_101, c_299])).
% 4.28/1.68  tff(c_195, plain, (![B_450, C_451, A_452]: (r1_tarski(u1_struct_0(B_450), u1_struct_0(C_451)) | ~m1_pre_topc(B_450, C_451) | ~m1_pre_topc(C_451, A_452) | ~m1_pre_topc(B_450, A_452) | ~l1_pre_topc(A_452) | ~v2_pre_topc(A_452))), inference(cnfTransformation, [status(thm)], [f_157])).
% 4.28/1.68  tff(c_199, plain, (![B_450]: (r1_tarski(u1_struct_0(B_450), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_450, '#skF_4') | ~m1_pre_topc(B_450, '#skF_2') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2'))), inference(resolution, [status(thm)], [c_62, c_195])).
% 4.28/1.68  tff(c_209, plain, (![B_453]: (r1_tarski(u1_struct_0(B_453), u1_struct_0('#skF_4')) | ~m1_pre_topc(B_453, '#skF_4') | ~m1_pre_topc(B_453, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_199])).
% 4.28/1.68  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.28/1.68  tff(c_212, plain, (![B_453]: (u1_struct_0(B_453)=u1_struct_0('#skF_4') | ~r1_tarski(u1_struct_0('#skF_4'), u1_struct_0(B_453)) | ~m1_pre_topc(B_453, '#skF_4') | ~m1_pre_topc(B_453, '#skF_2'))), inference(resolution, [status(thm)], [c_209, c_2])).
% 4.28/1.68  tff(c_383, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_2') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_377, c_212])).
% 4.28/1.68  tff(c_389, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_323, c_383])).
% 4.28/1.68  tff(c_391, plain, (~m1_pre_topc('#skF_4', '#skF_5')), inference(splitLeft, [status(thm)], [c_389])).
% 4.28/1.68  tff(c_125, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_122])).
% 4.28/1.68  tff(c_131, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_125])).
% 4.28/1.68  tff(c_256, plain, (m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2')), inference(resolution, [status(thm)], [c_62, c_252])).
% 4.28/1.68  tff(c_262, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_256])).
% 4.28/1.68  tff(c_489, plain, (![A_471, B_472]: (k1_tsep_1(A_471, B_472, B_472)=g1_pre_topc(u1_struct_0(B_472), u1_pre_topc(B_472)) | ~m1_pre_topc(B_472, A_471) | v2_struct_0(B_472) | ~l1_pre_topc(A_471) | ~v2_pre_topc(A_471) | v2_struct_0(A_471))), inference(cnfTransformation, [status(thm)], [f_143])).
% 4.28/1.68  tff(c_497, plain, (g1_pre_topc(u1_struct_0('#skF_4'), u1_pre_topc('#skF_4'))=k1_tsep_1('#skF_4', '#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_262, c_489])).
% 4.28/1.68  tff(c_517, plain, (k1_tsep_1('#skF_4', '#skF_4', '#skF_4')='#skF_5' | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_98, c_50, c_497])).
% 4.28/1.68  tff(c_518, plain, (k1_tsep_1('#skF_4', '#skF_4', '#skF_4')='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_64, c_517])).
% 4.28/1.68  tff(c_598, plain, (![B_475, A_476, C_477]: (m1_pre_topc(B_475, k1_tsep_1(A_476, B_475, C_477)) | ~m1_pre_topc(C_477, A_476) | v2_struct_0(C_477) | ~m1_pre_topc(B_475, A_476) | v2_struct_0(B_475) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.28/1.68  tff(c_631, plain, (m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_518, c_598])).
% 4.28/1.68  tff(c_656, plain, (m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_98, c_262, c_262, c_631])).
% 4.28/1.68  tff(c_658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_391, c_656])).
% 4.28/1.68  tff(c_659, plain, (u1_struct_0('#skF_5')=u1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_389])).
% 4.28/1.68  tff(c_20, plain, (![A_18, B_19]: (m1_connsp_2('#skF_1'(A_18, B_19), A_18, B_19) | ~m1_subset_1(B_19, u1_struct_0(A_18)) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.28/1.68  tff(c_756, plain, (![C_479, A_480, B_481]: (m1_subset_1(C_479, k1_zfmisc_1(u1_struct_0(A_480))) | ~m1_connsp_2(C_479, A_480, B_481) | ~m1_subset_1(B_481, u1_struct_0(A_480)) | ~l1_pre_topc(A_480) | ~v2_pre_topc(A_480) | v2_struct_0(A_480))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.28/1.68  tff(c_1128, plain, (![A_495, B_496]: (m1_subset_1('#skF_1'(A_495, B_496), k1_zfmisc_1(u1_struct_0(A_495))) | ~m1_subset_1(B_496, u1_struct_0(A_495)) | ~l1_pre_topc(A_495) | ~v2_pre_topc(A_495) | v2_struct_0(A_495))), inference(resolution, [status(thm)], [c_20, c_756])).
% 4.28/1.68  tff(c_1134, plain, (![B_496]: (m1_subset_1('#skF_1'('#skF_5', B_496), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_496, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_659, c_1128])).
% 4.28/1.68  tff(c_1137, plain, (![B_496]: (m1_subset_1('#skF_1'('#skF_5', B_496), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_496, u1_struct_0('#skF_4')) | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_101, c_659, c_1134])).
% 4.28/1.68  tff(c_1139, plain, (![B_497]: (m1_subset_1('#skF_1'('#skF_5', B_497), k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_subset_1(B_497, u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_60, c_1137])).
% 4.28/1.68  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.28/1.68  tff(c_1143, plain, (![B_497]: (r1_tarski('#skF_1'('#skF_5', B_497), u1_struct_0('#skF_4')) | ~m1_subset_1(B_497, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1139, c_8])).
% 4.28/1.68  tff(c_10, plain, (![A_3, B_4]: (m1_subset_1(A_3, k1_zfmisc_1(B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.28/1.68  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_44, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_40, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_78, plain, (~r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_40])).
% 4.28/1.68  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_54, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_700, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_54])).
% 4.28/1.68  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_699, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_659, c_52])).
% 4.28/1.68  tff(c_660, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(splitRight, [status(thm)], [c_389])).
% 4.28/1.68  tff(c_42, plain, (r1_tmap_1('#skF_4', '#skF_3', k3_tmap_1('#skF_2', '#skF_3', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_273])).
% 4.28/1.68  tff(c_1719, plain, (![E_528, F_532, D_527, B_531, H_533, C_530, A_529]: (r1_tmap_1(D_527, B_531, E_528, H_533) | ~r1_tmap_1(C_530, B_531, k3_tmap_1(A_529, B_531, D_527, C_530, E_528), H_533) | ~m1_connsp_2(F_532, D_527, H_533) | ~r1_tarski(F_532, u1_struct_0(C_530)) | ~m1_subset_1(H_533, u1_struct_0(C_530)) | ~m1_subset_1(H_533, u1_struct_0(D_527)) | ~m1_subset_1(F_532, k1_zfmisc_1(u1_struct_0(D_527))) | ~m1_pre_topc(C_530, D_527) | ~m1_subset_1(E_528, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_527), u1_struct_0(B_531)))) | ~v1_funct_2(E_528, u1_struct_0(D_527), u1_struct_0(B_531)) | ~v1_funct_1(E_528) | ~m1_pre_topc(D_527, A_529) | v2_struct_0(D_527) | ~m1_pre_topc(C_530, A_529) | v2_struct_0(C_530) | ~l1_pre_topc(B_531) | ~v2_pre_topc(B_531) | v2_struct_0(B_531) | ~l1_pre_topc(A_529) | ~v2_pre_topc(A_529) | v2_struct_0(A_529))), inference(cnfTransformation, [status(thm)], [f_224])).
% 4.28/1.68  tff(c_1721, plain, (![F_532]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_532, '#skF_5', '#skF_8') | ~r1_tarski(F_532, u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1(F_532, k1_zfmisc_1(u1_struct_0('#skF_5'))) | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_2') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_2') | v2_struct_0('#skF_4') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_42, c_1719])).
% 4.28/1.68  tff(c_1724, plain, (![F_532]: (r1_tmap_1('#skF_5', '#skF_3', '#skF_6', '#skF_8') | ~m1_connsp_2(F_532, '#skF_5', '#skF_8') | ~r1_tarski(F_532, u1_struct_0('#skF_4')) | ~m1_subset_1(F_532, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_5') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_700, c_659, c_699, c_659, c_660, c_659, c_46, c_659, c_46, c_1721])).
% 4.28/1.68  tff(c_1726, plain, (![F_534]: (~m1_connsp_2(F_534, '#skF_5', '#skF_8') | ~r1_tarski(F_534, u1_struct_0('#skF_4')) | ~m1_subset_1(F_534, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_78, c_1724])).
% 4.28/1.68  tff(c_1744, plain, (![A_535]: (~m1_connsp_2(A_535, '#skF_5', '#skF_8') | ~r1_tarski(A_535, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_10, c_1726])).
% 4.28/1.68  tff(c_1783, plain, (![B_539]: (~m1_connsp_2('#skF_1'('#skF_5', B_539), '#skF_5', '#skF_8') | ~m1_subset_1(B_539, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_1143, c_1744])).
% 4.28/1.68  tff(c_1787, plain, (~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_20, c_1783])).
% 4.28/1.68  tff(c_1790, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_134, c_101, c_46, c_659, c_46, c_1787])).
% 4.28/1.68  tff(c_1792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_1790])).
% 4.28/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.28/1.68  
% 4.28/1.68  Inference rules
% 4.28/1.68  ----------------------
% 4.28/1.68  #Ref     : 0
% 4.28/1.68  #Sup     : 332
% 4.28/1.68  #Fact    : 0
% 4.28/1.68  #Define  : 0
% 4.28/1.68  #Split   : 4
% 4.28/1.68  #Chain   : 0
% 4.28/1.68  #Close   : 0
% 4.28/1.68  
% 4.28/1.68  Ordering : KBO
% 4.28/1.68  
% 4.28/1.68  Simplification rules
% 4.28/1.68  ----------------------
% 4.28/1.68  #Subsume      : 63
% 4.28/1.68  #Demod        : 517
% 4.28/1.68  #Tautology    : 158
% 4.28/1.68  #SimpNegUnit  : 67
% 4.28/1.68  #BackRed      : 11
% 4.28/1.68  
% 4.28/1.68  #Partial instantiations: 0
% 4.28/1.68  #Strategies tried      : 1
% 4.28/1.68  
% 4.28/1.68  Timing (in seconds)
% 4.28/1.68  ----------------------
% 4.28/1.69  Preprocessing        : 0.39
% 4.28/1.69  Parsing              : 0.20
% 4.28/1.69  CNF conversion       : 0.05
% 4.28/1.69  Main loop            : 0.53
% 4.28/1.69  Inferencing          : 0.16
% 4.28/1.69  Reduction            : 0.19
% 4.28/1.69  Demodulation         : 0.14
% 4.28/1.69  BG Simplification    : 0.03
% 4.28/1.69  Subsumption          : 0.12
% 4.28/1.69  Abstraction          : 0.02
% 4.28/1.69  MUC search           : 0.00
% 4.28/1.69  Cooper               : 0.00
% 4.28/1.69  Total                : 0.96
% 4.28/1.69  Index Insertion      : 0.00
% 4.28/1.69  Index Deletion       : 0.00
% 4.28/1.69  Index Matching       : 0.00
% 4.28/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
