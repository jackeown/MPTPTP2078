%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:28 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.94s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 496 expanded)
%              Number of leaves         :   39 ( 202 expanded)
%              Depth                    :   15
%              Number of atoms          :  434 (3658 expanded)
%              Number of equality atoms :    5 ( 156 expanded)
%              Maximal formula depth    :   30 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k3_tmap_1,type,(
    k3_tmap_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v3_pre_topc,type,(
    v3_pre_topc: ( $i * $i ) > $o )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_216,negated_conjecture,(
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
                       => ( ( v1_tsep_1(C,D)
                            & m1_pre_topc(C,D) )
                         => ! [F] :
                              ( m1_subset_1(F,u1_struct_0(D))
                             => ! [G] :
                                  ( m1_subset_1(G,u1_struct_0(C))
                                 => ( F = G
                                   => ( r1_tmap_1(D,B,E,F)
                                    <=> r1_tmap_1(C,B,k3_tmap_1(A,B,D,C,E),G) ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_tmap_1)).

tff(f_63,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_56,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_96,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_71,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_52,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ! [C] :
              ( m1_subset_1(C,k1_zfmisc_1(u1_struct_0(A)))
             => ( C = u1_struct_0(B)
               => ( ( v1_tsep_1(B,A)
                    & m1_pre_topc(B,A) )
                <=> v3_pre_topc(C,A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tsep_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_165,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t84_tmap_1)).

tff(c_64,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_54,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_88,plain,(
    ! [B_411,A_412] :
      ( l1_pre_topc(B_411)
      | ~ m1_pre_topc(B_411,A_412)
      | ~ l1_pre_topc(A_412) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_94,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_88])).

tff(c_103,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_94])).

tff(c_14,plain,(
    ! [A_11] :
      ( l1_struct_0(A_11)
      | ~ l1_pre_topc(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_451,plain,(
    ! [B_473,A_474] :
      ( m1_subset_1(u1_struct_0(B_473),k1_zfmisc_1(u1_struct_0(A_474)))
      | ~ m1_pre_topc(B_473,A_474)
      | ~ l1_pre_topc(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( m1_subset_1(A_5,C_7)
      | ~ m1_subset_1(B_6,k1_zfmisc_1(C_7))
      | ~ r2_hidden(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_496,plain,(
    ! [A_481,A_482,B_483] :
      ( m1_subset_1(A_481,u1_struct_0(A_482))
      | ~ r2_hidden(A_481,u1_struct_0(B_483))
      | ~ m1_pre_topc(B_483,A_482)
      | ~ l1_pre_topc(A_482) ) ),
    inference(resolution,[status(thm)],[c_451,c_10])).

tff(c_501,plain,(
    ! [A_484,A_485,B_486] :
      ( m1_subset_1(A_484,u1_struct_0(A_485))
      | ~ m1_pre_topc(B_486,A_485)
      | ~ l1_pre_topc(A_485)
      | v1_xboole_0(u1_struct_0(B_486))
      | ~ m1_subset_1(A_484,u1_struct_0(B_486)) ) ),
    inference(resolution,[status(thm)],[c_8,c_496])).

tff(c_509,plain,(
    ! [A_484] :
      ( m1_subset_1(A_484,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_484,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_501])).

tff(c_519,plain,(
    ! [A_484] :
      ( m1_subset_1(A_484,u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_484,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_509])).

tff(c_541,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_519])).

tff(c_18,plain,(
    ! [A_15] :
      ( ~ v1_xboole_0(u1_struct_0(A_15))
      | ~ l1_struct_0(A_15)
      | v2_struct_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_549,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_541,c_18])).

tff(c_552,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_549])).

tff(c_555,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_552])).

tff(c_559,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_555])).

tff(c_561,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_519])).

tff(c_34,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_36,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_79,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_50,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_91,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_88])).

tff(c_100,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_91])).

tff(c_40,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_66,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_115,plain,(
    ! [B_417,A_418] :
      ( v2_pre_topc(B_417)
      | ~ m1_pre_topc(B_417,A_418)
      | ~ l1_pre_topc(A_418)
      | ~ v2_pre_topc(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_118,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_50,c_115])).

tff(c_127,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_118])).

tff(c_42,plain,(
    v1_tsep_1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_26,plain,(
    ! [B_25,A_23] :
      ( m1_subset_1(u1_struct_0(B_25),k1_zfmisc_1(u1_struct_0(A_23)))
      | ~ m1_pre_topc(B_25,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_631,plain,(
    ! [B_498,A_499] :
      ( v3_pre_topc(u1_struct_0(B_498),A_499)
      | ~ v1_tsep_1(B_498,A_499)
      | ~ m1_subset_1(u1_struct_0(B_498),k1_zfmisc_1(u1_struct_0(A_499)))
      | ~ m1_pre_topc(B_498,A_499)
      | ~ l1_pre_topc(A_499)
      | ~ v2_pre_topc(A_499) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_635,plain,(
    ! [B_25,A_23] :
      ( v3_pre_topc(u1_struct_0(B_25),A_23)
      | ~ v1_tsep_1(B_25,A_23)
      | ~ v2_pre_topc(A_23)
      | ~ m1_pre_topc(B_25,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_631])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_38,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_142,plain,(
    ! [B_423,A_424] :
      ( m1_subset_1(u1_struct_0(B_423),k1_zfmisc_1(u1_struct_0(A_424)))
      | ~ m1_pre_topc(B_423,A_424)
      | ~ l1_pre_topc(A_424) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_185,plain,(
    ! [A_431,A_432,B_433] :
      ( m1_subset_1(A_431,u1_struct_0(A_432))
      | ~ r2_hidden(A_431,u1_struct_0(B_433))
      | ~ m1_pre_topc(B_433,A_432)
      | ~ l1_pre_topc(A_432) ) ),
    inference(resolution,[status(thm)],[c_142,c_10])).

tff(c_191,plain,(
    ! [A_434,A_435,B_436] :
      ( m1_subset_1(A_434,u1_struct_0(A_435))
      | ~ m1_pre_topc(B_436,A_435)
      | ~ l1_pre_topc(A_435)
      | v1_xboole_0(u1_struct_0(B_436))
      | ~ m1_subset_1(A_434,u1_struct_0(B_436)) ) ),
    inference(resolution,[status(thm)],[c_8,c_185])).

tff(c_199,plain,(
    ! [A_434] :
      ( m1_subset_1(A_434,u1_struct_0('#skF_1'))
      | ~ l1_pre_topc('#skF_1')
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_434,u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_54,c_191])).

tff(c_209,plain,(
    ! [A_434] :
      ( m1_subset_1(A_434,u1_struct_0('#skF_1'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_434,u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_199])).

tff(c_235,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_209])).

tff(c_238,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_235,c_18])).

tff(c_241,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_238])).

tff(c_244,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_241])).

tff(c_248,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_244])).

tff(c_250,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_209])).

tff(c_385,plain,(
    ! [B_456,A_457] :
      ( v3_pre_topc(u1_struct_0(B_456),A_457)
      | ~ v1_tsep_1(B_456,A_457)
      | ~ m1_subset_1(u1_struct_0(B_456),k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ m1_pre_topc(B_456,A_457)
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_389,plain,(
    ! [B_25,A_23] :
      ( v3_pre_topc(u1_struct_0(B_25),A_23)
      | ~ v1_tsep_1(B_25,A_23)
      | ~ v2_pre_topc(A_23)
      | ~ m1_pre_topc(B_25,A_23)
      | ~ l1_pre_topc(A_23) ) ),
    inference(resolution,[status(thm)],[c_26,c_385])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_52,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_70,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6')
    | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_70])).

tff(c_134,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_60,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_58,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_48,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_46,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_76,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_216])).

tff(c_77,plain,
    ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_76])).

tff(c_190,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_77])).

tff(c_395,plain,(
    ! [C_461,A_460,F_464,D_466,B_462,E_465,H_463] :
      ( r1_tmap_1(D_466,B_462,E_465,H_463)
      | ~ r1_tmap_1(C_461,B_462,k3_tmap_1(A_460,B_462,D_466,C_461,E_465),H_463)
      | ~ r1_tarski(F_464,u1_struct_0(C_461))
      | ~ r2_hidden(H_463,F_464)
      | ~ v3_pre_topc(F_464,D_466)
      | ~ m1_subset_1(H_463,u1_struct_0(C_461))
      | ~ m1_subset_1(H_463,u1_struct_0(D_466))
      | ~ m1_subset_1(F_464,k1_zfmisc_1(u1_struct_0(D_466)))
      | ~ m1_pre_topc(C_461,D_466)
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_466),u1_struct_0(B_462))))
      | ~ v1_funct_2(E_465,u1_struct_0(D_466),u1_struct_0(B_462))
      | ~ v1_funct_1(E_465)
      | ~ m1_pre_topc(D_466,A_460)
      | v2_struct_0(D_466)
      | ~ m1_pre_topc(C_461,A_460)
      | v2_struct_0(C_461)
      | ~ l1_pre_topc(B_462)
      | ~ v2_pre_topc(B_462)
      | v2_struct_0(B_462)
      | ~ l1_pre_topc(A_460)
      | ~ v2_pre_topc(A_460)
      | v2_struct_0(A_460) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_397,plain,(
    ! [F_464] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_464,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_464)
      | ~ v3_pre_topc(F_464,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_464,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ m1_pre_topc('#skF_3','#skF_4')
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4','#skF_1')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc('#skF_3','#skF_1')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_1')
      | ~ v2_pre_topc('#skF_1')
      | v2_struct_0('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_190,c_395])).

tff(c_400,plain,(
    ! [F_464] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_464,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_464)
      | ~ v3_pre_topc(F_464,'#skF_4')
      | ~ m1_subset_1(F_464,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_64,c_60,c_58,c_54,c_50,c_48,c_46,c_44,c_40,c_38,c_79,c_397])).

tff(c_402,plain,(
    ! [F_467] :
      ( ~ r1_tarski(F_467,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_467)
      | ~ v3_pre_topc(F_467,'#skF_4')
      | ~ m1_subset_1(F_467,k1_zfmisc_1(u1_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_56,c_52,c_134,c_400])).

tff(c_406,plain,(
    ! [B_25] :
      ( ~ r1_tarski(u1_struct_0(B_25),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_25))
      | ~ v3_pre_topc(u1_struct_0(B_25),'#skF_4')
      | ~ m1_pre_topc(B_25,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_26,c_402])).

tff(c_410,plain,(
    ! [B_468] :
      ( ~ r1_tarski(u1_struct_0(B_468),u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',u1_struct_0(B_468))
      | ~ v3_pre_topc(u1_struct_0(B_468),'#skF_4')
      | ~ m1_pre_topc(B_468,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_406])).

tff(c_414,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_410])).

tff(c_417,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_414])).

tff(c_418,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_417])).

tff(c_421,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_389,c_418])).

tff(c_425,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_40,c_127,c_42,c_421])).

tff(c_426,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_417])).

tff(c_436,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_426])).

tff(c_439,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_436])).

tff(c_441,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_250,c_439])).

tff(c_443,plain,(
    r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_707,plain,(
    ! [A_517,C_518,F_521,H_520,B_519,E_522,D_523] :
      ( r1_tmap_1(C_518,B_519,k3_tmap_1(A_517,B_519,D_523,C_518,E_522),H_520)
      | ~ r1_tmap_1(D_523,B_519,E_522,H_520)
      | ~ r1_tarski(F_521,u1_struct_0(C_518))
      | ~ r2_hidden(H_520,F_521)
      | ~ v3_pre_topc(F_521,D_523)
      | ~ m1_subset_1(H_520,u1_struct_0(C_518))
      | ~ m1_subset_1(H_520,u1_struct_0(D_523))
      | ~ m1_subset_1(F_521,k1_zfmisc_1(u1_struct_0(D_523)))
      | ~ m1_pre_topc(C_518,D_523)
      | ~ m1_subset_1(E_522,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_523),u1_struct_0(B_519))))
      | ~ v1_funct_2(E_522,u1_struct_0(D_523),u1_struct_0(B_519))
      | ~ v1_funct_1(E_522)
      | ~ m1_pre_topc(D_523,A_517)
      | v2_struct_0(D_523)
      | ~ m1_pre_topc(C_518,A_517)
      | v2_struct_0(C_518)
      | ~ l1_pre_topc(B_519)
      | ~ v2_pre_topc(B_519)
      | v2_struct_0(B_519)
      | ~ l1_pre_topc(A_517)
      | ~ v2_pre_topc(A_517)
      | v2_struct_0(A_517) ) ),
    inference(cnfTransformation,[status(thm)],[f_165])).

tff(c_712,plain,(
    ! [E_529,B_527,C_525,D_526,H_528,A_524] :
      ( r1_tmap_1(C_525,B_527,k3_tmap_1(A_524,B_527,D_526,C_525,E_529),H_528)
      | ~ r1_tmap_1(D_526,B_527,E_529,H_528)
      | ~ r2_hidden(H_528,u1_struct_0(C_525))
      | ~ v3_pre_topc(u1_struct_0(C_525),D_526)
      | ~ m1_subset_1(H_528,u1_struct_0(C_525))
      | ~ m1_subset_1(H_528,u1_struct_0(D_526))
      | ~ m1_subset_1(u1_struct_0(C_525),k1_zfmisc_1(u1_struct_0(D_526)))
      | ~ m1_pre_topc(C_525,D_526)
      | ~ m1_subset_1(E_529,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_526),u1_struct_0(B_527))))
      | ~ v1_funct_2(E_529,u1_struct_0(D_526),u1_struct_0(B_527))
      | ~ v1_funct_1(E_529)
      | ~ m1_pre_topc(D_526,A_524)
      | v2_struct_0(D_526)
      | ~ m1_pre_topc(C_525,A_524)
      | v2_struct_0(C_525)
      | ~ l1_pre_topc(B_527)
      | ~ v2_pre_topc(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_524)
      | ~ v2_pre_topc(A_524)
      | v2_struct_0(A_524) ) ),
    inference(resolution,[status(thm)],[c_6,c_707])).

tff(c_716,plain,(
    ! [A_532,B_530,A_535,E_534,B_531,H_533] :
      ( r1_tmap_1(B_530,B_531,k3_tmap_1(A_532,B_531,A_535,B_530,E_534),H_533)
      | ~ r1_tmap_1(A_535,B_531,E_534,H_533)
      | ~ r2_hidden(H_533,u1_struct_0(B_530))
      | ~ v3_pre_topc(u1_struct_0(B_530),A_535)
      | ~ m1_subset_1(H_533,u1_struct_0(B_530))
      | ~ m1_subset_1(H_533,u1_struct_0(A_535))
      | ~ m1_subset_1(E_534,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535),u1_struct_0(B_531))))
      | ~ v1_funct_2(E_534,u1_struct_0(A_535),u1_struct_0(B_531))
      | ~ v1_funct_1(E_534)
      | ~ m1_pre_topc(A_535,A_532)
      | v2_struct_0(A_535)
      | ~ m1_pre_topc(B_530,A_532)
      | v2_struct_0(B_530)
      | ~ l1_pre_topc(B_531)
      | ~ v2_pre_topc(B_531)
      | v2_struct_0(B_531)
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532)
      | ~ m1_pre_topc(B_530,A_535)
      | ~ l1_pre_topc(A_535) ) ),
    inference(resolution,[status(thm)],[c_26,c_712])).

tff(c_718,plain,(
    ! [B_530,A_532,H_533] :
      ( r1_tmap_1(B_530,'#skF_2',k3_tmap_1(A_532,'#skF_2','#skF_4',B_530,'#skF_5'),H_533)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',H_533)
      | ~ r2_hidden(H_533,u1_struct_0(B_530))
      | ~ v3_pre_topc(u1_struct_0(B_530),'#skF_4')
      | ~ m1_subset_1(H_533,u1_struct_0(B_530))
      | ~ m1_subset_1(H_533,u1_struct_0('#skF_4'))
      | ~ v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_pre_topc('#skF_4',A_532)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_530,A_532)
      | v2_struct_0(B_530)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532)
      | ~ m1_pre_topc(B_530,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_44,c_716])).

tff(c_721,plain,(
    ! [B_530,A_532,H_533] :
      ( r1_tmap_1(B_530,'#skF_2',k3_tmap_1(A_532,'#skF_2','#skF_4',B_530,'#skF_5'),H_533)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',H_533)
      | ~ r2_hidden(H_533,u1_struct_0(B_530))
      | ~ v3_pre_topc(u1_struct_0(B_530),'#skF_4')
      | ~ m1_subset_1(H_533,u1_struct_0(B_530))
      | ~ m1_subset_1(H_533,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_532)
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_530,A_532)
      | v2_struct_0(B_530)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_532)
      | ~ v2_pre_topc(A_532)
      | v2_struct_0(A_532)
      | ~ m1_pre_topc(B_530,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_60,c_58,c_48,c_46,c_718])).

tff(c_723,plain,(
    ! [B_536,A_537,H_538] :
      ( r1_tmap_1(B_536,'#skF_2',k3_tmap_1(A_537,'#skF_2','#skF_4',B_536,'#skF_5'),H_538)
      | ~ r1_tmap_1('#skF_4','#skF_2','#skF_5',H_538)
      | ~ r2_hidden(H_538,u1_struct_0(B_536))
      | ~ v3_pre_topc(u1_struct_0(B_536),'#skF_4')
      | ~ m1_subset_1(H_538,u1_struct_0(B_536))
      | ~ m1_subset_1(H_538,u1_struct_0('#skF_4'))
      | ~ m1_pre_topc('#skF_4',A_537)
      | ~ m1_pre_topc(B_536,A_537)
      | v2_struct_0(B_536)
      | ~ l1_pre_topc(A_537)
      | ~ v2_pre_topc(A_537)
      | v2_struct_0(A_537)
      | ~ m1_pre_topc(B_536,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_52,c_721])).

tff(c_442,plain,(
    ~ r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_728,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
    | ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1')
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_723,c_442])).

tff(c_735,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_66,c_64,c_54,c_50,c_38,c_79,c_443,c_728])).

tff(c_736,plain,
    ( ~ r2_hidden('#skF_6',u1_struct_0('#skF_3'))
    | ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_56,c_735])).

tff(c_737,plain,(
    ~ v3_pre_topc(u1_struct_0('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_736])).

tff(c_740,plain,
    ( ~ v1_tsep_1('#skF_3','#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_635,c_737])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_40,c_127,c_42,c_740])).

tff(c_745,plain,(
    ~ r2_hidden('#skF_6',u1_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_736])).

tff(c_749,plain,
    ( v1_xboole_0(u1_struct_0('#skF_3'))
    | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_8,c_745])).

tff(c_752,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_749])).

tff(c_754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_561,c_752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:13:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.60  
% 3.60/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.60/1.60  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.60/1.60  
% 3.60/1.60  %Foreground sorts:
% 3.60/1.60  
% 3.60/1.60  
% 3.60/1.60  %Background operators:
% 3.60/1.60  
% 3.60/1.60  
% 3.60/1.60  %Foreground operators:
% 3.60/1.60  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.60/1.60  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.60/1.60  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.60/1.60  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.60/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.60/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.60/1.60  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.60/1.60  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.60/1.60  tff('#skF_7', type, '#skF_7': $i).
% 3.60/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.60/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.60/1.60  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.60/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.60/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.60/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.60/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.60/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.60/1.60  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.60/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.60/1.60  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.60/1.60  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.60/1.60  tff('#skF_4', type, '#skF_4': $i).
% 3.60/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.60/1.60  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.60/1.60  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.60/1.60  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.60/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.60/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.60/1.60  
% 3.94/1.64  tff(f_216, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.94/1.64  tff(f_63, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.94/1.64  tff(f_56, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.94/1.64  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.94/1.64  tff(f_96, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.94/1.64  tff(f_43, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 3.94/1.64  tff(f_71, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.94/1.64  tff(f_52, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.94/1.64  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(u1_struct_0(A))) => ((C = u1_struct_0(B)) => ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) <=> v3_pre_topc(C, A))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_tsep_1)).
% 3.94/1.64  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.94/1.64  tff(f_165, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.94/1.64  tff(c_64, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_54, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_88, plain, (![B_411, A_412]: (l1_pre_topc(B_411) | ~m1_pre_topc(B_411, A_412) | ~l1_pre_topc(A_412))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.94/1.64  tff(c_94, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_88])).
% 3.94/1.64  tff(c_103, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_94])).
% 3.94/1.64  tff(c_14, plain, (![A_11]: (l1_struct_0(A_11) | ~l1_pre_topc(A_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.94/1.64  tff(c_56, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.94/1.64  tff(c_451, plain, (![B_473, A_474]: (m1_subset_1(u1_struct_0(B_473), k1_zfmisc_1(u1_struct_0(A_474))) | ~m1_pre_topc(B_473, A_474) | ~l1_pre_topc(A_474))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.94/1.64  tff(c_10, plain, (![A_5, C_7, B_6]: (m1_subset_1(A_5, C_7) | ~m1_subset_1(B_6, k1_zfmisc_1(C_7)) | ~r2_hidden(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.94/1.64  tff(c_496, plain, (![A_481, A_482, B_483]: (m1_subset_1(A_481, u1_struct_0(A_482)) | ~r2_hidden(A_481, u1_struct_0(B_483)) | ~m1_pre_topc(B_483, A_482) | ~l1_pre_topc(A_482))), inference(resolution, [status(thm)], [c_451, c_10])).
% 3.94/1.64  tff(c_501, plain, (![A_484, A_485, B_486]: (m1_subset_1(A_484, u1_struct_0(A_485)) | ~m1_pre_topc(B_486, A_485) | ~l1_pre_topc(A_485) | v1_xboole_0(u1_struct_0(B_486)) | ~m1_subset_1(A_484, u1_struct_0(B_486)))), inference(resolution, [status(thm)], [c_8, c_496])).
% 3.94/1.64  tff(c_509, plain, (![A_484]: (m1_subset_1(A_484, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_484, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_501])).
% 3.94/1.64  tff(c_519, plain, (![A_484]: (m1_subset_1(A_484, u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_484, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_509])).
% 3.94/1.64  tff(c_541, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_519])).
% 3.94/1.64  tff(c_18, plain, (![A_15]: (~v1_xboole_0(u1_struct_0(A_15)) | ~l1_struct_0(A_15) | v2_struct_0(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.94/1.64  tff(c_549, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_541, c_18])).
% 3.94/1.64  tff(c_552, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_549])).
% 3.94/1.64  tff(c_555, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_552])).
% 3.94/1.64  tff(c_559, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_555])).
% 3.94/1.64  tff(c_561, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_519])).
% 3.94/1.64  tff(c_34, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_36, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_79, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 3.94/1.64  tff(c_50, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_91, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_88])).
% 3.94/1.64  tff(c_100, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_91])).
% 3.94/1.64  tff(c_40, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_66, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_115, plain, (![B_417, A_418]: (v2_pre_topc(B_417) | ~m1_pre_topc(B_417, A_418) | ~l1_pre_topc(A_418) | ~v2_pre_topc(A_418))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.94/1.64  tff(c_118, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_50, c_115])).
% 3.94/1.64  tff(c_127, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_118])).
% 3.94/1.64  tff(c_42, plain, (v1_tsep_1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_26, plain, (![B_25, A_23]: (m1_subset_1(u1_struct_0(B_25), k1_zfmisc_1(u1_struct_0(A_23))) | ~m1_pre_topc(B_25, A_23) | ~l1_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.94/1.64  tff(c_631, plain, (![B_498, A_499]: (v3_pre_topc(u1_struct_0(B_498), A_499) | ~v1_tsep_1(B_498, A_499) | ~m1_subset_1(u1_struct_0(B_498), k1_zfmisc_1(u1_struct_0(A_499))) | ~m1_pre_topc(B_498, A_499) | ~l1_pre_topc(A_499) | ~v2_pre_topc(A_499))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.94/1.64  tff(c_635, plain, (![B_25, A_23]: (v3_pre_topc(u1_struct_0(B_25), A_23) | ~v1_tsep_1(B_25, A_23) | ~v2_pre_topc(A_23) | ~m1_pre_topc(B_25, A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_26, c_631])).
% 3.94/1.64  tff(c_68, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_38, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_142, plain, (![B_423, A_424]: (m1_subset_1(u1_struct_0(B_423), k1_zfmisc_1(u1_struct_0(A_424))) | ~m1_pre_topc(B_423, A_424) | ~l1_pre_topc(A_424))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.94/1.64  tff(c_185, plain, (![A_431, A_432, B_433]: (m1_subset_1(A_431, u1_struct_0(A_432)) | ~r2_hidden(A_431, u1_struct_0(B_433)) | ~m1_pre_topc(B_433, A_432) | ~l1_pre_topc(A_432))), inference(resolution, [status(thm)], [c_142, c_10])).
% 3.94/1.64  tff(c_191, plain, (![A_434, A_435, B_436]: (m1_subset_1(A_434, u1_struct_0(A_435)) | ~m1_pre_topc(B_436, A_435) | ~l1_pre_topc(A_435) | v1_xboole_0(u1_struct_0(B_436)) | ~m1_subset_1(A_434, u1_struct_0(B_436)))), inference(resolution, [status(thm)], [c_8, c_185])).
% 3.94/1.64  tff(c_199, plain, (![A_434]: (m1_subset_1(A_434, u1_struct_0('#skF_1')) | ~l1_pre_topc('#skF_1') | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_434, u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_54, c_191])).
% 3.94/1.64  tff(c_209, plain, (![A_434]: (m1_subset_1(A_434, u1_struct_0('#skF_1')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1(A_434, u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_199])).
% 3.94/1.64  tff(c_235, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_209])).
% 3.94/1.64  tff(c_238, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_235, c_18])).
% 3.94/1.64  tff(c_241, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_238])).
% 3.94/1.64  tff(c_244, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_241])).
% 3.94/1.64  tff(c_248, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_244])).
% 3.94/1.64  tff(c_250, plain, (~v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_209])).
% 3.94/1.64  tff(c_385, plain, (![B_456, A_457]: (v3_pre_topc(u1_struct_0(B_456), A_457) | ~v1_tsep_1(B_456, A_457) | ~m1_subset_1(u1_struct_0(B_456), k1_zfmisc_1(u1_struct_0(A_457))) | ~m1_pre_topc(B_456, A_457) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.94/1.64  tff(c_389, plain, (![B_25, A_23]: (v3_pre_topc(u1_struct_0(B_25), A_23) | ~v1_tsep_1(B_25, A_23) | ~v2_pre_topc(A_23) | ~m1_pre_topc(B_25, A_23) | ~l1_pre_topc(A_23))), inference(resolution, [status(thm)], [c_26, c_385])).
% 3.94/1.64  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.94/1.64  tff(c_62, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_52, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_70, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_78, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6') | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_70])).
% 3.94/1.64  tff(c_134, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_78])).
% 3.94/1.64  tff(c_60, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_58, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_48, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_46, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_76, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_216])).
% 3.94/1.64  tff(c_77, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_76])).
% 3.94/1.64  tff(c_190, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_134, c_77])).
% 3.94/1.64  tff(c_395, plain, (![C_461, A_460, F_464, D_466, B_462, E_465, H_463]: (r1_tmap_1(D_466, B_462, E_465, H_463) | ~r1_tmap_1(C_461, B_462, k3_tmap_1(A_460, B_462, D_466, C_461, E_465), H_463) | ~r1_tarski(F_464, u1_struct_0(C_461)) | ~r2_hidden(H_463, F_464) | ~v3_pre_topc(F_464, D_466) | ~m1_subset_1(H_463, u1_struct_0(C_461)) | ~m1_subset_1(H_463, u1_struct_0(D_466)) | ~m1_subset_1(F_464, k1_zfmisc_1(u1_struct_0(D_466))) | ~m1_pre_topc(C_461, D_466) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_466), u1_struct_0(B_462)))) | ~v1_funct_2(E_465, u1_struct_0(D_466), u1_struct_0(B_462)) | ~v1_funct_1(E_465) | ~m1_pre_topc(D_466, A_460) | v2_struct_0(D_466) | ~m1_pre_topc(C_461, A_460) | v2_struct_0(C_461) | ~l1_pre_topc(B_462) | ~v2_pre_topc(B_462) | v2_struct_0(B_462) | ~l1_pre_topc(A_460) | ~v2_pre_topc(A_460) | v2_struct_0(A_460))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.94/1.64  tff(c_397, plain, (![F_464]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_464, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_464) | ~v3_pre_topc(F_464, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_464, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_190, c_395])).
% 3.94/1.64  tff(c_400, plain, (![F_464]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_464, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_464) | ~v3_pre_topc(F_464, '#skF_4') | ~m1_subset_1(F_464, k1_zfmisc_1(u1_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_64, c_60, c_58, c_54, c_50, c_48, c_46, c_44, c_40, c_38, c_79, c_397])).
% 3.94/1.64  tff(c_402, plain, (![F_467]: (~r1_tarski(F_467, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_467) | ~v3_pre_topc(F_467, '#skF_4') | ~m1_subset_1(F_467, k1_zfmisc_1(u1_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_56, c_52, c_134, c_400])).
% 3.94/1.64  tff(c_406, plain, (![B_25]: (~r1_tarski(u1_struct_0(B_25), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_25)) | ~v3_pre_topc(u1_struct_0(B_25), '#skF_4') | ~m1_pre_topc(B_25, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_26, c_402])).
% 3.94/1.64  tff(c_410, plain, (![B_468]: (~r1_tarski(u1_struct_0(B_468), u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', u1_struct_0(B_468)) | ~v3_pre_topc(u1_struct_0(B_468), '#skF_4') | ~m1_pre_topc(B_468, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_406])).
% 3.94/1.64  tff(c_414, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_6, c_410])).
% 3.94/1.64  tff(c_417, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_414])).
% 3.94/1.64  tff(c_418, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_417])).
% 3.94/1.64  tff(c_421, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_389, c_418])).
% 3.94/1.64  tff(c_425, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_40, c_127, c_42, c_421])).
% 3.94/1.64  tff(c_426, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_417])).
% 3.94/1.64  tff(c_436, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_426])).
% 3.94/1.64  tff(c_439, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_436])).
% 3.94/1.64  tff(c_441, plain, $false, inference(negUnitSimplification, [status(thm)], [c_250, c_439])).
% 3.94/1.64  tff(c_443, plain, (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 3.94/1.64  tff(c_707, plain, (![A_517, C_518, F_521, H_520, B_519, E_522, D_523]: (r1_tmap_1(C_518, B_519, k3_tmap_1(A_517, B_519, D_523, C_518, E_522), H_520) | ~r1_tmap_1(D_523, B_519, E_522, H_520) | ~r1_tarski(F_521, u1_struct_0(C_518)) | ~r2_hidden(H_520, F_521) | ~v3_pre_topc(F_521, D_523) | ~m1_subset_1(H_520, u1_struct_0(C_518)) | ~m1_subset_1(H_520, u1_struct_0(D_523)) | ~m1_subset_1(F_521, k1_zfmisc_1(u1_struct_0(D_523))) | ~m1_pre_topc(C_518, D_523) | ~m1_subset_1(E_522, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_523), u1_struct_0(B_519)))) | ~v1_funct_2(E_522, u1_struct_0(D_523), u1_struct_0(B_519)) | ~v1_funct_1(E_522) | ~m1_pre_topc(D_523, A_517) | v2_struct_0(D_523) | ~m1_pre_topc(C_518, A_517) | v2_struct_0(C_518) | ~l1_pre_topc(B_519) | ~v2_pre_topc(B_519) | v2_struct_0(B_519) | ~l1_pre_topc(A_517) | ~v2_pre_topc(A_517) | v2_struct_0(A_517))), inference(cnfTransformation, [status(thm)], [f_165])).
% 3.94/1.64  tff(c_712, plain, (![E_529, B_527, C_525, D_526, H_528, A_524]: (r1_tmap_1(C_525, B_527, k3_tmap_1(A_524, B_527, D_526, C_525, E_529), H_528) | ~r1_tmap_1(D_526, B_527, E_529, H_528) | ~r2_hidden(H_528, u1_struct_0(C_525)) | ~v3_pre_topc(u1_struct_0(C_525), D_526) | ~m1_subset_1(H_528, u1_struct_0(C_525)) | ~m1_subset_1(H_528, u1_struct_0(D_526)) | ~m1_subset_1(u1_struct_0(C_525), k1_zfmisc_1(u1_struct_0(D_526))) | ~m1_pre_topc(C_525, D_526) | ~m1_subset_1(E_529, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_526), u1_struct_0(B_527)))) | ~v1_funct_2(E_529, u1_struct_0(D_526), u1_struct_0(B_527)) | ~v1_funct_1(E_529) | ~m1_pre_topc(D_526, A_524) | v2_struct_0(D_526) | ~m1_pre_topc(C_525, A_524) | v2_struct_0(C_525) | ~l1_pre_topc(B_527) | ~v2_pre_topc(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_524) | ~v2_pre_topc(A_524) | v2_struct_0(A_524))), inference(resolution, [status(thm)], [c_6, c_707])).
% 3.94/1.64  tff(c_716, plain, (![A_532, B_530, A_535, E_534, B_531, H_533]: (r1_tmap_1(B_530, B_531, k3_tmap_1(A_532, B_531, A_535, B_530, E_534), H_533) | ~r1_tmap_1(A_535, B_531, E_534, H_533) | ~r2_hidden(H_533, u1_struct_0(B_530)) | ~v3_pre_topc(u1_struct_0(B_530), A_535) | ~m1_subset_1(H_533, u1_struct_0(B_530)) | ~m1_subset_1(H_533, u1_struct_0(A_535)) | ~m1_subset_1(E_534, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_535), u1_struct_0(B_531)))) | ~v1_funct_2(E_534, u1_struct_0(A_535), u1_struct_0(B_531)) | ~v1_funct_1(E_534) | ~m1_pre_topc(A_535, A_532) | v2_struct_0(A_535) | ~m1_pre_topc(B_530, A_532) | v2_struct_0(B_530) | ~l1_pre_topc(B_531) | ~v2_pre_topc(B_531) | v2_struct_0(B_531) | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532) | ~m1_pre_topc(B_530, A_535) | ~l1_pre_topc(A_535))), inference(resolution, [status(thm)], [c_26, c_712])).
% 3.94/1.64  tff(c_718, plain, (![B_530, A_532, H_533]: (r1_tmap_1(B_530, '#skF_2', k3_tmap_1(A_532, '#skF_2', '#skF_4', B_530, '#skF_5'), H_533) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', H_533) | ~r2_hidden(H_533, u1_struct_0(B_530)) | ~v3_pre_topc(u1_struct_0(B_530), '#skF_4') | ~m1_subset_1(H_533, u1_struct_0(B_530)) | ~m1_subset_1(H_533, u1_struct_0('#skF_4')) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', A_532) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_530, A_532) | v2_struct_0(B_530) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532) | ~m1_pre_topc(B_530, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(resolution, [status(thm)], [c_44, c_716])).
% 3.94/1.64  tff(c_721, plain, (![B_530, A_532, H_533]: (r1_tmap_1(B_530, '#skF_2', k3_tmap_1(A_532, '#skF_2', '#skF_4', B_530, '#skF_5'), H_533) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', H_533) | ~r2_hidden(H_533, u1_struct_0(B_530)) | ~v3_pre_topc(u1_struct_0(B_530), '#skF_4') | ~m1_subset_1(H_533, u1_struct_0(B_530)) | ~m1_subset_1(H_533, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', A_532) | v2_struct_0('#skF_4') | ~m1_pre_topc(B_530, A_532) | v2_struct_0(B_530) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_532) | ~v2_pre_topc(A_532) | v2_struct_0(A_532) | ~m1_pre_topc(B_530, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_60, c_58, c_48, c_46, c_718])).
% 3.94/1.64  tff(c_723, plain, (![B_536, A_537, H_538]: (r1_tmap_1(B_536, '#skF_2', k3_tmap_1(A_537, '#skF_2', '#skF_4', B_536, '#skF_5'), H_538) | ~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', H_538) | ~r2_hidden(H_538, u1_struct_0(B_536)) | ~v3_pre_topc(u1_struct_0(B_536), '#skF_4') | ~m1_subset_1(H_538, u1_struct_0(B_536)) | ~m1_subset_1(H_538, u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', A_537) | ~m1_pre_topc(B_536, A_537) | v2_struct_0(B_536) | ~l1_pre_topc(A_537) | ~v2_pre_topc(A_537) | v2_struct_0(A_537) | ~m1_pre_topc(B_536, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_62, c_52, c_721])).
% 3.94/1.64  tff(c_442, plain, (~r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(splitRight, [status(thm)], [c_78])).
% 3.94/1.64  tff(c_728, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1') | ~m1_pre_topc('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_723, c_442])).
% 3.94/1.64  tff(c_735, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_66, c_64, c_54, c_50, c_38, c_79, c_443, c_728])).
% 3.94/1.64  tff(c_736, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3')) | ~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_56, c_735])).
% 3.94/1.64  tff(c_737, plain, (~v3_pre_topc(u1_struct_0('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_736])).
% 3.94/1.64  tff(c_740, plain, (~v1_tsep_1('#skF_3', '#skF_4') | ~v2_pre_topc('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_635, c_737])).
% 3.94/1.64  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_100, c_40, c_127, c_42, c_740])).
% 3.94/1.64  tff(c_745, plain, (~r2_hidden('#skF_6', u1_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_736])).
% 3.94/1.64  tff(c_749, plain, (v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_8, c_745])).
% 3.94/1.64  tff(c_752, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_749])).
% 3.94/1.64  tff(c_754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_561, c_752])).
% 3.94/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.94/1.64  
% 3.94/1.64  Inference rules
% 3.94/1.64  ----------------------
% 3.94/1.64  #Ref     : 0
% 3.94/1.64  #Sup     : 116
% 3.94/1.64  #Fact    : 0
% 3.94/1.64  #Define  : 0
% 3.94/1.64  #Split   : 8
% 3.94/1.64  #Chain   : 0
% 3.94/1.64  #Close   : 0
% 3.94/1.64  
% 3.94/1.64  Ordering : KBO
% 3.94/1.64  
% 3.94/1.64  Simplification rules
% 3.94/1.64  ----------------------
% 3.94/1.64  #Subsume      : 20
% 3.94/1.64  #Demod        : 201
% 3.94/1.64  #Tautology    : 45
% 3.94/1.64  #SimpNegUnit  : 18
% 3.94/1.64  #BackRed      : 0
% 3.94/1.64  
% 3.94/1.64  #Partial instantiations: 0
% 3.94/1.64  #Strategies tried      : 1
% 3.94/1.64  
% 3.94/1.64  Timing (in seconds)
% 3.94/1.64  ----------------------
% 3.94/1.64  Preprocessing        : 0.41
% 3.94/1.64  Parsing              : 0.20
% 3.94/1.64  CNF conversion       : 0.06
% 3.94/1.64  Main loop            : 0.43
% 3.94/1.64  Inferencing          : 0.16
% 3.94/1.64  Reduction            : 0.13
% 3.94/1.64  Demodulation         : 0.09
% 3.94/1.64  BG Simplification    : 0.02
% 3.94/1.64  Subsumption          : 0.09
% 3.94/1.64  Abstraction          : 0.02
% 3.94/1.64  MUC search           : 0.00
% 3.94/1.64  Cooper               : 0.00
% 3.94/1.64  Total                : 0.90
% 3.94/1.64  Index Insertion      : 0.00
% 3.94/1.64  Index Deletion       : 0.00
% 3.94/1.64  Index Matching       : 0.00
% 3.94/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------
