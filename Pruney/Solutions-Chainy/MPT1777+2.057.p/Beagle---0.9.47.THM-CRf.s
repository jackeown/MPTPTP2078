%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:40 EST 2020

% Result     : Theorem 3.61s
% Output     : CNFRefutation 3.61s
% Verified   : 
% Statistics : Number of formulae       :  136 (2069 expanded)
%              Number of leaves         :   49 ( 774 expanded)
%              Depth                    :   19
%              Number of atoms          :  319 (10998 expanded)
%              Number of equality atoms :   27 (1362 expanded)
%              Maximal formula depth    :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

tff(k1_tsep_1,type,(
    k1_tsep_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v1_pre_topc,type,(
    v1_pre_topc: $i > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(l1_struct_0,type,(
    l1_struct_0: $i > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_50,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_46,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_87,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => m1_subset_1(k2_struct_0(A),k1_zfmisc_1(u1_struct_0(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_152,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => k1_tsep_1(A,B,B) = g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

tff(f_137,axiom,(
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

tff(f_81,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ( v1_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
        & v2_pre_topc(g1_pre_topc(u1_struct_0(A),u1_pre_topc(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_pre_topc)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_116,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & m1_pre_topc(B,A) )
         => ! [C] :
              ( ( ~ v2_struct_0(C)
                & m1_pre_topc(C,A) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_pre_topc(D)
                    & m1_pre_topc(D,A) )
                 => ( D = k1_tsep_1(A,B,C)
                  <=> u1_struct_0(D) = k2_xboole_0(u1_struct_0(B),u1_struct_0(C)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

tff(f_209,axiom,(
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

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_161,plain,(
    ! [B_426,A_427] :
      ( l1_pre_topc(B_426)
      | ~ m1_pre_topc(B_426,A_427)
      | ~ l1_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_167,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_161])).

tff(c_173,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_167])).

tff(c_16,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_97,plain,(
    ! [A_421] :
      ( u1_struct_0(A_421) = k2_struct_0(A_421)
      | ~ l1_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_101,plain,(
    ! [A_12] :
      ( u1_struct_0(A_12) = k2_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_16,c_97])).

tff(c_181,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_101])).

tff(c_20,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_212,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_20])).

tff(c_215,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_212])).

tff(c_222,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_215])).

tff(c_225,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_16,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_173,c_225])).

tff(c_230,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_208,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_48])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_289,plain,(
    ! [B_434,A_435] :
      ( v2_pre_topc(B_434)
      | ~ m1_pre_topc(B_434,A_435)
      | ~ l1_pre_topc(A_435)
      | ~ v2_pre_topc(A_435) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_295,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_289])).

tff(c_301,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_295])).

tff(c_26,plain,(
    ! [A_18] :
      ( v3_pre_topc(k2_struct_0(A_18),A_18)
      | ~ l1_pre_topc(A_18)
      | ~ v2_pre_topc(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_231,plain,(
    l1_struct_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_215])).

tff(c_243,plain,(
    ! [A_433] :
      ( m1_subset_1(k2_struct_0(A_433),k1_zfmisc_1(u1_struct_0(A_433)))
      | ~ l1_struct_0(A_433) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_249,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4')))
    | ~ l1_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_243])).

tff(c_261,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_249])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_271,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_261,c_6])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_102,plain,(
    ! [A_422] :
      ( u1_struct_0(A_422) = k2_struct_0(A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(resolution,[status(thm)],[c_16,c_97])).

tff(c_110,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_102])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_116,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_54])).

tff(c_207,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_116])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_115,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_52])).

tff(c_276,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_115])).

tff(c_164,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_161])).

tff(c_170,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_164])).

tff(c_177,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_170,c_101])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_182,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_50])).

tff(c_365,plain,(
    ! [A_439,B_440] :
      ( k1_tsep_1(A_439,B_440,B_440) = g1_pre_topc(u1_struct_0(B_440),u1_pre_topc(B_440))
      | ~ m1_pre_topc(B_440,A_439)
      | v2_struct_0(B_440)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439)
      | v2_struct_0(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_367,plain,
    ( g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = k1_tsep_1('#skF_1','#skF_3','#skF_3')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_365])).

tff(c_372,plain,
    ( k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4'
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_182,c_177,c_367])).

tff(c_373,plain,(
    k1_tsep_1('#skF_1','#skF_3','#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64,c_372])).

tff(c_388,plain,(
    ! [B_441,A_442,C_443] :
      ( m1_pre_topc(B_441,k1_tsep_1(A_442,B_441,C_443))
      | ~ m1_pre_topc(C_443,A_442)
      | v2_struct_0(C_443)
      | ~ m1_pre_topc(B_441,A_442)
      | v2_struct_0(B_441)
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_137])).

tff(c_399,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_388])).

tff(c_404,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_62,c_62,c_399])).

tff(c_405,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64,c_404])).

tff(c_292,plain,
    ( v2_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_289])).

tff(c_298,plain,(
    v2_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_292])).

tff(c_344,plain,(
    ! [A_438] :
      ( v1_pre_topc(g1_pre_topc(u1_struct_0(A_438),u1_pre_topc(A_438)))
      | ~ l1_pre_topc(A_438)
      | ~ v2_pre_topc(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_350,plain,
    ( v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_344])).

tff(c_360,plain,(
    v1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_170,c_182,c_350])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_500,plain,(
    ! [A_453,B_454,C_455] :
      ( u1_struct_0(k1_tsep_1(A_453,B_454,C_455)) = k2_xboole_0(u1_struct_0(B_454),u1_struct_0(C_455))
      | ~ m1_pre_topc(k1_tsep_1(A_453,B_454,C_455),A_453)
      | ~ v1_pre_topc(k1_tsep_1(A_453,B_454,C_455))
      | v2_struct_0(k1_tsep_1(A_453,B_454,C_455))
      | ~ m1_pre_topc(C_455,A_453)
      | v2_struct_0(C_455)
      | ~ m1_pre_topc(B_454,A_453)
      | v2_struct_0(B_454)
      | ~ l1_pre_topc(A_453)
      | v2_struct_0(A_453) ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_504,plain,
    ( k2_xboole_0(u1_struct_0('#skF_3'),u1_struct_0('#skF_3')) = u1_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_1')
    | ~ v1_pre_topc(k1_tsep_1('#skF_1','#skF_3','#skF_3'))
    | v2_struct_0(k1_tsep_1('#skF_1','#skF_3','#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_3','#skF_1')
    | v2_struct_0('#skF_3')
    | ~ l1_pre_topc('#skF_1')
    | v2_struct_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_373,c_500])).

tff(c_509,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_62,c_62,c_373,c_360,c_373,c_58,c_181,c_373,c_2,c_177,c_177,c_504])).

tff(c_510,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_64,c_60,c_509])).

tff(c_516,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_177])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_258])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_688,plain,(
    ! [F_475,B_481,A_479,E_477,H_478,D_476,C_480] :
      ( r1_tmap_1(D_476,B_481,E_477,H_478)
      | ~ r1_tmap_1(C_480,B_481,k3_tmap_1(A_479,B_481,D_476,C_480,E_477),H_478)
      | ~ r1_tarski(F_475,u1_struct_0(C_480))
      | ~ r2_hidden(H_478,F_475)
      | ~ v3_pre_topc(F_475,D_476)
      | ~ m1_subset_1(H_478,u1_struct_0(C_480))
      | ~ m1_subset_1(H_478,u1_struct_0(D_476))
      | ~ m1_subset_1(F_475,k1_zfmisc_1(u1_struct_0(D_476)))
      | ~ m1_pre_topc(C_480,D_476)
      | ~ m1_subset_1(E_477,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_476),u1_struct_0(B_481))))
      | ~ v1_funct_2(E_477,u1_struct_0(D_476),u1_struct_0(B_481))
      | ~ v1_funct_1(E_477)
      | ~ m1_pre_topc(D_476,A_479)
      | v2_struct_0(D_476)
      | ~ m1_pre_topc(C_480,A_479)
      | v2_struct_0(C_480)
      | ~ l1_pre_topc(B_481)
      | ~ v2_pre_topc(B_481)
      | v2_struct_0(B_481)
      | ~ l1_pre_topc(A_479)
      | ~ v2_pre_topc(A_479)
      | v2_struct_0(A_479) ) ),
    inference(cnfTransformation,[status(thm)],[f_209])).

tff(c_690,plain,(
    ! [F_475] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_475,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_475)
      | ~ v3_pre_topc(F_475,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_475,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_78,c_688])).

tff(c_693,plain,(
    ! [F_475] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_475,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_475)
      | ~ v3_pre_topc(F_475,'#skF_4')
      | ~ m1_subset_1(F_475,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_207,c_110,c_181,c_276,c_110,c_181,c_405,c_181,c_208,c_181,c_208,c_516,c_516,c_690])).

tff(c_758,plain,(
    ! [F_483] :
      ( ~ r1_tarski(F_483,k2_struct_0('#skF_4'))
      | ~ r2_hidden('#skF_6',F_483)
      | ~ v3_pre_topc(F_483,'#skF_4')
      | ~ m1_subset_1(F_483,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_693])).

tff(c_761,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_261,c_758])).

tff(c_768,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_271,c_761])).

tff(c_770,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_768])).

tff(c_773,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_770])).

tff(c_777,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_173,c_773])).

tff(c_778,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_768])).

tff(c_782,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4,c_778])).

tff(c_785,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_782])).

tff(c_787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:20:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.61/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.57  
% 3.61/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.57  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k1_tsep_1 > k2_zfmisc_1 > k2_xboole_0 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.61/1.57  
% 3.61/1.57  %Foreground sorts:
% 3.61/1.57  
% 3.61/1.57  
% 3.61/1.57  %Background operators:
% 3.61/1.57  
% 3.61/1.57  
% 3.61/1.57  %Foreground operators:
% 3.61/1.57  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.61/1.57  tff(k1_tsep_1, type, k1_tsep_1: ($i * $i * $i) > $i).
% 3.61/1.57  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.61/1.57  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.61/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.61/1.57  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.61/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.61/1.57  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.61/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.61/1.57  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.61/1.57  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.61/1.57  tff('#skF_7', type, '#skF_7': $i).
% 3.61/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.61/1.57  tff('#skF_5', type, '#skF_5': $i).
% 3.61/1.57  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.61/1.57  tff('#skF_6', type, '#skF_6': $i).
% 3.61/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.61/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.61/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.61/1.57  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 3.61/1.57  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.61/1.57  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.61/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.61/1.57  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.61/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.61/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.61/1.57  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.61/1.57  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.61/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.61/1.57  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.61/1.57  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.61/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.61/1.57  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.61/1.57  
% 3.61/1.59  tff(f_258, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.61/1.59  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.61/1.59  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.61/1.59  tff(f_50, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.61/1.59  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.61/1.59  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.61/1.59  tff(f_46, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.61/1.59  tff(f_87, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.61/1.59  tff(f_54, axiom, (![A]: (l1_struct_0(A) => m1_subset_1(k2_struct_0(A), k1_zfmisc_1(u1_struct_0(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_struct_0)).
% 3.61/1.59  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.61/1.59  tff(f_152, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (k1_tsep_1(A, B, B) = g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_tmap_1)).
% 3.61/1.59  tff(f_137, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => m1_pre_topc(B, k1_tsep_1(A, B, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_tsep_1)).
% 3.61/1.59  tff(f_81, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (v1_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) & v2_pre_topc(g1_pre_topc(u1_struct_0(A), u1_pre_topc(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_pre_topc)).
% 3.61/1.59  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.61/1.59  tff(f_116, axiom, (![A]: ((~v2_struct_0(A) & l1_pre_topc(A)) => (![B]: ((~v2_struct_0(B) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: (((~v2_struct_0(D) & v1_pre_topc(D)) & m1_pre_topc(D, A)) => ((D = k1_tsep_1(A, B, C)) <=> (u1_struct_0(D) = k2_xboole_0(u1_struct_0(B), u1_struct_0(C)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tsep_1)).
% 3.61/1.59  tff(f_209, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.61/1.59  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_161, plain, (![B_426, A_427]: (l1_pre_topc(B_426) | ~m1_pre_topc(B_426, A_427) | ~l1_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.61/1.59  tff(c_167, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_161])).
% 3.61/1.59  tff(c_173, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_167])).
% 3.61/1.59  tff(c_16, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.61/1.59  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_97, plain, (![A_421]: (u1_struct_0(A_421)=k2_struct_0(A_421) | ~l1_struct_0(A_421))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.61/1.59  tff(c_101, plain, (![A_12]: (u1_struct_0(A_12)=k2_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_16, c_97])).
% 3.61/1.59  tff(c_181, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_173, c_101])).
% 3.61/1.59  tff(c_20, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.61/1.59  tff(c_212, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_181, c_20])).
% 3.61/1.59  tff(c_215, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_212])).
% 3.61/1.59  tff(c_222, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_215])).
% 3.61/1.59  tff(c_225, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_16, c_222])).
% 3.61/1.59  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_173, c_225])).
% 3.61/1.59  tff(c_230, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_215])).
% 3.61/1.59  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_208, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_48])).
% 3.61/1.59  tff(c_4, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.61/1.59  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_289, plain, (![B_434, A_435]: (v2_pre_topc(B_434) | ~m1_pre_topc(B_434, A_435) | ~l1_pre_topc(A_435) | ~v2_pre_topc(A_435))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.61/1.59  tff(c_295, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_289])).
% 3.61/1.59  tff(c_301, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_295])).
% 3.61/1.59  tff(c_26, plain, (![A_18]: (v3_pre_topc(k2_struct_0(A_18), A_18) | ~l1_pre_topc(A_18) | ~v2_pre_topc(A_18))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.61/1.59  tff(c_231, plain, (l1_struct_0('#skF_4')), inference(splitRight, [status(thm)], [c_215])).
% 3.61/1.59  tff(c_243, plain, (![A_433]: (m1_subset_1(k2_struct_0(A_433), k1_zfmisc_1(u1_struct_0(A_433))) | ~l1_struct_0(A_433))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.61/1.59  tff(c_249, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~l1_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_181, c_243])).
% 3.61/1.59  tff(c_261, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_231, c_249])).
% 3.61/1.59  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.61/1.59  tff(c_271, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_261, c_6])).
% 3.61/1.59  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_102, plain, (![A_422]: (u1_struct_0(A_422)=k2_struct_0(A_422) | ~l1_pre_topc(A_422))), inference(resolution, [status(thm)], [c_16, c_97])).
% 3.61/1.59  tff(c_110, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_102])).
% 3.61/1.59  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_116, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_54])).
% 3.61/1.59  tff(c_207, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_116])).
% 3.61/1.59  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_115, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_110, c_52])).
% 3.61/1.59  tff(c_276, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_115])).
% 3.61/1.59  tff(c_164, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_161])).
% 3.61/1.59  tff(c_170, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_164])).
% 3.61/1.59  tff(c_177, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_170, c_101])).
% 3.61/1.59  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_182, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_177, c_50])).
% 3.61/1.59  tff(c_365, plain, (![A_439, B_440]: (k1_tsep_1(A_439, B_440, B_440)=g1_pre_topc(u1_struct_0(B_440), u1_pre_topc(B_440)) | ~m1_pre_topc(B_440, A_439) | v2_struct_0(B_440) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439) | v2_struct_0(A_439))), inference(cnfTransformation, [status(thm)], [f_152])).
% 3.61/1.59  tff(c_367, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))=k1_tsep_1('#skF_1', '#skF_3', '#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(resolution, [status(thm)], [c_62, c_365])).
% 3.61/1.59  tff(c_372, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4' | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_182, c_177, c_367])).
% 3.61/1.59  tff(c_373, plain, (k1_tsep_1('#skF_1', '#skF_3', '#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_76, c_64, c_372])).
% 3.61/1.59  tff(c_388, plain, (![B_441, A_442, C_443]: (m1_pre_topc(B_441, k1_tsep_1(A_442, B_441, C_443)) | ~m1_pre_topc(C_443, A_442) | v2_struct_0(C_443) | ~m1_pre_topc(B_441, A_442) | v2_struct_0(B_441) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(cnfTransformation, [status(thm)], [f_137])).
% 3.61/1.59  tff(c_399, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_373, c_388])).
% 3.61/1.59  tff(c_404, plain, (m1_pre_topc('#skF_3', '#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_62, c_62, c_399])).
% 3.61/1.59  tff(c_405, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_64, c_404])).
% 3.61/1.59  tff(c_292, plain, (v2_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_289])).
% 3.61/1.59  tff(c_298, plain, (v2_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_292])).
% 3.61/1.59  tff(c_344, plain, (![A_438]: (v1_pre_topc(g1_pre_topc(u1_struct_0(A_438), u1_pre_topc(A_438))) | ~l1_pre_topc(A_438) | ~v2_pre_topc(A_438))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.61/1.59  tff(c_350, plain, (v1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_177, c_344])).
% 3.61/1.59  tff(c_360, plain, (v1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_170, c_182, c_350])).
% 3.61/1.59  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.61/1.59  tff(c_500, plain, (![A_453, B_454, C_455]: (u1_struct_0(k1_tsep_1(A_453, B_454, C_455))=k2_xboole_0(u1_struct_0(B_454), u1_struct_0(C_455)) | ~m1_pre_topc(k1_tsep_1(A_453, B_454, C_455), A_453) | ~v1_pre_topc(k1_tsep_1(A_453, B_454, C_455)) | v2_struct_0(k1_tsep_1(A_453, B_454, C_455)) | ~m1_pre_topc(C_455, A_453) | v2_struct_0(C_455) | ~m1_pre_topc(B_454, A_453) | v2_struct_0(B_454) | ~l1_pre_topc(A_453) | v2_struct_0(A_453))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.61/1.59  tff(c_504, plain, (k2_xboole_0(u1_struct_0('#skF_3'), u1_struct_0('#skF_3'))=u1_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_1') | ~v1_pre_topc(k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | v2_struct_0(k1_tsep_1('#skF_1', '#skF_3', '#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_1') | v2_struct_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_373, c_500])).
% 3.61/1.59  tff(c_509, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_62, c_62, c_373, c_360, c_373, c_58, c_181, c_373, c_2, c_177, c_177, c_504])).
% 3.61/1.59  tff(c_510, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_76, c_64, c_60, c_509])).
% 3.61/1.59  tff(c_516, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_510, c_177])).
% 3.61/1.59  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_258])).
% 3.61/1.59  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 3.61/1.59  tff(c_688, plain, (![F_475, B_481, A_479, E_477, H_478, D_476, C_480]: (r1_tmap_1(D_476, B_481, E_477, H_478) | ~r1_tmap_1(C_480, B_481, k3_tmap_1(A_479, B_481, D_476, C_480, E_477), H_478) | ~r1_tarski(F_475, u1_struct_0(C_480)) | ~r2_hidden(H_478, F_475) | ~v3_pre_topc(F_475, D_476) | ~m1_subset_1(H_478, u1_struct_0(C_480)) | ~m1_subset_1(H_478, u1_struct_0(D_476)) | ~m1_subset_1(F_475, k1_zfmisc_1(u1_struct_0(D_476))) | ~m1_pre_topc(C_480, D_476) | ~m1_subset_1(E_477, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_476), u1_struct_0(B_481)))) | ~v1_funct_2(E_477, u1_struct_0(D_476), u1_struct_0(B_481)) | ~v1_funct_1(E_477) | ~m1_pre_topc(D_476, A_479) | v2_struct_0(D_476) | ~m1_pre_topc(C_480, A_479) | v2_struct_0(C_480) | ~l1_pre_topc(B_481) | ~v2_pre_topc(B_481) | v2_struct_0(B_481) | ~l1_pre_topc(A_479) | ~v2_pre_topc(A_479) | v2_struct_0(A_479))), inference(cnfTransformation, [status(thm)], [f_209])).
% 3.61/1.59  tff(c_690, plain, (![F_475]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_475, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_475) | ~v3_pre_topc(F_475, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_475, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_688])).
% 3.61/1.59  tff(c_693, plain, (![F_475]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_475, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_475) | ~v3_pre_topc(F_475, '#skF_4') | ~m1_subset_1(F_475, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_207, c_110, c_181, c_276, c_110, c_181, c_405, c_181, c_208, c_181, c_208, c_516, c_516, c_690])).
% 3.61/1.59  tff(c_758, plain, (![F_483]: (~r1_tarski(F_483, k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', F_483) | ~v3_pre_topc(F_483, '#skF_4') | ~m1_subset_1(F_483, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_693])).
% 3.61/1.59  tff(c_761, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_261, c_758])).
% 3.61/1.59  tff(c_768, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_271, c_761])).
% 3.61/1.59  tff(c_770, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_768])).
% 3.61/1.59  tff(c_773, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_770])).
% 3.61/1.59  tff(c_777, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_301, c_173, c_773])).
% 3.61/1.59  tff(c_778, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_768])).
% 3.61/1.59  tff(c_782, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_4, c_778])).
% 3.61/1.59  tff(c_785, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_208, c_782])).
% 3.61/1.59  tff(c_787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_785])).
% 3.61/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.61/1.59  
% 3.61/1.59  Inference rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Ref     : 1
% 3.61/1.59  #Sup     : 151
% 3.61/1.59  #Fact    : 0
% 3.61/1.59  #Define  : 0
% 3.61/1.59  #Split   : 7
% 3.61/1.59  #Chain   : 0
% 3.61/1.59  #Close   : 0
% 3.61/1.59  
% 3.61/1.59  Ordering : KBO
% 3.61/1.59  
% 3.61/1.59  Simplification rules
% 3.61/1.59  ----------------------
% 3.61/1.59  #Subsume      : 8
% 3.61/1.59  #Demod        : 237
% 3.61/1.59  #Tautology    : 67
% 3.61/1.59  #SimpNegUnit  : 57
% 3.61/1.59  #BackRed      : 17
% 3.61/1.59  
% 3.61/1.59  #Partial instantiations: 0
% 3.61/1.59  #Strategies tried      : 1
% 3.61/1.59  
% 3.61/1.59  Timing (in seconds)
% 3.61/1.59  ----------------------
% 3.61/1.59  Preprocessing        : 0.40
% 3.61/1.59  Parsing              : 0.20
% 3.61/1.59  CNF conversion       : 0.05
% 3.61/1.60  Main loop            : 0.42
% 3.61/1.60  Inferencing          : 0.14
% 3.61/1.60  Reduction            : 0.15
% 3.61/1.60  Demodulation         : 0.11
% 3.61/1.60  BG Simplification    : 0.03
% 3.61/1.60  Subsumption          : 0.08
% 3.61/1.60  Abstraction          : 0.02
% 3.61/1.60  MUC search           : 0.00
% 3.61/1.60  Cooper               : 0.00
% 3.61/1.60  Total                : 0.86
% 3.61/1.60  Index Insertion      : 0.00
% 3.61/1.60  Index Deletion       : 0.00
% 3.61/1.60  Index Matching       : 0.00
% 3.61/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
