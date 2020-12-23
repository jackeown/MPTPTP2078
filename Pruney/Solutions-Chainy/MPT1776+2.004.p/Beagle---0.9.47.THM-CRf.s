%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:30 EST 2020

% Result     : Theorem 5.35s
% Output     : CNFRefutation 5.58s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 694 expanded)
%              Number of leaves         :   44 ( 266 expanded)
%              Depth                    :   18
%              Number of atoms          :  603 (4572 expanded)
%              Number of equality atoms :   32 ( 192 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(m1_pre_topc,type,(
    m1_pre_topc: ( $i * $i ) > $o )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v2_pre_topc,type,(
    v2_pre_topc: $i > $o )).

tff(k2_tmap_1,type,(
    k2_tmap_1: ( $i * $i * $i * $i ) > $i )).

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_325,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_tmap_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_178,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(f_72,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_171,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tsep_1)).

tff(f_147,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( m1_pre_topc(C,A)
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => ! [E] :
                      ( ( v1_funct_1(E)
                        & v1_funct_2(E,u1_struct_0(C),u1_struct_0(B))
                        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C),u1_struct_0(B)))) )
                     => ( m1_pre_topc(D,C)
                       => k3_tmap_1(A,B,C,D,E) = k2_partfun1(u1_struct_0(C),u1_struct_0(B),E,u1_struct_0(D)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_115,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(A),u1_struct_0(B))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A),u1_struct_0(B)))) )
             => ! [D] :
                  ( m1_pre_topc(D,A)
                 => k2_tmap_1(A,B,C,D) = k2_partfun1(u1_struct_0(A),u1_struct_0(B),C,u1_struct_0(D)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_260,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & v1_tsep_1(D,B)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( E = F
                           => ( r1_tmap_1(B,A,C,E)
                            <=> r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_218,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( ( ~ v2_struct_0(B)
            & v2_pre_topc(B)
            & l1_pre_topc(B) )
         => ! [C] :
              ( ( v1_funct_1(C)
                & v1_funct_2(C,u1_struct_0(B),u1_struct_0(A))
                & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B),u1_struct_0(A)))) )
             => ! [D] :
                  ( ( ~ v2_struct_0(D)
                    & m1_pre_topc(D,B) )
                 => ! [E] :
                      ( m1_subset_1(E,u1_struct_0(B))
                     => ! [F] :
                          ( m1_subset_1(F,u1_struct_0(D))
                         => ( ( E = F
                              & r1_tmap_1(B,A,C,E) )
                           => r1_tmap_1(D,A,k2_tmap_1(B,A,C,D),F) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_46,plain,(
    m1_pre_topc('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_40,plain,(
    '#skF_7' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_88,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_84,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_7')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_84])).

tff(c_135,plain,(
    r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_86])).

tff(c_78,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_87,plain,
    ( ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8')
    | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_78])).

tff(c_173,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_87])).

tff(c_74,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_72,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_58,plain,(
    m1_pre_topc('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_136,plain,(
    ! [B_349,A_350] :
      ( v2_pre_topc(B_349)
      | ~ m1_pre_topc(B_349,A_350)
      | ~ l1_pre_topc(A_350)
      | ~ v2_pre_topc(A_350) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_142,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_136])).

tff(c_151,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_142])).

tff(c_94,plain,(
    ! [B_336,A_337] :
      ( l1_pre_topc(B_336)
      | ~ m1_pre_topc(B_336,A_337)
      | ~ l1_pre_topc(A_337) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_100,plain,
    ( l1_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_94])).

tff(c_109,plain,(
    l1_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_100])).

tff(c_56,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_54,plain,(
    v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_52,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_62,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_97,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_94])).

tff(c_106,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_97])).

tff(c_14,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( r2_hidden(A_6,B_7)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_168,plain,(
    ! [B_357,A_358] :
      ( m1_subset_1(u1_struct_0(B_357),k1_zfmisc_1(u1_struct_0(A_358)))
      | ~ m1_pre_topc(B_357,A_358)
      | ~ l1_pre_topc(A_358) ) ),
    inference(cnfTransformation,[status(thm)],[f_178])).

tff(c_10,plain,(
    ! [A_8,C_10,B_9] :
      ( m1_subset_1(A_8,C_10)
      | ~ m1_subset_1(B_9,k1_zfmisc_1(C_10))
      | ~ r2_hidden(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_264,plain,(
    ! [A_378,A_379,B_380] :
      ( m1_subset_1(A_378,u1_struct_0(A_379))
      | ~ r2_hidden(A_378,u1_struct_0(B_380))
      | ~ m1_pre_topc(B_380,A_379)
      | ~ l1_pre_topc(A_379) ) ),
    inference(resolution,[status(thm)],[c_168,c_10])).

tff(c_281,plain,(
    ! [A_385,A_386,B_387] :
      ( m1_subset_1(A_385,u1_struct_0(A_386))
      | ~ m1_pre_topc(B_387,A_386)
      | ~ l1_pre_topc(A_386)
      | v1_xboole_0(u1_struct_0(B_387))
      | ~ m1_subset_1(A_385,u1_struct_0(B_387)) ) ),
    inference(resolution,[status(thm)],[c_8,c_264])).

tff(c_285,plain,(
    ! [A_385] :
      ( m1_subset_1(A_385,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_385,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_62,c_281])).

tff(c_293,plain,(
    ! [A_385] :
      ( m1_subset_1(A_385,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_385,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_285])).

tff(c_305,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_293])).

tff(c_18,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_308,plain,
    ( ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_305,c_18])).

tff(c_311,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_308])).

tff(c_314,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_311])).

tff(c_318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_314])).

tff(c_320,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_504,plain,(
    ! [B_414,B_415,A_416] :
      ( m1_subset_1('#skF_1'(u1_struct_0(B_414),B_415),u1_struct_0(A_416))
      | ~ m1_pre_topc(B_414,A_416)
      | ~ l1_pre_topc(A_416)
      | r1_tarski(u1_struct_0(B_414),B_415) ) ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_341,plain,(
    ! [A_395] :
      ( m1_subset_1(A_395,u1_struct_0('#skF_3'))
      | ~ m1_subset_1(A_395,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_293])).

tff(c_122,plain,(
    ! [A_344,B_345] :
      ( r2_hidden(A_344,B_345)
      | v1_xboole_0(B_345)
      | ~ m1_subset_1(A_344,B_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_127,plain,(
    ! [A_1,B_345] :
      ( r1_tarski(A_1,B_345)
      | v1_xboole_0(B_345)
      | ~ m1_subset_1('#skF_1'(A_1,B_345),B_345) ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_351,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_341,c_127])).

tff(c_419,plain,(
    v1_xboole_0(u1_struct_0('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_351])).

tff(c_422,plain,
    ( ~ l1_struct_0('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_419,c_18])).

tff(c_425,plain,(
    ~ l1_struct_0('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_422])).

tff(c_428,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_425])).

tff(c_432,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_428])).

tff(c_433,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0('#skF_3')),u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_351])).

tff(c_518,plain,(
    ! [B_414] :
      ( ~ m1_pre_topc(B_414,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | r1_tarski(u1_struct_0(B_414),u1_struct_0('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_504,c_433])).

tff(c_571,plain,(
    ! [B_420] :
      ( ~ m1_pre_topc(B_420,'#skF_4')
      | r1_tarski(u1_struct_0(B_420),u1_struct_0('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_518])).

tff(c_128,plain,(
    ! [C_346,B_347,A_348] :
      ( r2_hidden(C_346,B_347)
      | ~ r2_hidden(C_346,A_348)
      | ~ r1_tarski(A_348,B_347) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_133,plain,(
    ! [A_6,B_347,B_7] :
      ( r2_hidden(A_6,B_347)
      | ~ r1_tarski(B_7,B_347)
      | v1_xboole_0(B_7)
      | ~ m1_subset_1(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_8,c_128])).

tff(c_631,plain,(
    ! [A_426,B_427] :
      ( r2_hidden(A_426,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0(B_427))
      | ~ m1_subset_1(A_426,u1_struct_0(B_427))
      | ~ m1_pre_topc(B_427,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_571,c_133])).

tff(c_649,plain,
    ( r2_hidden('#skF_8',u1_struct_0('#skF_3'))
    | v1_xboole_0(u1_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_631])).

tff(c_667,plain,
    ( r2_hidden('#skF_8',u1_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_649])).

tff(c_678,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_667])).

tff(c_50,plain,(
    v1_tsep_1('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_325])).

tff(c_115,plain,(
    ! [A_341,B_342] :
      ( r2_hidden('#skF_1'(A_341,B_342),A_341)
      | r1_tarski(A_341,B_342) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_120,plain,(
    ! [A_341] : r1_tarski(A_341,A_341) ),
    inference(resolution,[status(thm)],[c_115,c_4])).

tff(c_336,plain,(
    ! [B_392,C_393,A_394] :
      ( m1_pre_topc(B_392,C_393)
      | ~ r1_tarski(u1_struct_0(B_392),u1_struct_0(C_393))
      | ~ m1_pre_topc(C_393,A_394)
      | v2_struct_0(C_393)
      | ~ m1_pre_topc(B_392,A_394)
      | ~ v1_tsep_1(B_392,A_394)
      | ~ l1_pre_topc(A_394)
      | ~ v2_pre_topc(A_394)
      | v2_struct_0(A_394) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_1172,plain,(
    ! [B_471,A_472] :
      ( m1_pre_topc(B_471,B_471)
      | v2_struct_0(B_471)
      | ~ m1_pre_topc(B_471,A_472)
      | ~ v1_tsep_1(B_471,A_472)
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(resolution,[status(thm)],[c_120,c_336])).

tff(c_1174,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_1172])).

tff(c_1177,plain,
    ( m1_pre_topc('#skF_4','#skF_4')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_62,c_1174])).

tff(c_1179,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_64,c_678,c_1177])).

tff(c_1181,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_667])).

tff(c_287,plain,(
    ! [A_385] :
      ( m1_subset_1(A_385,u1_struct_0('#skF_3'))
      | ~ l1_pre_topc('#skF_3')
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_385,u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_58,c_281])).

tff(c_296,plain,(
    ! [A_385] :
      ( m1_subset_1(A_385,u1_struct_0('#skF_3'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_385,u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_287])).

tff(c_352,plain,(
    v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_296])).

tff(c_355,plain,
    ( ~ l1_struct_0('#skF_5')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_352,c_18])).

tff(c_358,plain,(
    ~ l1_struct_0('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_355])).

tff(c_361,plain,(
    ~ l1_pre_topc('#skF_5') ),
    inference(resolution,[status(thm)],[c_14,c_358])).

tff(c_365,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_361])).

tff(c_367,plain,(
    ~ v1_xboole_0(u1_struct_0('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_296])).

tff(c_289,plain,(
    ! [A_385] :
      ( m1_subset_1(A_385,u1_struct_0('#skF_5'))
      | ~ l1_pre_topc('#skF_5')
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_385,u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_46,c_281])).

tff(c_299,plain,(
    ! [A_385] :
      ( m1_subset_1(A_385,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_4'))
      | ~ m1_subset_1(A_385,u1_struct_0('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_289])).

tff(c_321,plain,(
    v1_xboole_0(u1_struct_0('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_299])).

tff(c_322,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_320,c_321])).

tff(c_325,plain,(
    ! [A_391] :
      ( m1_subset_1(A_391,u1_struct_0('#skF_5'))
      | ~ m1_subset_1(A_391,u1_struct_0('#skF_4')) ) ),
    inference(splitRight,[status(thm)],[c_299])).

tff(c_335,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_5'))
      | v1_xboole_0(u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0('#skF_5')),u1_struct_0('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_325,c_127])).

tff(c_436,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,u1_struct_0('#skF_5'))
      | ~ m1_subset_1('#skF_1'(A_1,u1_struct_0('#skF_5')),u1_struct_0('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_367,c_335])).

tff(c_514,plain,(
    ! [B_414] :
      ( ~ m1_pre_topc(B_414,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | r1_tarski(u1_struct_0(B_414),u1_struct_0('#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_504,c_436])).

tff(c_546,plain,(
    ! [B_417] :
      ( ~ m1_pre_topc(B_417,'#skF_4')
      | r1_tarski(u1_struct_0(B_417),u1_struct_0('#skF_5')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_106,c_514])).

tff(c_28,plain,(
    ! [B_76,C_78,A_72] :
      ( v1_tsep_1(B_76,C_78)
      | ~ r1_tarski(u1_struct_0(B_76),u1_struct_0(C_78))
      | ~ m1_pre_topc(C_78,A_72)
      | v2_struct_0(C_78)
      | ~ m1_pre_topc(B_76,A_72)
      | ~ v1_tsep_1(B_76,A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_171])).

tff(c_550,plain,(
    ! [B_417,A_72] :
      ( v1_tsep_1(B_417,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_72)
      | v2_struct_0('#skF_5')
      | ~ m1_pre_topc(B_417,A_72)
      | ~ v1_tsep_1(B_417,A_72)
      | ~ l1_pre_topc(A_72)
      | ~ v2_pre_topc(A_72)
      | v2_struct_0(A_72)
      | ~ m1_pre_topc(B_417,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_546,c_28])).

tff(c_1414,plain,(
    ! [B_487,A_488] :
      ( v1_tsep_1(B_487,'#skF_5')
      | ~ m1_pre_topc('#skF_5',A_488)
      | ~ m1_pre_topc(B_487,A_488)
      | ~ v1_tsep_1(B_487,A_488)
      | ~ l1_pre_topc(A_488)
      | ~ v2_pre_topc(A_488)
      | v2_struct_0(A_488)
      | ~ m1_pre_topc(B_487,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_550])).

tff(c_1416,plain,
    ( v1_tsep_1('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3')
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_1414])).

tff(c_1419,plain,
    ( v1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1181,c_68,c_66,c_62,c_58,c_1416])).

tff(c_1420,plain,(
    v1_tsep_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1419])).

tff(c_488,plain,(
    ! [E_409,B_410,A_408,C_411,D_412] :
      ( k3_tmap_1(A_408,B_410,C_411,D_412,E_409) = k2_partfun1(u1_struct_0(C_411),u1_struct_0(B_410),E_409,u1_struct_0(D_412))
      | ~ m1_pre_topc(D_412,C_411)
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_411),u1_struct_0(B_410))))
      | ~ v1_funct_2(E_409,u1_struct_0(C_411),u1_struct_0(B_410))
      | ~ v1_funct_1(E_409)
      | ~ m1_pre_topc(D_412,A_408)
      | ~ m1_pre_topc(C_411,A_408)
      | ~ l1_pre_topc(B_410)
      | ~ v2_pre_topc(B_410)
      | v2_struct_0(B_410)
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_490,plain,(
    ! [A_408,D_412] :
      ( k3_tmap_1(A_408,'#skF_2','#skF_5',D_412,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_412))
      | ~ m1_pre_topc(D_412,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_412,A_408)
      | ~ m1_pre_topc('#skF_5',A_408)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(resolution,[status(thm)],[c_52,c_488])).

tff(c_493,plain,(
    ! [A_408,D_412] :
      ( k3_tmap_1(A_408,'#skF_2','#skF_5',D_412,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_412))
      | ~ m1_pre_topc(D_412,'#skF_5')
      | ~ m1_pre_topc(D_412,A_408)
      | ~ m1_pre_topc('#skF_5',A_408)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_408)
      | ~ v2_pre_topc(A_408)
      | v2_struct_0(A_408) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_56,c_54,c_490])).

tff(c_1632,plain,(
    ! [A_506,D_507] :
      ( k3_tmap_1(A_506,'#skF_2','#skF_5',D_507,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_507))
      | ~ m1_pre_topc(D_507,'#skF_5')
      | ~ m1_pre_topc(D_507,A_506)
      | ~ m1_pre_topc('#skF_5',A_506)
      | ~ l1_pre_topc(A_506)
      | ~ v2_pre_topc(A_506)
      | v2_struct_0(A_506) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_493])).

tff(c_1638,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_1632])).

tff(c_1650,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_58,c_46,c_1638])).

tff(c_1651,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_1650])).

tff(c_400,plain,(
    ! [A_397,B_398,C_399,D_400] :
      ( k2_partfun1(u1_struct_0(A_397),u1_struct_0(B_398),C_399,u1_struct_0(D_400)) = k2_tmap_1(A_397,B_398,C_399,D_400)
      | ~ m1_pre_topc(D_400,A_397)
      | ~ m1_subset_1(C_399,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397),u1_struct_0(B_398))))
      | ~ v1_funct_2(C_399,u1_struct_0(A_397),u1_struct_0(B_398))
      | ~ v1_funct_1(C_399)
      | ~ l1_pre_topc(B_398)
      | ~ v2_pre_topc(B_398)
      | v2_struct_0(B_398)
      | ~ l1_pre_topc(A_397)
      | ~ v2_pre_topc(A_397)
      | v2_struct_0(A_397) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_402,plain,(
    ! [D_400] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_400)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_400)
      | ~ m1_pre_topc(D_400,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_400])).

tff(c_405,plain,(
    ! [D_400] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_400)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_400)
      | ~ m1_pre_topc(D_400,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_151,c_109,c_74,c_72,c_56,c_54,c_402])).

tff(c_406,plain,(
    ! [D_400] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_400)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_400)
      | ~ m1_pre_topc(D_400,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_76,c_405])).

tff(c_1663,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_1651,c_406])).

tff(c_1670,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_1663])).

tff(c_1675,plain,(
    r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1670,c_135])).

tff(c_34,plain,(
    ! [B_177,C_193,A_145,D_201,F_207] :
      ( r1_tmap_1(B_177,A_145,C_193,F_207)
      | ~ r1_tmap_1(D_201,A_145,k2_tmap_1(B_177,A_145,C_193,D_201),F_207)
      | ~ m1_subset_1(F_207,u1_struct_0(D_201))
      | ~ m1_subset_1(F_207,u1_struct_0(B_177))
      | ~ m1_pre_topc(D_201,B_177)
      | ~ v1_tsep_1(D_201,B_177)
      | v2_struct_0(D_201)
      | ~ m1_subset_1(C_193,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_177),u1_struct_0(A_145))))
      | ~ v1_funct_2(C_193,u1_struct_0(B_177),u1_struct_0(A_145))
      | ~ v1_funct_1(C_193)
      | ~ l1_pre_topc(B_177)
      | ~ v2_pre_topc(B_177)
      | v2_struct_0(B_177)
      | ~ l1_pre_topc(A_145)
      | ~ v2_pre_topc(A_145)
      | v2_struct_0(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_260])).

tff(c_1681,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ v1_tsep_1('#skF_4','#skF_5')
    | v2_struct_0('#skF_4')
    | ~ m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))))
    | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
    | ~ v1_funct_1('#skF_6')
    | ~ l1_pre_topc('#skF_5')
    | ~ v2_pre_topc('#skF_5')
    | v2_struct_0('#skF_5')
    | ~ l1_pre_topc('#skF_2')
    | ~ v2_pre_topc('#skF_2')
    | v2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_1675,c_34])).

tff(c_1684,plain,
    ( r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | v2_struct_0('#skF_4')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_151,c_109,c_56,c_54,c_52,c_1420,c_46,c_88,c_42,c_1681])).

tff(c_1686,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_60,c_64,c_173,c_1684])).

tff(c_1687,plain,(
    r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitRight,[status(thm)],[c_86])).

tff(c_1695,plain,(
    ! [B_508,A_509] :
      ( v2_pre_topc(B_508)
      | ~ m1_pre_topc(B_508,A_509)
      | ~ l1_pre_topc(A_509)
      | ~ v2_pre_topc(A_509) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1701,plain,
    ( v2_pre_topc('#skF_5')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1695])).

tff(c_1710,plain,(
    v2_pre_topc('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_1701])).

tff(c_2322,plain,(
    ! [B_590,D_592,F_591,A_594,C_593] :
      ( r1_tmap_1(D_592,A_594,k2_tmap_1(B_590,A_594,C_593,D_592),F_591)
      | ~ r1_tmap_1(B_590,A_594,C_593,F_591)
      | ~ m1_subset_1(F_591,u1_struct_0(D_592))
      | ~ m1_subset_1(F_591,u1_struct_0(B_590))
      | ~ m1_pre_topc(D_592,B_590)
      | v2_struct_0(D_592)
      | ~ m1_subset_1(C_593,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_590),u1_struct_0(A_594))))
      | ~ v1_funct_2(C_593,u1_struct_0(B_590),u1_struct_0(A_594))
      | ~ v1_funct_1(C_593)
      | ~ l1_pre_topc(B_590)
      | ~ v2_pre_topc(B_590)
      | v2_struct_0(B_590)
      | ~ l1_pre_topc(A_594)
      | ~ v2_pre_topc(A_594)
      | v2_struct_0(A_594) ) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_2324,plain,(
    ! [D_592,F_591] :
      ( r1_tmap_1(D_592,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_592),F_591)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_591)
      | ~ m1_subset_1(F_591,u1_struct_0(D_592))
      | ~ m1_subset_1(F_591,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_592,'#skF_5')
      | v2_struct_0(D_592)
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_52,c_2322])).

tff(c_2327,plain,(
    ! [D_592,F_591] :
      ( r1_tmap_1(D_592,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_592),F_591)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_591)
      | ~ m1_subset_1(F_591,u1_struct_0(D_592))
      | ~ m1_subset_1(F_591,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_592,'#skF_5')
      | v2_struct_0(D_592)
      | v2_struct_0('#skF_5')
      | v2_struct_0('#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_1710,c_109,c_56,c_54,c_2324])).

tff(c_2328,plain,(
    ! [D_592,F_591] :
      ( r1_tmap_1(D_592,'#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6',D_592),F_591)
      | ~ r1_tmap_1('#skF_5','#skF_2','#skF_6',F_591)
      | ~ m1_subset_1(F_591,u1_struct_0(D_592))
      | ~ m1_subset_1(F_591,u1_struct_0('#skF_5'))
      | ~ m1_pre_topc(D_592,'#skF_5')
      | v2_struct_0(D_592) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_60,c_2327])).

tff(c_2153,plain,(
    ! [A_577,B_579,C_580,D_581,E_578] :
      ( k3_tmap_1(A_577,B_579,C_580,D_581,E_578) = k2_partfun1(u1_struct_0(C_580),u1_struct_0(B_579),E_578,u1_struct_0(D_581))
      | ~ m1_pre_topc(D_581,C_580)
      | ~ m1_subset_1(E_578,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_580),u1_struct_0(B_579))))
      | ~ v1_funct_2(E_578,u1_struct_0(C_580),u1_struct_0(B_579))
      | ~ v1_funct_1(E_578)
      | ~ m1_pre_topc(D_581,A_577)
      | ~ m1_pre_topc(C_580,A_577)
      | ~ l1_pre_topc(B_579)
      | ~ v2_pre_topc(B_579)
      | v2_struct_0(B_579)
      | ~ l1_pre_topc(A_577)
      | ~ v2_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_2155,plain,(
    ! [A_577,D_581] :
      ( k3_tmap_1(A_577,'#skF_2','#skF_5',D_581,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_581))
      | ~ m1_pre_topc(D_581,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ m1_pre_topc(D_581,A_577)
      | ~ m1_pre_topc('#skF_5',A_577)
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_577)
      | ~ v2_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(resolution,[status(thm)],[c_52,c_2153])).

tff(c_2158,plain,(
    ! [A_577,D_581] :
      ( k3_tmap_1(A_577,'#skF_2','#skF_5',D_581,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_581))
      | ~ m1_pre_topc(D_581,'#skF_5')
      | ~ m1_pre_topc(D_581,A_577)
      | ~ m1_pre_topc('#skF_5',A_577)
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc(A_577)
      | ~ v2_pre_topc(A_577)
      | v2_struct_0(A_577) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_56,c_54,c_2155])).

tff(c_2698,plain,(
    ! [A_635,D_636] :
      ( k3_tmap_1(A_635,'#skF_2','#skF_5',D_636,'#skF_6') = k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_636))
      | ~ m1_pre_topc(D_636,'#skF_5')
      | ~ m1_pre_topc(D_636,A_635)
      | ~ m1_pre_topc('#skF_5',A_635)
      | ~ l1_pre_topc(A_635)
      | ~ v2_pre_topc(A_635)
      | v2_struct_0(A_635) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_2158])).

tff(c_2702,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_3')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_62,c_2698])).

tff(c_2710,plain,
    ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_58,c_46,c_2702])).

tff(c_2711,plain,(
    k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0('#skF_4')) = k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_2710])).

tff(c_2010,plain,(
    ! [A_561,B_562,C_563,D_564] :
      ( k2_partfun1(u1_struct_0(A_561),u1_struct_0(B_562),C_563,u1_struct_0(D_564)) = k2_tmap_1(A_561,B_562,C_563,D_564)
      | ~ m1_pre_topc(D_564,A_561)
      | ~ m1_subset_1(C_563,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561),u1_struct_0(B_562))))
      | ~ v1_funct_2(C_563,u1_struct_0(A_561),u1_struct_0(B_562))
      | ~ v1_funct_1(C_563)
      | ~ l1_pre_topc(B_562)
      | ~ v2_pre_topc(B_562)
      | v2_struct_0(B_562)
      | ~ l1_pre_topc(A_561)
      | ~ v2_pre_topc(A_561)
      | v2_struct_0(A_561) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_2012,plain,(
    ! [D_564] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_564)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_564)
      | ~ m1_pre_topc(D_564,'#skF_5')
      | ~ v1_funct_2('#skF_6',u1_struct_0('#skF_5'),u1_struct_0('#skF_2'))
      | ~ v1_funct_1('#skF_6')
      | ~ l1_pre_topc('#skF_2')
      | ~ v2_pre_topc('#skF_2')
      | v2_struct_0('#skF_2')
      | ~ l1_pre_topc('#skF_5')
      | ~ v2_pre_topc('#skF_5')
      | v2_struct_0('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_52,c_2010])).

tff(c_2015,plain,(
    ! [D_564] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_564)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_564)
      | ~ m1_pre_topc(D_564,'#skF_5')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1710,c_109,c_74,c_72,c_56,c_54,c_2012])).

tff(c_2016,plain,(
    ! [D_564] :
      ( k2_partfun1(u1_struct_0('#skF_5'),u1_struct_0('#skF_2'),'#skF_6',u1_struct_0(D_564)) = k2_tmap_1('#skF_5','#skF_2','#skF_6',D_564)
      | ~ m1_pre_topc(D_564,'#skF_5') ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_76,c_2015])).

tff(c_2723,plain,
    ( k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4')
    | ~ m1_pre_topc('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_2711,c_2016])).

tff(c_2730,plain,(
    k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6') = k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2723])).

tff(c_1689,plain,(
    ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_87])).

tff(c_1691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1687,c_1689])).

tff(c_1692,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k3_tmap_1('#skF_3','#skF_2','#skF_5','#skF_4','#skF_6'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_87])).

tff(c_2735,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2',k2_tmap_1('#skF_5','#skF_2','#skF_6','#skF_4'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_1692])).

tff(c_2742,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_2','#skF_6','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_pre_topc('#skF_4','#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_2328,c_2735])).

tff(c_2745,plain,(
    v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_88,c_42,c_1687,c_2742])).

tff(c_2747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_2745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.35/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.97  
% 5.35/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.35/1.98  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4 > #skF_1
% 5.35/1.98  
% 5.35/1.98  %Foreground sorts:
% 5.35/1.98  
% 5.35/1.98  
% 5.35/1.98  %Background operators:
% 5.35/1.98  
% 5.35/1.98  
% 5.35/1.98  %Foreground operators:
% 5.35/1.98  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.35/1.98  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.35/1.98  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.35/1.98  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.35/1.98  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.35/1.98  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.35/1.98  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.35/1.98  tff('#skF_7', type, '#skF_7': $i).
% 5.35/1.98  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.35/1.98  tff('#skF_5', type, '#skF_5': $i).
% 5.35/1.98  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.35/1.98  tff('#skF_6', type, '#skF_6': $i).
% 5.35/1.98  tff('#skF_2', type, '#skF_2': $i).
% 5.35/1.98  tff('#skF_3', type, '#skF_3': $i).
% 5.35/1.98  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.35/1.98  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.35/1.98  tff('#skF_8', type, '#skF_8': $i).
% 5.35/1.98  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.35/1.98  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.35/1.98  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 5.35/1.98  tff('#skF_4', type, '#skF_4': $i).
% 5.35/1.98  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.35/1.98  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.35/1.98  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 5.35/1.98  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.35/1.98  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 5.35/1.98  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.35/1.98  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.35/1.98  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.35/1.98  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.35/1.98  
% 5.58/2.01  tff(f_325, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_tmap_1)).
% 5.58/2.01  tff(f_53, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.58/2.01  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.58/2.01  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.58/2.01  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.58/2.01  tff(f_178, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.58/2.01  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 5.58/2.01  tff(f_72, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.58/2.01  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 5.58/2.01  tff(f_171, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_tsep_1)).
% 5.58/2.01  tff(f_147, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_tmap_1)).
% 5.58/2.01  tff(f_115, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_tmap_1)).
% 5.58/2.01  tff(f_260, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_tmap_1)).
% 5.58/2.01  tff(f_218, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_tmap_1)).
% 5.58/2.01  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_46, plain, (m1_pre_topc('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_40, plain, ('#skF_7'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_88, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 5.58/2.01  tff(c_42, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_76, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_60, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_84, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_7') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_86, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_84])).
% 5.58/2.01  tff(c_135, plain, (r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitLeft, [status(thm)], [c_86])).
% 5.58/2.01  tff(c_78, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_87, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8') | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_78])).
% 5.58/2.01  tff(c_173, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_135, c_87])).
% 5.58/2.01  tff(c_74, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_72, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_58, plain, (m1_pre_topc('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_136, plain, (![B_349, A_350]: (v2_pre_topc(B_349) | ~m1_pre_topc(B_349, A_350) | ~l1_pre_topc(A_350) | ~v2_pre_topc(A_350))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.58/2.01  tff(c_142, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_136])).
% 5.58/2.01  tff(c_151, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_142])).
% 5.58/2.01  tff(c_94, plain, (![B_336, A_337]: (l1_pre_topc(B_336) | ~m1_pre_topc(B_336, A_337) | ~l1_pre_topc(A_337))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.58/2.01  tff(c_100, plain, (l1_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_94])).
% 5.58/2.01  tff(c_109, plain, (l1_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_100])).
% 5.58/2.01  tff(c_56, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_54, plain, (v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_52, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_62, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_97, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_62, c_94])).
% 5.58/2.01  tff(c_106, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_97])).
% 5.58/2.01  tff(c_14, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 5.58/2.01  tff(c_8, plain, (![A_6, B_7]: (r2_hidden(A_6, B_7) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.01  tff(c_168, plain, (![B_357, A_358]: (m1_subset_1(u1_struct_0(B_357), k1_zfmisc_1(u1_struct_0(A_358))) | ~m1_pre_topc(B_357, A_358) | ~l1_pre_topc(A_358))), inference(cnfTransformation, [status(thm)], [f_178])).
% 5.58/2.01  tff(c_10, plain, (![A_8, C_10, B_9]: (m1_subset_1(A_8, C_10) | ~m1_subset_1(B_9, k1_zfmisc_1(C_10)) | ~r2_hidden(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.58/2.01  tff(c_264, plain, (![A_378, A_379, B_380]: (m1_subset_1(A_378, u1_struct_0(A_379)) | ~r2_hidden(A_378, u1_struct_0(B_380)) | ~m1_pre_topc(B_380, A_379) | ~l1_pre_topc(A_379))), inference(resolution, [status(thm)], [c_168, c_10])).
% 5.58/2.01  tff(c_281, plain, (![A_385, A_386, B_387]: (m1_subset_1(A_385, u1_struct_0(A_386)) | ~m1_pre_topc(B_387, A_386) | ~l1_pre_topc(A_386) | v1_xboole_0(u1_struct_0(B_387)) | ~m1_subset_1(A_385, u1_struct_0(B_387)))), inference(resolution, [status(thm)], [c_8, c_264])).
% 5.58/2.01  tff(c_285, plain, (![A_385]: (m1_subset_1(A_385, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_385, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_62, c_281])).
% 5.58/2.01  tff(c_293, plain, (![A_385]: (m1_subset_1(A_385, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_385, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_285])).
% 5.58/2.01  tff(c_305, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_293])).
% 5.58/2.01  tff(c_18, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.58/2.01  tff(c_308, plain, (~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_305, c_18])).
% 5.58/2.01  tff(c_311, plain, (~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_64, c_308])).
% 5.58/2.01  tff(c_314, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_311])).
% 5.58/2.01  tff(c_318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_106, c_314])).
% 5.58/2.01  tff(c_320, plain, (~v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_293])).
% 5.58/2.01  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.58/2.01  tff(c_504, plain, (![B_414, B_415, A_416]: (m1_subset_1('#skF_1'(u1_struct_0(B_414), B_415), u1_struct_0(A_416)) | ~m1_pre_topc(B_414, A_416) | ~l1_pre_topc(A_416) | r1_tarski(u1_struct_0(B_414), B_415))), inference(resolution, [status(thm)], [c_6, c_264])).
% 5.58/2.01  tff(c_341, plain, (![A_395]: (m1_subset_1(A_395, u1_struct_0('#skF_3')) | ~m1_subset_1(A_395, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_293])).
% 5.58/2.01  tff(c_122, plain, (![A_344, B_345]: (r2_hidden(A_344, B_345) | v1_xboole_0(B_345) | ~m1_subset_1(A_344, B_345))), inference(cnfTransformation, [status(thm)], [f_38])).
% 5.58/2.01  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.58/2.01  tff(c_127, plain, (![A_1, B_345]: (r1_tarski(A_1, B_345) | v1_xboole_0(B_345) | ~m1_subset_1('#skF_1'(A_1, B_345), B_345))), inference(resolution, [status(thm)], [c_122, c_4])).
% 5.58/2.01  tff(c_351, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0('#skF_3')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_341, c_127])).
% 5.58/2.01  tff(c_419, plain, (v1_xboole_0(u1_struct_0('#skF_3'))), inference(splitLeft, [status(thm)], [c_351])).
% 5.58/2.01  tff(c_422, plain, (~l1_struct_0('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_419, c_18])).
% 5.58/2.01  tff(c_425, plain, (~l1_struct_0('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_70, c_422])).
% 5.58/2.01  tff(c_428, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_14, c_425])).
% 5.58/2.01  tff(c_432, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_66, c_428])).
% 5.58/2.01  tff(c_433, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0('#skF_3')), u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_351])).
% 5.58/2.01  tff(c_518, plain, (![B_414]: (~m1_pre_topc(B_414, '#skF_4') | ~l1_pre_topc('#skF_4') | r1_tarski(u1_struct_0(B_414), u1_struct_0('#skF_3')))), inference(resolution, [status(thm)], [c_504, c_433])).
% 5.58/2.01  tff(c_571, plain, (![B_420]: (~m1_pre_topc(B_420, '#skF_4') | r1_tarski(u1_struct_0(B_420), u1_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_518])).
% 5.58/2.01  tff(c_128, plain, (![C_346, B_347, A_348]: (r2_hidden(C_346, B_347) | ~r2_hidden(C_346, A_348) | ~r1_tarski(A_348, B_347))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.58/2.01  tff(c_133, plain, (![A_6, B_347, B_7]: (r2_hidden(A_6, B_347) | ~r1_tarski(B_7, B_347) | v1_xboole_0(B_7) | ~m1_subset_1(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_128])).
% 5.58/2.01  tff(c_631, plain, (![A_426, B_427]: (r2_hidden(A_426, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0(B_427)) | ~m1_subset_1(A_426, u1_struct_0(B_427)) | ~m1_pre_topc(B_427, '#skF_4'))), inference(resolution, [status(thm)], [c_571, c_133])).
% 5.58/2.01  tff(c_649, plain, (r2_hidden('#skF_8', u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_631])).
% 5.58/2.01  tff(c_667, plain, (r2_hidden('#skF_8', u1_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_320, c_649])).
% 5.58/2.01  tff(c_678, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_667])).
% 5.58/2.01  tff(c_50, plain, (v1_tsep_1('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_325])).
% 5.58/2.01  tff(c_115, plain, (![A_341, B_342]: (r2_hidden('#skF_1'(A_341, B_342), A_341) | r1_tarski(A_341, B_342))), inference(cnfTransformation, [status(thm)], [f_32])).
% 5.58/2.01  tff(c_120, plain, (![A_341]: (r1_tarski(A_341, A_341))), inference(resolution, [status(thm)], [c_115, c_4])).
% 5.58/2.01  tff(c_336, plain, (![B_392, C_393, A_394]: (m1_pre_topc(B_392, C_393) | ~r1_tarski(u1_struct_0(B_392), u1_struct_0(C_393)) | ~m1_pre_topc(C_393, A_394) | v2_struct_0(C_393) | ~m1_pre_topc(B_392, A_394) | ~v1_tsep_1(B_392, A_394) | ~l1_pre_topc(A_394) | ~v2_pre_topc(A_394) | v2_struct_0(A_394))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.58/2.01  tff(c_1172, plain, (![B_471, A_472]: (m1_pre_topc(B_471, B_471) | v2_struct_0(B_471) | ~m1_pre_topc(B_471, A_472) | ~v1_tsep_1(B_471, A_472) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(resolution, [status(thm)], [c_120, c_336])).
% 5.58/2.01  tff(c_1174, plain, (m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_50, c_1172])).
% 5.58/2.01  tff(c_1177, plain, (m1_pre_topc('#skF_4', '#skF_4') | v2_struct_0('#skF_4') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_62, c_1174])).
% 5.58/2.01  tff(c_1179, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_64, c_678, c_1177])).
% 5.58/2.01  tff(c_1181, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_667])).
% 5.58/2.01  tff(c_287, plain, (![A_385]: (m1_subset_1(A_385, u1_struct_0('#skF_3')) | ~l1_pre_topc('#skF_3') | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_385, u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_58, c_281])).
% 5.58/2.01  tff(c_296, plain, (![A_385]: (m1_subset_1(A_385, u1_struct_0('#skF_3')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1(A_385, u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_287])).
% 5.58/2.01  tff(c_352, plain, (v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitLeft, [status(thm)], [c_296])).
% 5.58/2.01  tff(c_355, plain, (~l1_struct_0('#skF_5') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_352, c_18])).
% 5.58/2.01  tff(c_358, plain, (~l1_struct_0('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_60, c_355])).
% 5.58/2.01  tff(c_361, plain, (~l1_pre_topc('#skF_5')), inference(resolution, [status(thm)], [c_14, c_358])).
% 5.58/2.01  tff(c_365, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_361])).
% 5.58/2.01  tff(c_367, plain, (~v1_xboole_0(u1_struct_0('#skF_5'))), inference(splitRight, [status(thm)], [c_296])).
% 5.58/2.01  tff(c_289, plain, (![A_385]: (m1_subset_1(A_385, u1_struct_0('#skF_5')) | ~l1_pre_topc('#skF_5') | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_385, u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_46, c_281])).
% 5.58/2.01  tff(c_299, plain, (![A_385]: (m1_subset_1(A_385, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_4')) | ~m1_subset_1(A_385, u1_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_289])).
% 5.58/2.01  tff(c_321, plain, (v1_xboole_0(u1_struct_0('#skF_4'))), inference(splitLeft, [status(thm)], [c_299])).
% 5.58/2.01  tff(c_322, plain, $false, inference(negUnitSimplification, [status(thm)], [c_320, c_321])).
% 5.58/2.01  tff(c_325, plain, (![A_391]: (m1_subset_1(A_391, u1_struct_0('#skF_5')) | ~m1_subset_1(A_391, u1_struct_0('#skF_4')))), inference(splitRight, [status(thm)], [c_299])).
% 5.58/2.01  tff(c_335, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_5')) | v1_xboole_0(u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0('#skF_5')), u1_struct_0('#skF_4')))), inference(resolution, [status(thm)], [c_325, c_127])).
% 5.58/2.01  tff(c_436, plain, (![A_1]: (r1_tarski(A_1, u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_1'(A_1, u1_struct_0('#skF_5')), u1_struct_0('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_367, c_335])).
% 5.58/2.01  tff(c_514, plain, (![B_414]: (~m1_pre_topc(B_414, '#skF_4') | ~l1_pre_topc('#skF_4') | r1_tarski(u1_struct_0(B_414), u1_struct_0('#skF_5')))), inference(resolution, [status(thm)], [c_504, c_436])).
% 5.58/2.01  tff(c_546, plain, (![B_417]: (~m1_pre_topc(B_417, '#skF_4') | r1_tarski(u1_struct_0(B_417), u1_struct_0('#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_106, c_514])).
% 5.58/2.01  tff(c_28, plain, (![B_76, C_78, A_72]: (v1_tsep_1(B_76, C_78) | ~r1_tarski(u1_struct_0(B_76), u1_struct_0(C_78)) | ~m1_pre_topc(C_78, A_72) | v2_struct_0(C_78) | ~m1_pre_topc(B_76, A_72) | ~v1_tsep_1(B_76, A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72))), inference(cnfTransformation, [status(thm)], [f_171])).
% 5.58/2.01  tff(c_550, plain, (![B_417, A_72]: (v1_tsep_1(B_417, '#skF_5') | ~m1_pre_topc('#skF_5', A_72) | v2_struct_0('#skF_5') | ~m1_pre_topc(B_417, A_72) | ~v1_tsep_1(B_417, A_72) | ~l1_pre_topc(A_72) | ~v2_pre_topc(A_72) | v2_struct_0(A_72) | ~m1_pre_topc(B_417, '#skF_4'))), inference(resolution, [status(thm)], [c_546, c_28])).
% 5.58/2.01  tff(c_1414, plain, (![B_487, A_488]: (v1_tsep_1(B_487, '#skF_5') | ~m1_pre_topc('#skF_5', A_488) | ~m1_pre_topc(B_487, A_488) | ~v1_tsep_1(B_487, A_488) | ~l1_pre_topc(A_488) | ~v2_pre_topc(A_488) | v2_struct_0(A_488) | ~m1_pre_topc(B_487, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_60, c_550])).
% 5.58/2.01  tff(c_1416, plain, (v1_tsep_1('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_1414])).
% 5.58/2.01  tff(c_1419, plain, (v1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1181, c_68, c_66, c_62, c_58, c_1416])).
% 5.58/2.01  tff(c_1420, plain, (v1_tsep_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_70, c_1419])).
% 5.58/2.01  tff(c_488, plain, (![E_409, B_410, A_408, C_411, D_412]: (k3_tmap_1(A_408, B_410, C_411, D_412, E_409)=k2_partfun1(u1_struct_0(C_411), u1_struct_0(B_410), E_409, u1_struct_0(D_412)) | ~m1_pre_topc(D_412, C_411) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_411), u1_struct_0(B_410)))) | ~v1_funct_2(E_409, u1_struct_0(C_411), u1_struct_0(B_410)) | ~v1_funct_1(E_409) | ~m1_pre_topc(D_412, A_408) | ~m1_pre_topc(C_411, A_408) | ~l1_pre_topc(B_410) | ~v2_pre_topc(B_410) | v2_struct_0(B_410) | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.58/2.01  tff(c_490, plain, (![A_408, D_412]: (k3_tmap_1(A_408, '#skF_2', '#skF_5', D_412, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_412)) | ~m1_pre_topc(D_412, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_412, A_408) | ~m1_pre_topc('#skF_5', A_408) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(resolution, [status(thm)], [c_52, c_488])).
% 5.58/2.01  tff(c_493, plain, (![A_408, D_412]: (k3_tmap_1(A_408, '#skF_2', '#skF_5', D_412, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_412)) | ~m1_pre_topc(D_412, '#skF_5') | ~m1_pre_topc(D_412, A_408) | ~m1_pre_topc('#skF_5', A_408) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_408) | ~v2_pre_topc(A_408) | v2_struct_0(A_408))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_56, c_54, c_490])).
% 5.58/2.01  tff(c_1632, plain, (![A_506, D_507]: (k3_tmap_1(A_506, '#skF_2', '#skF_5', D_507, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_507)) | ~m1_pre_topc(D_507, '#skF_5') | ~m1_pre_topc(D_507, A_506) | ~m1_pre_topc('#skF_5', A_506) | ~l1_pre_topc(A_506) | ~v2_pre_topc(A_506) | v2_struct_0(A_506))), inference(negUnitSimplification, [status(thm)], [c_76, c_493])).
% 5.58/2.01  tff(c_1638, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_1632])).
% 5.58/2.01  tff(c_1650, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_58, c_46, c_1638])).
% 5.58/2.01  tff(c_1651, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_1650])).
% 5.58/2.01  tff(c_400, plain, (![A_397, B_398, C_399, D_400]: (k2_partfun1(u1_struct_0(A_397), u1_struct_0(B_398), C_399, u1_struct_0(D_400))=k2_tmap_1(A_397, B_398, C_399, D_400) | ~m1_pre_topc(D_400, A_397) | ~m1_subset_1(C_399, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_397), u1_struct_0(B_398)))) | ~v1_funct_2(C_399, u1_struct_0(A_397), u1_struct_0(B_398)) | ~v1_funct_1(C_399) | ~l1_pre_topc(B_398) | ~v2_pre_topc(B_398) | v2_struct_0(B_398) | ~l1_pre_topc(A_397) | ~v2_pre_topc(A_397) | v2_struct_0(A_397))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.58/2.01  tff(c_402, plain, (![D_400]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_400))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_400) | ~m1_pre_topc(D_400, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_400])).
% 5.58/2.01  tff(c_405, plain, (![D_400]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_400))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_400) | ~m1_pre_topc(D_400, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_151, c_109, c_74, c_72, c_56, c_54, c_402])).
% 5.58/2.01  tff(c_406, plain, (![D_400]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_400))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_400) | ~m1_pre_topc(D_400, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_76, c_405])).
% 5.58/2.01  tff(c_1663, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_1651, c_406])).
% 5.58/2.01  tff(c_1670, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_1663])).
% 5.58/2.01  tff(c_1675, plain, (r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1670, c_135])).
% 5.58/2.01  tff(c_34, plain, (![B_177, C_193, A_145, D_201, F_207]: (r1_tmap_1(B_177, A_145, C_193, F_207) | ~r1_tmap_1(D_201, A_145, k2_tmap_1(B_177, A_145, C_193, D_201), F_207) | ~m1_subset_1(F_207, u1_struct_0(D_201)) | ~m1_subset_1(F_207, u1_struct_0(B_177)) | ~m1_pre_topc(D_201, B_177) | ~v1_tsep_1(D_201, B_177) | v2_struct_0(D_201) | ~m1_subset_1(C_193, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_177), u1_struct_0(A_145)))) | ~v1_funct_2(C_193, u1_struct_0(B_177), u1_struct_0(A_145)) | ~v1_funct_1(C_193) | ~l1_pre_topc(B_177) | ~v2_pre_topc(B_177) | v2_struct_0(B_177) | ~l1_pre_topc(A_145) | ~v2_pre_topc(A_145) | v2_struct_0(A_145))), inference(cnfTransformation, [status(thm)], [f_260])).
% 5.58/2.01  tff(c_1681, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | ~v1_tsep_1('#skF_4', '#skF_5') | v2_struct_0('#skF_4') | ~m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_1675, c_34])).
% 5.58/2.01  tff(c_1684, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | v2_struct_0('#skF_4') | v2_struct_0('#skF_5') | v2_struct_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_151, c_109, c_56, c_54, c_52, c_1420, c_46, c_88, c_42, c_1681])).
% 5.58/2.01  tff(c_1686, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_60, c_64, c_173, c_1684])).
% 5.58/2.01  tff(c_1687, plain, (r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitRight, [status(thm)], [c_86])).
% 5.58/2.01  tff(c_1695, plain, (![B_508, A_509]: (v2_pre_topc(B_508) | ~m1_pre_topc(B_508, A_509) | ~l1_pre_topc(A_509) | ~v2_pre_topc(A_509))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.58/2.01  tff(c_1701, plain, (v2_pre_topc('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_58, c_1695])).
% 5.58/2.01  tff(c_1710, plain, (v2_pre_topc('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_1701])).
% 5.58/2.01  tff(c_2322, plain, (![B_590, D_592, F_591, A_594, C_593]: (r1_tmap_1(D_592, A_594, k2_tmap_1(B_590, A_594, C_593, D_592), F_591) | ~r1_tmap_1(B_590, A_594, C_593, F_591) | ~m1_subset_1(F_591, u1_struct_0(D_592)) | ~m1_subset_1(F_591, u1_struct_0(B_590)) | ~m1_pre_topc(D_592, B_590) | v2_struct_0(D_592) | ~m1_subset_1(C_593, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_590), u1_struct_0(A_594)))) | ~v1_funct_2(C_593, u1_struct_0(B_590), u1_struct_0(A_594)) | ~v1_funct_1(C_593) | ~l1_pre_topc(B_590) | ~v2_pre_topc(B_590) | v2_struct_0(B_590) | ~l1_pre_topc(A_594) | ~v2_pre_topc(A_594) | v2_struct_0(A_594))), inference(cnfTransformation, [status(thm)], [f_218])).
% 5.58/2.01  tff(c_2324, plain, (![D_592, F_591]: (r1_tmap_1(D_592, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_592), F_591) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_591) | ~m1_subset_1(F_591, u1_struct_0(D_592)) | ~m1_subset_1(F_591, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_592, '#skF_5') | v2_struct_0(D_592) | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2'))), inference(resolution, [status(thm)], [c_52, c_2322])).
% 5.58/2.01  tff(c_2327, plain, (![D_592, F_591]: (r1_tmap_1(D_592, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_592), F_591) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_591) | ~m1_subset_1(F_591, u1_struct_0(D_592)) | ~m1_subset_1(F_591, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_592, '#skF_5') | v2_struct_0(D_592) | v2_struct_0('#skF_5') | v2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_1710, c_109, c_56, c_54, c_2324])).
% 5.58/2.01  tff(c_2328, plain, (![D_592, F_591]: (r1_tmap_1(D_592, '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_592), F_591) | ~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', F_591) | ~m1_subset_1(F_591, u1_struct_0(D_592)) | ~m1_subset_1(F_591, u1_struct_0('#skF_5')) | ~m1_pre_topc(D_592, '#skF_5') | v2_struct_0(D_592))), inference(negUnitSimplification, [status(thm)], [c_76, c_60, c_2327])).
% 5.58/2.01  tff(c_2153, plain, (![A_577, B_579, C_580, D_581, E_578]: (k3_tmap_1(A_577, B_579, C_580, D_581, E_578)=k2_partfun1(u1_struct_0(C_580), u1_struct_0(B_579), E_578, u1_struct_0(D_581)) | ~m1_pre_topc(D_581, C_580) | ~m1_subset_1(E_578, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_580), u1_struct_0(B_579)))) | ~v1_funct_2(E_578, u1_struct_0(C_580), u1_struct_0(B_579)) | ~v1_funct_1(E_578) | ~m1_pre_topc(D_581, A_577) | ~m1_pre_topc(C_580, A_577) | ~l1_pre_topc(B_579) | ~v2_pre_topc(B_579) | v2_struct_0(B_579) | ~l1_pre_topc(A_577) | ~v2_pre_topc(A_577) | v2_struct_0(A_577))), inference(cnfTransformation, [status(thm)], [f_147])).
% 5.58/2.01  tff(c_2155, plain, (![A_577, D_581]: (k3_tmap_1(A_577, '#skF_2', '#skF_5', D_581, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_581)) | ~m1_pre_topc(D_581, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~m1_pre_topc(D_581, A_577) | ~m1_pre_topc('#skF_5', A_577) | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc(A_577) | ~v2_pre_topc(A_577) | v2_struct_0(A_577))), inference(resolution, [status(thm)], [c_52, c_2153])).
% 5.58/2.01  tff(c_2158, plain, (![A_577, D_581]: (k3_tmap_1(A_577, '#skF_2', '#skF_5', D_581, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_581)) | ~m1_pre_topc(D_581, '#skF_5') | ~m1_pre_topc(D_581, A_577) | ~m1_pre_topc('#skF_5', A_577) | v2_struct_0('#skF_2') | ~l1_pre_topc(A_577) | ~v2_pre_topc(A_577) | v2_struct_0(A_577))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_56, c_54, c_2155])).
% 5.58/2.01  tff(c_2698, plain, (![A_635, D_636]: (k3_tmap_1(A_635, '#skF_2', '#skF_5', D_636, '#skF_6')=k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_636)) | ~m1_pre_topc(D_636, '#skF_5') | ~m1_pre_topc(D_636, A_635) | ~m1_pre_topc('#skF_5', A_635) | ~l1_pre_topc(A_635) | ~v2_pre_topc(A_635) | v2_struct_0(A_635))), inference(negUnitSimplification, [status(thm)], [c_76, c_2158])).
% 5.58/2.01  tff(c_2702, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | ~m1_pre_topc('#skF_4', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_3') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_62, c_2698])).
% 5.58/2.01  tff(c_2710, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_58, c_46, c_2702])).
% 5.58/2.01  tff(c_2711, plain, (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0('#skF_4'))=k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_70, c_2710])).
% 5.58/2.01  tff(c_2010, plain, (![A_561, B_562, C_563, D_564]: (k2_partfun1(u1_struct_0(A_561), u1_struct_0(B_562), C_563, u1_struct_0(D_564))=k2_tmap_1(A_561, B_562, C_563, D_564) | ~m1_pre_topc(D_564, A_561) | ~m1_subset_1(C_563, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_561), u1_struct_0(B_562)))) | ~v1_funct_2(C_563, u1_struct_0(A_561), u1_struct_0(B_562)) | ~v1_funct_1(C_563) | ~l1_pre_topc(B_562) | ~v2_pre_topc(B_562) | v2_struct_0(B_562) | ~l1_pre_topc(A_561) | ~v2_pre_topc(A_561) | v2_struct_0(A_561))), inference(cnfTransformation, [status(thm)], [f_115])).
% 5.58/2.01  tff(c_2012, plain, (![D_564]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_564))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_564) | ~m1_pre_topc(D_564, '#skF_5') | ~v1_funct_2('#skF_6', u1_struct_0('#skF_5'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_6') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_5') | ~v2_pre_topc('#skF_5') | v2_struct_0('#skF_5'))), inference(resolution, [status(thm)], [c_52, c_2010])).
% 5.58/2.01  tff(c_2015, plain, (![D_564]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_564))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_564) | ~m1_pre_topc(D_564, '#skF_5') | v2_struct_0('#skF_2') | v2_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1710, c_109, c_74, c_72, c_56, c_54, c_2012])).
% 5.58/2.01  tff(c_2016, plain, (![D_564]: (k2_partfun1(u1_struct_0('#skF_5'), u1_struct_0('#skF_2'), '#skF_6', u1_struct_0(D_564))=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', D_564) | ~m1_pre_topc(D_564, '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_60, c_76, c_2015])).
% 5.58/2.01  tff(c_2723, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4') | ~m1_pre_topc('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2711, c_2016])).
% 5.58/2.01  tff(c_2730, plain, (k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6')=k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2723])).
% 5.58/2.01  tff(c_1689, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8')), inference(splitLeft, [status(thm)], [c_87])).
% 5.58/2.01  tff(c_1691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1687, c_1689])).
% 5.58/2.01  tff(c_1692, plain, (~r1_tmap_1('#skF_4', '#skF_2', k3_tmap_1('#skF_3', '#skF_2', '#skF_5', '#skF_4', '#skF_6'), '#skF_8')), inference(splitRight, [status(thm)], [c_87])).
% 5.58/2.01  tff(c_2735, plain, (~r1_tmap_1('#skF_4', '#skF_2', k2_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_4'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_2730, c_1692])).
% 5.58/2.01  tff(c_2742, plain, (~r1_tmap_1('#skF_5', '#skF_2', '#skF_6', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_4')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_pre_topc('#skF_4', '#skF_5') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_2328, c_2735])).
% 5.58/2.01  tff(c_2745, plain, (v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_88, c_42, c_1687, c_2742])).
% 5.58/2.01  tff(c_2747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_2745])).
% 5.58/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.58/2.01  
% 5.58/2.01  Inference rules
% 5.58/2.01  ----------------------
% 5.58/2.01  #Ref     : 0
% 5.58/2.01  #Sup     : 530
% 5.58/2.01  #Fact    : 0
% 5.58/2.01  #Define  : 0
% 5.58/2.01  #Split   : 23
% 5.58/2.01  #Chain   : 0
% 5.58/2.01  #Close   : 0
% 5.58/2.01  
% 5.58/2.01  Ordering : KBO
% 5.58/2.01  
% 5.58/2.01  Simplification rules
% 5.58/2.01  ----------------------
% 5.58/2.01  #Subsume      : 154
% 5.58/2.01  #Demod        : 423
% 5.58/2.01  #Tautology    : 120
% 5.58/2.01  #SimpNegUnit  : 152
% 5.58/2.01  #BackRed      : 6
% 5.58/2.01  
% 5.58/2.01  #Partial instantiations: 0
% 5.58/2.01  #Strategies tried      : 1
% 5.58/2.01  
% 5.58/2.01  Timing (in seconds)
% 5.58/2.01  ----------------------
% 5.58/2.01  Preprocessing        : 0.41
% 5.58/2.01  Parsing              : 0.20
% 5.58/2.01  CNF conversion       : 0.05
% 5.58/2.01  Main loop            : 0.77
% 5.58/2.01  Inferencing          : 0.25
% 5.58/2.01  Reduction            : 0.26
% 5.58/2.01  Demodulation         : 0.18
% 5.58/2.01  BG Simplification    : 0.03
% 5.58/2.01  Subsumption          : 0.17
% 5.58/2.01  Abstraction          : 0.03
% 5.58/2.01  MUC search           : 0.00
% 5.58/2.01  Cooper               : 0.00
% 5.58/2.01  Total                : 1.24
% 5.58/2.01  Index Insertion      : 0.00
% 5.58/2.01  Index Deletion       : 0.00
% 5.58/2.01  Index Matching       : 0.00
% 5.58/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
