%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:29 EST 2020

% Result     : Theorem 4.13s
% Output     : CNFRefutation 4.39s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 350 expanded)
%              Number of leaves         :   42 ( 154 expanded)
%              Depth                    :   15
%              Number of atoms          :  456 (2810 expanded)
%              Number of equality atoms :   33 ( 144 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(f_310,negated_conjecture,(
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

tff(f_57,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_163,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_156,axiom,(
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

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_132,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tmap_1)).

tff(f_100,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tmap_1)).

tff(f_245,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tmap_1)).

tff(f_203,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_tmap_1)).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_48,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_46,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_42,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_44,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_90,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_52,plain,(
    v1_tsep_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_64,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_68,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_60,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_97,plain,(
    ! [B_334,A_335] :
      ( l1_pre_topc(B_334)
      | ~ m1_pre_topc(B_334,A_335)
      | ~ l1_pre_topc(A_335) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_106,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_97])).

tff(c_113,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_106])).

tff(c_70,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_156,plain,(
    ! [B_344,A_345] :
      ( m1_subset_1(u1_struct_0(B_344),k1_zfmisc_1(u1_struct_0(A_345)))
      | ~ m1_pre_topc(B_344,A_345)
      | ~ l1_pre_topc(A_345) ) ),
    inference(cnfTransformation,[status(thm)],[f_163])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_121,plain,(
    ! [A_338,B_339] :
      ( r2_hidden(A_338,B_339)
      | v1_xboole_0(B_339)
      | ~ m1_subset_1(A_338,B_339) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_125,plain,(
    ! [A_338,A_1] :
      ( r1_tarski(A_338,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_338,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_121,c_2])).

tff(c_128,plain,(
    ! [A_338,A_1] :
      ( r1_tarski(A_338,A_1)
      | ~ m1_subset_1(A_338,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_125])).

tff(c_160,plain,(
    ! [B_344,A_345] :
      ( r1_tarski(u1_struct_0(B_344),u1_struct_0(A_345))
      | ~ m1_pre_topc(B_344,A_345)
      | ~ l1_pre_topc(A_345) ) ),
    inference(resolution,[status(thm)],[c_156,c_128])).

tff(c_451,plain,(
    ! [B_389,C_390,A_391] :
      ( v1_tsep_1(B_389,C_390)
      | ~ r1_tarski(u1_struct_0(B_389),u1_struct_0(C_390))
      | ~ m1_pre_topc(C_390,A_391)
      | v2_struct_0(C_390)
      | ~ m1_pre_topc(B_389,A_391)
      | ~ v1_tsep_1(B_389,A_391)
      | ~ l1_pre_topc(A_391)
      | ~ v2_pre_topc(A_391)
      | v2_struct_0(A_391) ) ),
    inference(cnfTransformation,[status(thm)],[f_156])).

tff(c_546,plain,(
    ! [B_403,A_404,A_405] :
      ( v1_tsep_1(B_403,A_404)
      | ~ m1_pre_topc(A_404,A_405)
      | v2_struct_0(A_404)
      | ~ m1_pre_topc(B_403,A_405)
      | ~ v1_tsep_1(B_403,A_405)
      | ~ l1_pre_topc(A_405)
      | ~ v2_pre_topc(A_405)
      | v2_struct_0(A_405)
      | ~ m1_pre_topc(B_403,A_404)
      | ~ l1_pre_topc(A_404) ) ),
    inference(resolution,[status(thm)],[c_160,c_451])).

tff(c_558,plain,(
    ! [B_403] :
      ( v1_tsep_1(B_403,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_403,'#skF_4')
      | ~ v1_tsep_1(B_403,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_403,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_60,c_546])).

tff(c_581,plain,(
    ! [B_403] :
      ( v1_tsep_1(B_403,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_403,'#skF_4')
      | ~ v1_tsep_1(B_403,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_403,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_70,c_68,c_558])).

tff(c_582,plain,(
    ! [B_403] :
      ( v1_tsep_1(B_403,'#skF_6')
      | ~ m1_pre_topc(B_403,'#skF_4')
      | ~ v1_tsep_1(B_403,'#skF_4')
      | ~ m1_pre_topc(B_403,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_62,c_581])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_80,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_89,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_80])).

tff(c_153,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_76,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_74,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_134,plain,(
    ! [B_342,A_343] :
      ( v2_pre_topc(B_342)
      | ~ m1_pre_topc(B_342,A_343)
      | ~ l1_pre_topc(A_343)
      | ~ v2_pre_topc(A_343) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_143,plain,
    ( v2_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_134])).

tff(c_152,plain,(
    v2_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_143])).

tff(c_58,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_56,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_586,plain,(
    ! [C_410,E_409,D_413,A_411,B_412] :
      ( k3_tmap_1(A_411,B_412,C_410,D_413,E_409) = k2_partfun1(u1_struct_0(C_410),u1_struct_0(B_412),E_409,u1_struct_0(D_413))
      | ~ m1_pre_topc(D_413,C_410)
      | ~ m1_subset_1(E_409,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_410),u1_struct_0(B_412))))
      | ~ v1_funct_2(E_409,u1_struct_0(C_410),u1_struct_0(B_412))
      | ~ v1_funct_1(E_409)
      | ~ m1_pre_topc(D_413,A_411)
      | ~ m1_pre_topc(C_410,A_411)
      | ~ l1_pre_topc(B_412)
      | ~ v2_pre_topc(B_412)
      | v2_struct_0(B_412)
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_588,plain,(
    ! [A_411,D_413] :
      ( k3_tmap_1(A_411,'#skF_3','#skF_6',D_413,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_413))
      | ~ m1_pre_topc(D_413,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_413,A_411)
      | ~ m1_pre_topc('#skF_6',A_411)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(resolution,[status(thm)],[c_54,c_586])).

tff(c_591,plain,(
    ! [A_411,D_413] :
      ( k3_tmap_1(A_411,'#skF_3','#skF_6',D_413,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_413))
      | ~ m1_pre_topc(D_413,'#skF_6')
      | ~ m1_pre_topc(D_413,A_411)
      | ~ m1_pre_topc('#skF_6',A_411)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_411)
      | ~ v2_pre_topc(A_411)
      | v2_struct_0(A_411) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_56,c_588])).

tff(c_688,plain,(
    ! [A_420,D_421] :
      ( k3_tmap_1(A_420,'#skF_3','#skF_6',D_421,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_421))
      | ~ m1_pre_topc(D_421,'#skF_6')
      | ~ m1_pre_topc(D_421,A_420)
      | ~ m1_pre_topc('#skF_6',A_420)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420)
      | v2_struct_0(A_420) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_591])).

tff(c_696,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_688])).

tff(c_710,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_48,c_696])).

tff(c_711,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_710])).

tff(c_530,plain,(
    ! [A_398,B_399,C_400,D_401] :
      ( k2_partfun1(u1_struct_0(A_398),u1_struct_0(B_399),C_400,u1_struct_0(D_401)) = k2_tmap_1(A_398,B_399,C_400,D_401)
      | ~ m1_pre_topc(D_401,A_398)
      | ~ m1_subset_1(C_400,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_398),u1_struct_0(B_399))))
      | ~ v1_funct_2(C_400,u1_struct_0(A_398),u1_struct_0(B_399))
      | ~ v1_funct_1(C_400)
      | ~ l1_pre_topc(B_399)
      | ~ v2_pre_topc(B_399)
      | v2_struct_0(B_399)
      | ~ l1_pre_topc(A_398)
      | ~ v2_pre_topc(A_398)
      | v2_struct_0(A_398) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_532,plain,(
    ! [D_401] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_401)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_401)
      | ~ m1_pre_topc(D_401,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_530])).

tff(c_535,plain,(
    ! [D_401] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_401)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_401)
      | ~ m1_pre_topc(D_401,'#skF_6')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_113,c_76,c_74,c_58,c_56,c_532])).

tff(c_536,plain,(
    ! [D_401] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_401)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_401)
      | ~ m1_pre_topc(D_401,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_78,c_535])).

tff(c_730,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_536])).

tff(c_737,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_730])).

tff(c_86,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_310])).

tff(c_88,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_86])).

tff(c_178,plain,(
    r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_88])).

tff(c_742,plain,(
    r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_178])).

tff(c_771,plain,(
    ! [F_427,B_428,C_429,A_431,D_430] :
      ( r1_tmap_1(B_428,A_431,C_429,F_427)
      | ~ r1_tmap_1(D_430,A_431,k2_tmap_1(B_428,A_431,C_429,D_430),F_427)
      | ~ m1_subset_1(F_427,u1_struct_0(D_430))
      | ~ m1_subset_1(F_427,u1_struct_0(B_428))
      | ~ m1_pre_topc(D_430,B_428)
      | ~ v1_tsep_1(D_430,B_428)
      | v2_struct_0(D_430)
      | ~ m1_subset_1(C_429,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_428),u1_struct_0(A_431))))
      | ~ v1_funct_2(C_429,u1_struct_0(B_428),u1_struct_0(A_431))
      | ~ v1_funct_1(C_429)
      | ~ l1_pre_topc(B_428)
      | ~ v2_pre_topc(B_428)
      | v2_struct_0(B_428)
      | ~ l1_pre_topc(A_431)
      | ~ v2_pre_topc(A_431)
      | v2_struct_0(A_431) ) ),
    inference(cnfTransformation,[status(thm)],[f_245])).

tff(c_773,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ v1_tsep_1('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | ~ m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))))
    | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
    | ~ v1_funct_1('#skF_7')
    | ~ l1_pre_topc('#skF_6')
    | ~ v2_pre_topc('#skF_6')
    | v2_struct_0('#skF_6')
    | ~ l1_pre_topc('#skF_3')
    | ~ v2_pre_topc('#skF_3')
    | v2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_742,c_771])).

tff(c_776,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ v1_tsep_1('#skF_5','#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_152,c_113,c_58,c_56,c_54,c_48,c_46,c_90,c_773])).

tff(c_777,plain,(
    ~ v1_tsep_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_62,c_66,c_153,c_776])).

tff(c_780,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_582,c_777])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_52,c_64,c_780])).

tff(c_786,plain,(
    r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1398,plain,(
    ! [F_513,C_514,A_511,D_510,B_512] :
      ( r1_tmap_1(D_510,A_511,k2_tmap_1(B_512,A_511,C_514,D_510),F_513)
      | ~ r1_tmap_1(B_512,A_511,C_514,F_513)
      | ~ m1_subset_1(F_513,u1_struct_0(D_510))
      | ~ m1_subset_1(F_513,u1_struct_0(B_512))
      | ~ m1_pre_topc(D_510,B_512)
      | v2_struct_0(D_510)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_512),u1_struct_0(A_511))))
      | ~ v1_funct_2(C_514,u1_struct_0(B_512),u1_struct_0(A_511))
      | ~ v1_funct_1(C_514)
      | ~ l1_pre_topc(B_512)
      | ~ v2_pre_topc(B_512)
      | v2_struct_0(B_512)
      | ~ l1_pre_topc(A_511)
      | ~ v2_pre_topc(A_511)
      | v2_struct_0(A_511) ) ),
    inference(cnfTransformation,[status(thm)],[f_203])).

tff(c_1400,plain,(
    ! [D_510,F_513] :
      ( r1_tmap_1(D_510,'#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7',D_510),F_513)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',F_513)
      | ~ m1_subset_1(F_513,u1_struct_0(D_510))
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_510,'#skF_6')
      | v2_struct_0(D_510)
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_54,c_1398])).

tff(c_1403,plain,(
    ! [D_510,F_513] :
      ( r1_tmap_1(D_510,'#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7',D_510),F_513)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',F_513)
      | ~ m1_subset_1(F_513,u1_struct_0(D_510))
      | ~ m1_subset_1(F_513,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_510,'#skF_6')
      | v2_struct_0(D_510)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_152,c_113,c_58,c_56,c_1400])).

tff(c_1411,plain,(
    ! [D_515,F_516] :
      ( r1_tmap_1(D_515,'#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7',D_515),F_516)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',F_516)
      | ~ m1_subset_1(F_516,u1_struct_0(D_515))
      | ~ m1_subset_1(F_516,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_515,'#skF_6')
      | v2_struct_0(D_515) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_62,c_1403])).

tff(c_1295,plain,(
    ! [C_502,D_505,B_504,A_503,E_501] :
      ( k3_tmap_1(A_503,B_504,C_502,D_505,E_501) = k2_partfun1(u1_struct_0(C_502),u1_struct_0(B_504),E_501,u1_struct_0(D_505))
      | ~ m1_pre_topc(D_505,C_502)
      | ~ m1_subset_1(E_501,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_502),u1_struct_0(B_504))))
      | ~ v1_funct_2(E_501,u1_struct_0(C_502),u1_struct_0(B_504))
      | ~ v1_funct_1(E_501)
      | ~ m1_pre_topc(D_505,A_503)
      | ~ m1_pre_topc(C_502,A_503)
      | ~ l1_pre_topc(B_504)
      | ~ v2_pre_topc(B_504)
      | v2_struct_0(B_504)
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(cnfTransformation,[status(thm)],[f_132])).

tff(c_1297,plain,(
    ! [A_503,D_505] :
      ( k3_tmap_1(A_503,'#skF_3','#skF_6',D_505,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_505))
      | ~ m1_pre_topc(D_505,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_505,A_503)
      | ~ m1_pre_topc('#skF_6',A_503)
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(resolution,[status(thm)],[c_54,c_1295])).

tff(c_1300,plain,(
    ! [A_503,D_505] :
      ( k3_tmap_1(A_503,'#skF_3','#skF_6',D_505,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_505))
      | ~ m1_pre_topc(D_505,'#skF_6')
      | ~ m1_pre_topc(D_505,A_503)
      | ~ m1_pre_topc('#skF_6',A_503)
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_503)
      | ~ v2_pre_topc(A_503)
      | v2_struct_0(A_503) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_74,c_58,c_56,c_1297])).

tff(c_1327,plain,(
    ! [A_508,D_509] :
      ( k3_tmap_1(A_508,'#skF_3','#skF_6',D_509,'#skF_7') = k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_509))
      | ~ m1_pre_topc(D_509,'#skF_6')
      | ~ m1_pre_topc(D_509,A_508)
      | ~ m1_pre_topc('#skF_6',A_508)
      | ~ l1_pre_topc(A_508)
      | ~ v2_pre_topc(A_508)
      | v2_struct_0(A_508) ) ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_1300])).

tff(c_1335,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | ~ m1_pre_topc('#skF_6','#skF_4')
    | ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_1327])).

tff(c_1349,plain,
    ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_60,c_48,c_1335])).

tff(c_1350,plain,(
    k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0('#skF_5')) = k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1349])).

tff(c_1207,plain,(
    ! [A_490,B_491,C_492,D_493] :
      ( k2_partfun1(u1_struct_0(A_490),u1_struct_0(B_491),C_492,u1_struct_0(D_493)) = k2_tmap_1(A_490,B_491,C_492,D_493)
      | ~ m1_pre_topc(D_493,A_490)
      | ~ m1_subset_1(C_492,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490),u1_struct_0(B_491))))
      | ~ v1_funct_2(C_492,u1_struct_0(A_490),u1_struct_0(B_491))
      | ~ v1_funct_1(C_492)
      | ~ l1_pre_topc(B_491)
      | ~ v2_pre_topc(B_491)
      | v2_struct_0(B_491)
      | ~ l1_pre_topc(A_490)
      | ~ v2_pre_topc(A_490)
      | v2_struct_0(A_490) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_1209,plain,(
    ! [D_493] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_493)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_493)
      | ~ m1_pre_topc(D_493,'#skF_6')
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc('#skF_6')
      | ~ v2_pre_topc('#skF_6')
      | v2_struct_0('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_54,c_1207])).

tff(c_1212,plain,(
    ! [D_493] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_493)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_493)
      | ~ m1_pre_topc(D_493,'#skF_6')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_113,c_76,c_74,c_58,c_56,c_1209])).

tff(c_1213,plain,(
    ! [D_493] :
      ( k2_partfun1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3'),'#skF_7',u1_struct_0(D_493)) = k2_tmap_1('#skF_6','#skF_3','#skF_7',D_493)
      | ~ m1_pre_topc(D_493,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_78,c_1212])).

tff(c_1362,plain,
    ( k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1350,c_1213])).

tff(c_1369,plain,(
    k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7') = k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1362])).

tff(c_785,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_1374,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k2_tmap_1('#skF_6','#skF_3','#skF_7','#skF_5'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1369,c_785])).

tff(c_1414,plain,
    ( ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_5'))
    | ~ m1_subset_1('#skF_8',u1_struct_0('#skF_6'))
    | ~ m1_pre_topc('#skF_5','#skF_6')
    | v2_struct_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1411,c_1374])).

tff(c_1417,plain,(
    v2_struct_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_46,c_90,c_786,c_1414])).

tff(c_1419,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_1417])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:19:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.13/1.70  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.72  
% 4.13/1.72  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.13/1.72  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_tmap_1 > k2_partfun1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 4.13/1.72  
% 4.13/1.72  %Foreground sorts:
% 4.13/1.72  
% 4.13/1.72  
% 4.13/1.72  %Background operators:
% 4.13/1.72  
% 4.13/1.72  
% 4.13/1.72  %Foreground operators:
% 4.13/1.72  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 4.13/1.72  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 4.13/1.72  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.13/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.13/1.72  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 4.13/1.72  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 4.13/1.72  tff('#skF_7', type, '#skF_7': $i).
% 4.13/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.13/1.72  tff('#skF_5', type, '#skF_5': $i).
% 4.13/1.72  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.13/1.72  tff('#skF_6', type, '#skF_6': $i).
% 4.13/1.72  tff('#skF_3', type, '#skF_3': $i).
% 4.13/1.72  tff('#skF_9', type, '#skF_9': $i).
% 4.13/1.72  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.13/1.72  tff('#skF_8', type, '#skF_8': $i).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.13/1.72  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.13/1.72  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 4.13/1.72  tff('#skF_4', type, '#skF_4': $i).
% 4.13/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.13/1.72  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.13/1.72  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 4.13/1.72  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 4.13/1.72  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 4.13/1.72  tff(k2_tmap_1, type, k2_tmap_1: ($i * $i * $i * $i) > $i).
% 4.13/1.72  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 4.13/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.13/1.72  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.13/1.72  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.13/1.72  
% 4.39/1.74  tff(f_310, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 4.39/1.74  tff(f_57, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.39/1.74  tff(f_163, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 4.39/1.74  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.39/1.74  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.39/1.74  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.39/1.74  tff(f_156, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 4.39/1.74  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.39/1.74  tff(f_132, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (m1_pre_topc(C, A) => (![D]: (m1_pre_topc(D, A) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (m1_pre_topc(D, C) => (k3_tmap_1(A, B, C, D, E) = k2_partfun1(u1_struct_0(C), u1_struct_0(B), E, u1_struct_0(D)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_tmap_1)).
% 4.39/1.74  tff(f_100, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(A), u1_struct_0(B))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A), u1_struct_0(B))))) => (![D]: (m1_pre_topc(D, A) => (k2_tmap_1(A, B, C, D) = k2_partfun1(u1_struct_0(A), u1_struct_0(B), C, u1_struct_0(D))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_tmap_1)).
% 4.39/1.74  tff(f_245, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: (((~v2_struct_0(D) & v1_tsep_1(D, B)) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => ((E = F) => (r1_tmap_1(B, A, C, E) <=> r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_tmap_1)).
% 4.39/1.74  tff(f_203, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: (((v1_funct_1(C) & v1_funct_2(C, u1_struct_0(B), u1_struct_0(A))) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B), u1_struct_0(A))))) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (m1_subset_1(E, u1_struct_0(B)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (((E = F) & r1_tmap_1(B, A, C, E)) => r1_tmap_1(D, A, k2_tmap_1(B, A, C, D), F)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_tmap_1)).
% 4.39/1.74  tff(c_66, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_48, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_46, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_42, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_44, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_90, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 4.39/1.74  tff(c_52, plain, (v1_tsep_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_64, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_72, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_62, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_68, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_60, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_97, plain, (![B_334, A_335]: (l1_pre_topc(B_334) | ~m1_pre_topc(B_334, A_335) | ~l1_pre_topc(A_335))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.39/1.74  tff(c_106, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_97])).
% 4.39/1.74  tff(c_113, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_106])).
% 4.39/1.74  tff(c_70, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_156, plain, (![B_344, A_345]: (m1_subset_1(u1_struct_0(B_344), k1_zfmisc_1(u1_struct_0(A_345))) | ~m1_pre_topc(B_344, A_345) | ~l1_pre_topc(A_345))), inference(cnfTransformation, [status(thm)], [f_163])).
% 4.39/1.74  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.39/1.74  tff(c_121, plain, (![A_338, B_339]: (r2_hidden(A_338, B_339) | v1_xboole_0(B_339) | ~m1_subset_1(A_338, B_339))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.39/1.74  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 4.39/1.74  tff(c_125, plain, (![A_338, A_1]: (r1_tarski(A_338, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_338, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_121, c_2])).
% 4.39/1.74  tff(c_128, plain, (![A_338, A_1]: (r1_tarski(A_338, A_1) | ~m1_subset_1(A_338, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_125])).
% 4.39/1.74  tff(c_160, plain, (![B_344, A_345]: (r1_tarski(u1_struct_0(B_344), u1_struct_0(A_345)) | ~m1_pre_topc(B_344, A_345) | ~l1_pre_topc(A_345))), inference(resolution, [status(thm)], [c_156, c_128])).
% 4.39/1.74  tff(c_451, plain, (![B_389, C_390, A_391]: (v1_tsep_1(B_389, C_390) | ~r1_tarski(u1_struct_0(B_389), u1_struct_0(C_390)) | ~m1_pre_topc(C_390, A_391) | v2_struct_0(C_390) | ~m1_pre_topc(B_389, A_391) | ~v1_tsep_1(B_389, A_391) | ~l1_pre_topc(A_391) | ~v2_pre_topc(A_391) | v2_struct_0(A_391))), inference(cnfTransformation, [status(thm)], [f_156])).
% 4.39/1.74  tff(c_546, plain, (![B_403, A_404, A_405]: (v1_tsep_1(B_403, A_404) | ~m1_pre_topc(A_404, A_405) | v2_struct_0(A_404) | ~m1_pre_topc(B_403, A_405) | ~v1_tsep_1(B_403, A_405) | ~l1_pre_topc(A_405) | ~v2_pre_topc(A_405) | v2_struct_0(A_405) | ~m1_pre_topc(B_403, A_404) | ~l1_pre_topc(A_404))), inference(resolution, [status(thm)], [c_160, c_451])).
% 4.39/1.74  tff(c_558, plain, (![B_403]: (v1_tsep_1(B_403, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_403, '#skF_4') | ~v1_tsep_1(B_403, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_403, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_60, c_546])).
% 4.39/1.74  tff(c_581, plain, (![B_403]: (v1_tsep_1(B_403, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_403, '#skF_4') | ~v1_tsep_1(B_403, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_403, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_70, c_68, c_558])).
% 4.39/1.74  tff(c_582, plain, (![B_403]: (v1_tsep_1(B_403, '#skF_6') | ~m1_pre_topc(B_403, '#skF_4') | ~v1_tsep_1(B_403, '#skF_4') | ~m1_pre_topc(B_403, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_72, c_62, c_581])).
% 4.39/1.74  tff(c_78, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_80, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_89, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_80])).
% 4.39/1.74  tff(c_153, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_89])).
% 4.39/1.74  tff(c_76, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_74, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_134, plain, (![B_342, A_343]: (v2_pre_topc(B_342) | ~m1_pre_topc(B_342, A_343) | ~l1_pre_topc(A_343) | ~v2_pre_topc(A_343))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.39/1.74  tff(c_143, plain, (v2_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_60, c_134])).
% 4.39/1.74  tff(c_152, plain, (v2_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_143])).
% 4.39/1.74  tff(c_58, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_56, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_54, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_586, plain, (![C_410, E_409, D_413, A_411, B_412]: (k3_tmap_1(A_411, B_412, C_410, D_413, E_409)=k2_partfun1(u1_struct_0(C_410), u1_struct_0(B_412), E_409, u1_struct_0(D_413)) | ~m1_pre_topc(D_413, C_410) | ~m1_subset_1(E_409, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_410), u1_struct_0(B_412)))) | ~v1_funct_2(E_409, u1_struct_0(C_410), u1_struct_0(B_412)) | ~v1_funct_1(E_409) | ~m1_pre_topc(D_413, A_411) | ~m1_pre_topc(C_410, A_411) | ~l1_pre_topc(B_412) | ~v2_pre_topc(B_412) | v2_struct_0(B_412) | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.74  tff(c_588, plain, (![A_411, D_413]: (k3_tmap_1(A_411, '#skF_3', '#skF_6', D_413, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_413)) | ~m1_pre_topc(D_413, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_413, A_411) | ~m1_pre_topc('#skF_6', A_411) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(resolution, [status(thm)], [c_54, c_586])).
% 4.39/1.74  tff(c_591, plain, (![A_411, D_413]: (k3_tmap_1(A_411, '#skF_3', '#skF_6', D_413, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_413)) | ~m1_pre_topc(D_413, '#skF_6') | ~m1_pre_topc(D_413, A_411) | ~m1_pre_topc('#skF_6', A_411) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_411) | ~v2_pre_topc(A_411) | v2_struct_0(A_411))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_56, c_588])).
% 4.39/1.74  tff(c_688, plain, (![A_420, D_421]: (k3_tmap_1(A_420, '#skF_3', '#skF_6', D_421, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_421)) | ~m1_pre_topc(D_421, '#skF_6') | ~m1_pre_topc(D_421, A_420) | ~m1_pre_topc('#skF_6', A_420) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420) | v2_struct_0(A_420))), inference(negUnitSimplification, [status(thm)], [c_78, c_591])).
% 4.39/1.74  tff(c_696, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_688])).
% 4.39/1.74  tff(c_710, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_60, c_48, c_696])).
% 4.39/1.74  tff(c_711, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_710])).
% 4.39/1.74  tff(c_530, plain, (![A_398, B_399, C_400, D_401]: (k2_partfun1(u1_struct_0(A_398), u1_struct_0(B_399), C_400, u1_struct_0(D_401))=k2_tmap_1(A_398, B_399, C_400, D_401) | ~m1_pre_topc(D_401, A_398) | ~m1_subset_1(C_400, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_398), u1_struct_0(B_399)))) | ~v1_funct_2(C_400, u1_struct_0(A_398), u1_struct_0(B_399)) | ~v1_funct_1(C_400) | ~l1_pre_topc(B_399) | ~v2_pre_topc(B_399) | v2_struct_0(B_399) | ~l1_pre_topc(A_398) | ~v2_pre_topc(A_398) | v2_struct_0(A_398))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.39/1.74  tff(c_532, plain, (![D_401]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_401))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_401) | ~m1_pre_topc(D_401, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_530])).
% 4.39/1.74  tff(c_535, plain, (![D_401]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_401))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_401) | ~m1_pre_topc(D_401, '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_113, c_76, c_74, c_58, c_56, c_532])).
% 4.39/1.74  tff(c_536, plain, (![D_401]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_401))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_401) | ~m1_pre_topc(D_401, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_78, c_535])).
% 4.39/1.74  tff(c_730, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_711, c_536])).
% 4.39/1.74  tff(c_737, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_730])).
% 4.39/1.74  tff(c_86, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_310])).
% 4.39/1.74  tff(c_88, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_86])).
% 4.39/1.74  tff(c_178, plain, (r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_153, c_88])).
% 4.39/1.74  tff(c_742, plain, (r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_178])).
% 4.39/1.74  tff(c_771, plain, (![F_427, B_428, C_429, A_431, D_430]: (r1_tmap_1(B_428, A_431, C_429, F_427) | ~r1_tmap_1(D_430, A_431, k2_tmap_1(B_428, A_431, C_429, D_430), F_427) | ~m1_subset_1(F_427, u1_struct_0(D_430)) | ~m1_subset_1(F_427, u1_struct_0(B_428)) | ~m1_pre_topc(D_430, B_428) | ~v1_tsep_1(D_430, B_428) | v2_struct_0(D_430) | ~m1_subset_1(C_429, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_428), u1_struct_0(A_431)))) | ~v1_funct_2(C_429, u1_struct_0(B_428), u1_struct_0(A_431)) | ~v1_funct_1(C_429) | ~l1_pre_topc(B_428) | ~v2_pre_topc(B_428) | v2_struct_0(B_428) | ~l1_pre_topc(A_431) | ~v2_pre_topc(A_431) | v2_struct_0(A_431))), inference(cnfTransformation, [status(thm)], [f_245])).
% 4.39/1.74  tff(c_773, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_6') | ~v1_tsep_1('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_742, c_771])).
% 4.39/1.74  tff(c_776, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~v1_tsep_1('#skF_5', '#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_6') | v2_struct_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_152, c_113, c_58, c_56, c_54, c_48, c_46, c_90, c_773])).
% 4.39/1.74  tff(c_777, plain, (~v1_tsep_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_78, c_62, c_66, c_153, c_776])).
% 4.39/1.74  tff(c_780, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_tsep_1('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_582, c_777])).
% 4.39/1.74  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_52, c_64, c_780])).
% 4.39/1.74  tff(c_786, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_89])).
% 4.39/1.74  tff(c_1398, plain, (![F_513, C_514, A_511, D_510, B_512]: (r1_tmap_1(D_510, A_511, k2_tmap_1(B_512, A_511, C_514, D_510), F_513) | ~r1_tmap_1(B_512, A_511, C_514, F_513) | ~m1_subset_1(F_513, u1_struct_0(D_510)) | ~m1_subset_1(F_513, u1_struct_0(B_512)) | ~m1_pre_topc(D_510, B_512) | v2_struct_0(D_510) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(B_512), u1_struct_0(A_511)))) | ~v1_funct_2(C_514, u1_struct_0(B_512), u1_struct_0(A_511)) | ~v1_funct_1(C_514) | ~l1_pre_topc(B_512) | ~v2_pre_topc(B_512) | v2_struct_0(B_512) | ~l1_pre_topc(A_511) | ~v2_pre_topc(A_511) | v2_struct_0(A_511))), inference(cnfTransformation, [status(thm)], [f_203])).
% 4.39/1.74  tff(c_1400, plain, (![D_510, F_513]: (r1_tmap_1(D_510, '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_510), F_513) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', F_513) | ~m1_subset_1(F_513, u1_struct_0(D_510)) | ~m1_subset_1(F_513, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_510, '#skF_6') | v2_struct_0(D_510) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_54, c_1398])).
% 4.39/1.74  tff(c_1403, plain, (![D_510, F_513]: (r1_tmap_1(D_510, '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_510), F_513) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', F_513) | ~m1_subset_1(F_513, u1_struct_0(D_510)) | ~m1_subset_1(F_513, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_510, '#skF_6') | v2_struct_0(D_510) | v2_struct_0('#skF_6') | v2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_152, c_113, c_58, c_56, c_1400])).
% 4.39/1.74  tff(c_1411, plain, (![D_515, F_516]: (r1_tmap_1(D_515, '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_515), F_516) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', F_516) | ~m1_subset_1(F_516, u1_struct_0(D_515)) | ~m1_subset_1(F_516, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_515, '#skF_6') | v2_struct_0(D_515))), inference(negUnitSimplification, [status(thm)], [c_78, c_62, c_1403])).
% 4.39/1.74  tff(c_1295, plain, (![C_502, D_505, B_504, A_503, E_501]: (k3_tmap_1(A_503, B_504, C_502, D_505, E_501)=k2_partfun1(u1_struct_0(C_502), u1_struct_0(B_504), E_501, u1_struct_0(D_505)) | ~m1_pre_topc(D_505, C_502) | ~m1_subset_1(E_501, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_502), u1_struct_0(B_504)))) | ~v1_funct_2(E_501, u1_struct_0(C_502), u1_struct_0(B_504)) | ~v1_funct_1(E_501) | ~m1_pre_topc(D_505, A_503) | ~m1_pre_topc(C_502, A_503) | ~l1_pre_topc(B_504) | ~v2_pre_topc(B_504) | v2_struct_0(B_504) | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(cnfTransformation, [status(thm)], [f_132])).
% 4.39/1.74  tff(c_1297, plain, (![A_503, D_505]: (k3_tmap_1(A_503, '#skF_3', '#skF_6', D_505, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_505)) | ~m1_pre_topc(D_505, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_505, A_503) | ~m1_pre_topc('#skF_6', A_503) | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(resolution, [status(thm)], [c_54, c_1295])).
% 4.39/1.74  tff(c_1300, plain, (![A_503, D_505]: (k3_tmap_1(A_503, '#skF_3', '#skF_6', D_505, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_505)) | ~m1_pre_topc(D_505, '#skF_6') | ~m1_pre_topc(D_505, A_503) | ~m1_pre_topc('#skF_6', A_503) | v2_struct_0('#skF_3') | ~l1_pre_topc(A_503) | ~v2_pre_topc(A_503) | v2_struct_0(A_503))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_74, c_58, c_56, c_1297])).
% 4.39/1.74  tff(c_1327, plain, (![A_508, D_509]: (k3_tmap_1(A_508, '#skF_3', '#skF_6', D_509, '#skF_7')=k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_509)) | ~m1_pre_topc(D_509, '#skF_6') | ~m1_pre_topc(D_509, A_508) | ~m1_pre_topc('#skF_6', A_508) | ~l1_pre_topc(A_508) | ~v2_pre_topc(A_508) | v2_struct_0(A_508))), inference(negUnitSimplification, [status(thm)], [c_78, c_1300])).
% 4.39/1.74  tff(c_1335, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_64, c_1327])).
% 4.39/1.74  tff(c_1349, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_60, c_48, c_1335])).
% 4.39/1.74  tff(c_1350, plain, (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0('#skF_5'))=k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_72, c_1349])).
% 4.39/1.74  tff(c_1207, plain, (![A_490, B_491, C_492, D_493]: (k2_partfun1(u1_struct_0(A_490), u1_struct_0(B_491), C_492, u1_struct_0(D_493))=k2_tmap_1(A_490, B_491, C_492, D_493) | ~m1_pre_topc(D_493, A_490) | ~m1_subset_1(C_492, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(A_490), u1_struct_0(B_491)))) | ~v1_funct_2(C_492, u1_struct_0(A_490), u1_struct_0(B_491)) | ~v1_funct_1(C_492) | ~l1_pre_topc(B_491) | ~v2_pre_topc(B_491) | v2_struct_0(B_491) | ~l1_pre_topc(A_490) | ~v2_pre_topc(A_490) | v2_struct_0(A_490))), inference(cnfTransformation, [status(thm)], [f_100])).
% 4.39/1.74  tff(c_1209, plain, (![D_493]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_493))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_493) | ~m1_pre_topc(D_493, '#skF_6') | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_6') | ~v2_pre_topc('#skF_6') | v2_struct_0('#skF_6'))), inference(resolution, [status(thm)], [c_54, c_1207])).
% 4.39/1.74  tff(c_1212, plain, (![D_493]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_493))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_493) | ~m1_pre_topc(D_493, '#skF_6') | v2_struct_0('#skF_3') | v2_struct_0('#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_152, c_113, c_76, c_74, c_58, c_56, c_1209])).
% 4.39/1.74  tff(c_1213, plain, (![D_493]: (k2_partfun1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'), '#skF_7', u1_struct_0(D_493))=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', D_493) | ~m1_pre_topc(D_493, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_62, c_78, c_1212])).
% 4.39/1.74  tff(c_1362, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1350, c_1213])).
% 4.39/1.74  tff(c_1369, plain, (k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7')=k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1362])).
% 4.39/1.74  tff(c_785, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_89])).
% 4.39/1.74  tff(c_1374, plain, (~r1_tmap_1('#skF_5', '#skF_3', k2_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_5'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_1369, c_785])).
% 4.39/1.74  tff(c_1414, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_6') | v2_struct_0('#skF_5')), inference(resolution, [status(thm)], [c_1411, c_1374])).
% 4.39/1.74  tff(c_1417, plain, (v2_struct_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_46, c_90, c_786, c_1414])).
% 4.39/1.74  tff(c_1419, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_1417])).
% 4.39/1.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.39/1.74  
% 4.39/1.74  Inference rules
% 4.39/1.74  ----------------------
% 4.39/1.74  #Ref     : 0
% 4.39/1.74  #Sup     : 238
% 4.39/1.74  #Fact    : 0
% 4.39/1.74  #Define  : 0
% 4.39/1.74  #Split   : 10
% 4.39/1.74  #Chain   : 0
% 4.39/1.74  #Close   : 0
% 4.39/1.74  
% 4.39/1.74  Ordering : KBO
% 4.39/1.74  
% 4.39/1.74  Simplification rules
% 4.39/1.74  ----------------------
% 4.39/1.74  #Subsume      : 72
% 4.39/1.74  #Demod        : 416
% 4.39/1.74  #Tautology    : 83
% 4.39/1.74  #SimpNegUnit  : 101
% 4.39/1.74  #BackRed      : 4
% 4.39/1.74  
% 4.39/1.74  #Partial instantiations: 0
% 4.39/1.74  #Strategies tried      : 1
% 4.39/1.74  
% 4.39/1.74  Timing (in seconds)
% 4.39/1.74  ----------------------
% 4.39/1.74  Preprocessing        : 0.41
% 4.39/1.74  Parsing              : 0.22
% 4.39/1.74  CNF conversion       : 0.05
% 4.39/1.74  Main loop            : 0.50
% 4.39/1.74  Inferencing          : 0.17
% 4.39/1.74  Reduction            : 0.18
% 4.39/1.74  Demodulation         : 0.13
% 4.39/1.74  BG Simplification    : 0.03
% 4.39/1.74  Subsumption          : 0.09
% 4.39/1.74  Abstraction          : 0.02
% 4.39/1.74  MUC search           : 0.00
% 4.39/1.75  Cooper               : 0.00
% 4.39/1.75  Total                : 0.96
% 4.39/1.75  Index Insertion      : 0.00
% 4.39/1.75  Index Deletion       : 0.00
% 4.39/1.75  Index Matching       : 0.00
% 4.39/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
