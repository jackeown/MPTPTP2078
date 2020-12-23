%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:31 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 184 expanded)
%              Number of leaves         :   37 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  295 (1453 expanded)
%              Number of equality atoms :    5 (  64 expanded)
%              Maximal formula depth    :   26 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1

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

tff(f_242,negated_conjecture,(
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

tff(f_48,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_79,axiom,(
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

tff(f_72,axiom,(
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

tff(f_189,axiom,(
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

tff(f_139,axiom,(
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

tff(c_64,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_62,plain,(
    v2_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_60,plain,(
    l1_pre_topc('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_52,plain,(
    m1_pre_topc('#skF_6','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_56,plain,(
    m1_pre_topc('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_34,plain,(
    '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_36,plain,(
    m1_subset_1('#skF_9',u1_struct_0('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_82,plain,(
    m1_subset_1('#skF_8',u1_struct_0('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_36])).

tff(c_40,plain,(
    m1_pre_topc('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_44,plain,(
    v1_tsep_1('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_54,plain,(
    ~ v2_struct_0('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_89,plain,(
    ! [B_406,A_407] :
      ( l1_pre_topc(B_406)
      | ~ m1_pre_topc(B_406,A_407)
      | ~ l1_pre_topc(A_407) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_92,plain,
    ( l1_pre_topc('#skF_6')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_89])).

tff(c_101,plain,(
    l1_pre_topc('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_92])).

tff(c_126,plain,(
    ! [B_414,A_415] :
      ( m1_subset_1(u1_struct_0(B_414),k1_zfmisc_1(u1_struct_0(A_415)))
      | ~ m1_pre_topc(B_414,A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [A_410,B_411] :
      ( r2_hidden(A_410,B_411)
      | v1_xboole_0(B_411)
      | ~ m1_subset_1(A_410,B_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( r1_tarski(C_5,A_1)
      | ~ r2_hidden(C_5,k1_zfmisc_1(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_117,plain,(
    ! [A_410,A_1] :
      ( r1_tarski(A_410,A_1)
      | v1_xboole_0(k1_zfmisc_1(A_1))
      | ~ m1_subset_1(A_410,k1_zfmisc_1(A_1)) ) ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_120,plain,(
    ! [A_410,A_1] :
      ( r1_tarski(A_410,A_1)
      | ~ m1_subset_1(A_410,k1_zfmisc_1(A_1)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_117])).

tff(c_130,plain,(
    ! [B_414,A_415] :
      ( r1_tarski(u1_struct_0(B_414),u1_struct_0(A_415))
      | ~ m1_pre_topc(B_414,A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(resolution,[status(thm)],[c_126,c_120])).

tff(c_224,plain,(
    ! [B_440,C_441,A_442] :
      ( v1_tsep_1(B_440,C_441)
      | ~ r1_tarski(u1_struct_0(B_440),u1_struct_0(C_441))
      | ~ m1_pre_topc(C_441,A_442)
      | v2_struct_0(C_441)
      | ~ m1_pre_topc(B_440,A_442)
      | ~ v1_tsep_1(B_440,A_442)
      | ~ l1_pre_topc(A_442)
      | ~ v2_pre_topc(A_442)
      | v2_struct_0(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_346,plain,(
    ! [B_456,A_457,A_458] :
      ( v1_tsep_1(B_456,A_457)
      | ~ m1_pre_topc(A_457,A_458)
      | v2_struct_0(A_457)
      | ~ m1_pre_topc(B_456,A_458)
      | ~ v1_tsep_1(B_456,A_458)
      | ~ l1_pre_topc(A_458)
      | ~ v2_pre_topc(A_458)
      | v2_struct_0(A_458)
      | ~ m1_pre_topc(B_456,A_457)
      | ~ l1_pre_topc(A_457) ) ),
    inference(resolution,[status(thm)],[c_130,c_224])).

tff(c_354,plain,(
    ! [B_456] :
      ( v1_tsep_1(B_456,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_456,'#skF_4')
      | ~ v1_tsep_1(B_456,'#skF_4')
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_456,'#skF_6')
      | ~ l1_pre_topc('#skF_6') ) ),
    inference(resolution,[status(thm)],[c_52,c_346])).

tff(c_373,plain,(
    ! [B_456] :
      ( v1_tsep_1(B_456,'#skF_6')
      | v2_struct_0('#skF_6')
      | ~ m1_pre_topc(B_456,'#skF_4')
      | ~ v1_tsep_1(B_456,'#skF_4')
      | v2_struct_0('#skF_4')
      | ~ m1_pre_topc(B_456,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_62,c_60,c_354])).

tff(c_374,plain,(
    ! [B_456] :
      ( v1_tsep_1(B_456,'#skF_6')
      | ~ m1_pre_topc(B_456,'#skF_4')
      | ~ v1_tsep_1(B_456,'#skF_4')
      | ~ m1_pre_topc(B_456,'#skF_6') ) ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_54,c_373])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_72,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_81,plain,
    ( ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8')
    | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_72])).

tff(c_131,plain,(
    ~ r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_68,plain,(
    v2_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_66,plain,(
    l1_pre_topc('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_50,plain,(
    v1_funct_1('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_48,plain,(
    v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'),u1_struct_0('#skF_3')))) ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_78,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_242])).

tff(c_80,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_78])).

tff(c_183,plain,(
    r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_131,c_80])).

tff(c_445,plain,(
    ! [A_476,D_471,C_472,E_473,B_474,G_475] :
      ( r1_tmap_1(D_471,B_474,E_473,G_475)
      | ~ r1_tmap_1(C_472,B_474,k3_tmap_1(A_476,B_474,D_471,C_472,E_473),G_475)
      | ~ m1_subset_1(G_475,u1_struct_0(C_472))
      | ~ m1_subset_1(G_475,u1_struct_0(D_471))
      | ~ m1_pre_topc(C_472,D_471)
      | ~ v1_tsep_1(C_472,D_471)
      | ~ m1_subset_1(E_473,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_471),u1_struct_0(B_474))))
      | ~ v1_funct_2(E_473,u1_struct_0(D_471),u1_struct_0(B_474))
      | ~ v1_funct_1(E_473)
      | ~ m1_pre_topc(D_471,A_476)
      | v2_struct_0(D_471)
      | ~ m1_pre_topc(C_472,A_476)
      | v2_struct_0(C_472)
      | ~ l1_pre_topc(B_474)
      | ~ v2_pre_topc(B_474)
      | v2_struct_0(B_474)
      | ~ l1_pre_topc(A_476)
      | ~ v2_pre_topc(A_476)
      | v2_struct_0(A_476) ) ),
    inference(cnfTransformation,[status(thm)],[f_189])).

tff(c_447,plain,
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
    inference(resolution,[status(thm)],[c_183,c_445])).

tff(c_450,plain,
    ( r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8')
    | ~ v1_tsep_1('#skF_5','#skF_6')
    | v2_struct_0('#skF_6')
    | v2_struct_0('#skF_5')
    | v2_struct_0('#skF_3')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_68,c_66,c_56,c_52,c_50,c_48,c_46,c_40,c_38,c_82,c_447])).

tff(c_451,plain,(
    ~ v1_tsep_1('#skF_5','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_70,c_58,c_54,c_131,c_450])).

tff(c_454,plain,
    ( ~ m1_pre_topc('#skF_5','#skF_4')
    | ~ v1_tsep_1('#skF_5','#skF_4')
    | ~ m1_pre_topc('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_374,c_451])).

tff(c_458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44,c_56,c_454])).

tff(c_460,plain,(
    r1_tmap_1('#skF_6','#skF_3','#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_715,plain,(
    ! [B_527,C_522,E_526,G_524,A_525,D_523] :
      ( r1_tmap_1(D_523,B_527,k3_tmap_1(A_525,B_527,C_522,D_523,E_526),G_524)
      | ~ r1_tmap_1(C_522,B_527,E_526,G_524)
      | ~ m1_pre_topc(D_523,C_522)
      | ~ m1_subset_1(G_524,u1_struct_0(D_523))
      | ~ m1_subset_1(G_524,u1_struct_0(C_522))
      | ~ m1_subset_1(E_526,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_522),u1_struct_0(B_527))))
      | ~ v1_funct_2(E_526,u1_struct_0(C_522),u1_struct_0(B_527))
      | ~ v1_funct_1(E_526)
      | ~ m1_pre_topc(D_523,A_525)
      | v2_struct_0(D_523)
      | ~ m1_pre_topc(C_522,A_525)
      | v2_struct_0(C_522)
      | ~ l1_pre_topc(B_527)
      | ~ v2_pre_topc(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_717,plain,(
    ! [D_523,A_525,G_524] :
      ( r1_tmap_1(D_523,'#skF_3',k3_tmap_1(A_525,'#skF_3','#skF_6',D_523,'#skF_7'),G_524)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_524)
      | ~ m1_pre_topc(D_523,'#skF_6')
      | ~ m1_subset_1(G_524,u1_struct_0(D_523))
      | ~ m1_subset_1(G_524,u1_struct_0('#skF_6'))
      | ~ v1_funct_2('#skF_7',u1_struct_0('#skF_6'),u1_struct_0('#skF_3'))
      | ~ v1_funct_1('#skF_7')
      | ~ m1_pre_topc(D_523,A_525)
      | v2_struct_0(D_523)
      | ~ m1_pre_topc('#skF_6',A_525)
      | v2_struct_0('#skF_6')
      | ~ l1_pre_topc('#skF_3')
      | ~ v2_pre_topc('#skF_3')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(resolution,[status(thm)],[c_46,c_715])).

tff(c_720,plain,(
    ! [D_523,A_525,G_524] :
      ( r1_tmap_1(D_523,'#skF_3',k3_tmap_1(A_525,'#skF_3','#skF_6',D_523,'#skF_7'),G_524)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_524)
      | ~ m1_pre_topc(D_523,'#skF_6')
      | ~ m1_subset_1(G_524,u1_struct_0(D_523))
      | ~ m1_subset_1(G_524,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_523,A_525)
      | v2_struct_0(D_523)
      | ~ m1_pre_topc('#skF_6',A_525)
      | v2_struct_0('#skF_6')
      | v2_struct_0('#skF_3')
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_66,c_50,c_48,c_717])).

tff(c_795,plain,(
    ! [D_540,A_541,G_542] :
      ( r1_tmap_1(D_540,'#skF_3',k3_tmap_1(A_541,'#skF_3','#skF_6',D_540,'#skF_7'),G_542)
      | ~ r1_tmap_1('#skF_6','#skF_3','#skF_7',G_542)
      | ~ m1_pre_topc(D_540,'#skF_6')
      | ~ m1_subset_1(G_542,u1_struct_0(D_540))
      | ~ m1_subset_1(G_542,u1_struct_0('#skF_6'))
      | ~ m1_pre_topc(D_540,A_541)
      | v2_struct_0(D_540)
      | ~ m1_pre_topc('#skF_6',A_541)
      | ~ l1_pre_topc(A_541)
      | ~ v2_pre_topc(A_541)
      | v2_struct_0(A_541) ) ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_54,c_720])).

tff(c_459,plain,(
    ~ r1_tmap_1('#skF_5','#skF_3',k3_tmap_1('#skF_4','#skF_3','#skF_6','#skF_5','#skF_7'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_800,plain,
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
    inference(resolution,[status(thm)],[c_795,c_459])).

tff(c_807,plain,
    ( v2_struct_0('#skF_5')
    | v2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_52,c_56,c_38,c_82,c_40,c_460,c_800])).

tff(c_809,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_58,c_807])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:56:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.58  
% 3.25/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.58  %$ r1_tmap_1 > v1_funct_2 > v1_tsep_1 > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > #nlpp > u1_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_2 > #skF_1
% 3.25/1.58  
% 3.25/1.58  %Foreground sorts:
% 3.25/1.58  
% 3.25/1.58  
% 3.25/1.58  %Background operators:
% 3.25/1.58  
% 3.25/1.58  
% 3.25/1.58  %Foreground operators:
% 3.25/1.58  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.25/1.58  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.58  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.58  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.25/1.58  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.25/1.58  tff('#skF_7', type, '#skF_7': $i).
% 3.25/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.25/1.58  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.58  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.58  tff('#skF_6', type, '#skF_6': $i).
% 3.25/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.25/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.58  tff('#skF_8', type, '#skF_8': $i).
% 3.25/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.58  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.58  tff(v1_tsep_1, type, v1_tsep_1: ($i * $i) > $o).
% 3.25/1.58  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.25/1.58  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.25/1.58  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.25/1.58  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.25/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.25/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.25/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.58  
% 3.25/1.60  tff(f_242, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, B)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, B)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(A))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(A))))) => (((v1_tsep_1(C, B) & m1_pre_topc(C, B)) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, A, E, F) <=> r1_tmap_1(C, A, k3_tmap_1(B, A, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_tmap_1)).
% 3.25/1.60  tff(f_48, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.25/1.60  tff(f_79, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tsep_1)).
% 3.25/1.60  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.25/1.60  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 3.25/1.60  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.25/1.60  tff(f_72, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: ((v1_tsep_1(B, A) & m1_pre_topc(B, A)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (r1_tarski(u1_struct_0(B), u1_struct_0(C)) => (v1_tsep_1(B, C) & m1_pre_topc(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_tsep_1)).
% 3.25/1.60  tff(f_189, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((v1_tsep_1(C, D) & m1_pre_topc(C, D)) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => ((F = G) => (r1_tmap_1(D, B, E, F) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_tmap_1)).
% 3.25/1.60  tff(f_139, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(C), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C), u1_struct_0(B))))) => (![F]: (m1_subset_1(F, u1_struct_0(C)) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => ((((F = G) & m1_pre_topc(D, C)) & r1_tmap_1(C, B, E, F)) => r1_tmap_1(D, B, k3_tmap_1(A, B, C, D, E), G)))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_tmap_1)).
% 3.25/1.60  tff(c_64, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_58, plain, (~v2_struct_0('#skF_5')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_62, plain, (v2_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_60, plain, (l1_pre_topc('#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_52, plain, (m1_pre_topc('#skF_6', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_56, plain, (m1_pre_topc('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_38, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_34, plain, ('#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_36, plain, (m1_subset_1('#skF_9', u1_struct_0('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_82, plain, (m1_subset_1('#skF_8', u1_struct_0('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_36])).
% 3.25/1.60  tff(c_40, plain, (m1_pre_topc('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_44, plain, (v1_tsep_1('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_54, plain, (~v2_struct_0('#skF_6')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_89, plain, (![B_406, A_407]: (l1_pre_topc(B_406) | ~m1_pre_topc(B_406, A_407) | ~l1_pre_topc(A_407))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.25/1.60  tff(c_92, plain, (l1_pre_topc('#skF_6') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_52, c_89])).
% 3.25/1.60  tff(c_101, plain, (l1_pre_topc('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_92])).
% 3.25/1.60  tff(c_126, plain, (![B_414, A_415]: (m1_subset_1(u1_struct_0(B_414), k1_zfmisc_1(u1_struct_0(A_415))) | ~m1_pre_topc(B_414, A_415) | ~l1_pre_topc(A_415))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.25/1.60  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.60  tff(c_113, plain, (![A_410, B_411]: (r2_hidden(A_410, B_411) | v1_xboole_0(B_411) | ~m1_subset_1(A_410, B_411))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.25/1.60  tff(c_2, plain, (![C_5, A_1]: (r1_tarski(C_5, A_1) | ~r2_hidden(C_5, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.25/1.60  tff(c_117, plain, (![A_410, A_1]: (r1_tarski(A_410, A_1) | v1_xboole_0(k1_zfmisc_1(A_1)) | ~m1_subset_1(A_410, k1_zfmisc_1(A_1)))), inference(resolution, [status(thm)], [c_113, c_2])).
% 3.25/1.60  tff(c_120, plain, (![A_410, A_1]: (r1_tarski(A_410, A_1) | ~m1_subset_1(A_410, k1_zfmisc_1(A_1)))), inference(negUnitSimplification, [status(thm)], [c_14, c_117])).
% 3.25/1.60  tff(c_130, plain, (![B_414, A_415]: (r1_tarski(u1_struct_0(B_414), u1_struct_0(A_415)) | ~m1_pre_topc(B_414, A_415) | ~l1_pre_topc(A_415))), inference(resolution, [status(thm)], [c_126, c_120])).
% 3.25/1.60  tff(c_224, plain, (![B_440, C_441, A_442]: (v1_tsep_1(B_440, C_441) | ~r1_tarski(u1_struct_0(B_440), u1_struct_0(C_441)) | ~m1_pre_topc(C_441, A_442) | v2_struct_0(C_441) | ~m1_pre_topc(B_440, A_442) | ~v1_tsep_1(B_440, A_442) | ~l1_pre_topc(A_442) | ~v2_pre_topc(A_442) | v2_struct_0(A_442))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.25/1.60  tff(c_346, plain, (![B_456, A_457, A_458]: (v1_tsep_1(B_456, A_457) | ~m1_pre_topc(A_457, A_458) | v2_struct_0(A_457) | ~m1_pre_topc(B_456, A_458) | ~v1_tsep_1(B_456, A_458) | ~l1_pre_topc(A_458) | ~v2_pre_topc(A_458) | v2_struct_0(A_458) | ~m1_pre_topc(B_456, A_457) | ~l1_pre_topc(A_457))), inference(resolution, [status(thm)], [c_130, c_224])).
% 3.25/1.60  tff(c_354, plain, (![B_456]: (v1_tsep_1(B_456, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_456, '#skF_4') | ~v1_tsep_1(B_456, '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_456, '#skF_6') | ~l1_pre_topc('#skF_6'))), inference(resolution, [status(thm)], [c_52, c_346])).
% 3.25/1.60  tff(c_373, plain, (![B_456]: (v1_tsep_1(B_456, '#skF_6') | v2_struct_0('#skF_6') | ~m1_pre_topc(B_456, '#skF_4') | ~v1_tsep_1(B_456, '#skF_4') | v2_struct_0('#skF_4') | ~m1_pre_topc(B_456, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_101, c_62, c_60, c_354])).
% 3.25/1.60  tff(c_374, plain, (![B_456]: (v1_tsep_1(B_456, '#skF_6') | ~m1_pre_topc(B_456, '#skF_4') | ~v1_tsep_1(B_456, '#skF_4') | ~m1_pre_topc(B_456, '#skF_6'))), inference(negUnitSimplification, [status(thm)], [c_64, c_54, c_373])).
% 3.25/1.60  tff(c_70, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_72, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_81, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8') | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_72])).
% 3.25/1.60  tff(c_131, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(splitLeft, [status(thm)], [c_81])).
% 3.25/1.60  tff(c_68, plain, (v2_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_66, plain, (l1_pre_topc('#skF_3')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_50, plain, (v1_funct_1('#skF_7')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_48, plain, (v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_46, plain, (m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3'))))), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_78, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_242])).
% 3.25/1.60  tff(c_80, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_78])).
% 3.25/1.60  tff(c_183, plain, (r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_131, c_80])).
% 3.25/1.60  tff(c_445, plain, (![A_476, D_471, C_472, E_473, B_474, G_475]: (r1_tmap_1(D_471, B_474, E_473, G_475) | ~r1_tmap_1(C_472, B_474, k3_tmap_1(A_476, B_474, D_471, C_472, E_473), G_475) | ~m1_subset_1(G_475, u1_struct_0(C_472)) | ~m1_subset_1(G_475, u1_struct_0(D_471)) | ~m1_pre_topc(C_472, D_471) | ~v1_tsep_1(C_472, D_471) | ~m1_subset_1(E_473, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_471), u1_struct_0(B_474)))) | ~v1_funct_2(E_473, u1_struct_0(D_471), u1_struct_0(B_474)) | ~v1_funct_1(E_473) | ~m1_pre_topc(D_471, A_476) | v2_struct_0(D_471) | ~m1_pre_topc(C_472, A_476) | v2_struct_0(C_472) | ~l1_pre_topc(B_474) | ~v2_pre_topc(B_474) | v2_struct_0(B_474) | ~l1_pre_topc(A_476) | ~v2_pre_topc(A_476) | v2_struct_0(A_476))), inference(cnfTransformation, [status(thm)], [f_189])).
% 3.25/1.60  tff(c_447, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_6') | ~v1_tsep_1('#skF_5', '#skF_6') | ~m1_subset_1('#skF_7', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_6'), u1_struct_0('#skF_3')))) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc('#skF_6', '#skF_4') | v2_struct_0('#skF_6') | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_183, c_445])).
% 3.25/1.60  tff(c_450, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~v1_tsep_1('#skF_5', '#skF_6') | v2_struct_0('#skF_6') | v2_struct_0('#skF_5') | v2_struct_0('#skF_3') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_68, c_66, c_56, c_52, c_50, c_48, c_46, c_40, c_38, c_82, c_447])).
% 3.25/1.60  tff(c_451, plain, (~v1_tsep_1('#skF_5', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_64, c_70, c_58, c_54, c_131, c_450])).
% 3.25/1.60  tff(c_454, plain, (~m1_pre_topc('#skF_5', '#skF_4') | ~v1_tsep_1('#skF_5', '#skF_4') | ~m1_pre_topc('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_374, c_451])).
% 3.25/1.60  tff(c_458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_44, c_56, c_454])).
% 3.25/1.60  tff(c_460, plain, (r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 3.25/1.60  tff(c_715, plain, (![B_527, C_522, E_526, G_524, A_525, D_523]: (r1_tmap_1(D_523, B_527, k3_tmap_1(A_525, B_527, C_522, D_523, E_526), G_524) | ~r1_tmap_1(C_522, B_527, E_526, G_524) | ~m1_pre_topc(D_523, C_522) | ~m1_subset_1(G_524, u1_struct_0(D_523)) | ~m1_subset_1(G_524, u1_struct_0(C_522)) | ~m1_subset_1(E_526, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(C_522), u1_struct_0(B_527)))) | ~v1_funct_2(E_526, u1_struct_0(C_522), u1_struct_0(B_527)) | ~v1_funct_1(E_526) | ~m1_pre_topc(D_523, A_525) | v2_struct_0(D_523) | ~m1_pre_topc(C_522, A_525) | v2_struct_0(C_522) | ~l1_pre_topc(B_527) | ~v2_pre_topc(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_525) | ~v2_pre_topc(A_525) | v2_struct_0(A_525))), inference(cnfTransformation, [status(thm)], [f_139])).
% 3.25/1.60  tff(c_717, plain, (![D_523, A_525, G_524]: (r1_tmap_1(D_523, '#skF_3', k3_tmap_1(A_525, '#skF_3', '#skF_6', D_523, '#skF_7'), G_524) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_524) | ~m1_pre_topc(D_523, '#skF_6') | ~m1_subset_1(G_524, u1_struct_0(D_523)) | ~m1_subset_1(G_524, u1_struct_0('#skF_6')) | ~v1_funct_2('#skF_7', u1_struct_0('#skF_6'), u1_struct_0('#skF_3')) | ~v1_funct_1('#skF_7') | ~m1_pre_topc(D_523, A_525) | v2_struct_0(D_523) | ~m1_pre_topc('#skF_6', A_525) | v2_struct_0('#skF_6') | ~l1_pre_topc('#skF_3') | ~v2_pre_topc('#skF_3') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_525) | ~v2_pre_topc(A_525) | v2_struct_0(A_525))), inference(resolution, [status(thm)], [c_46, c_715])).
% 3.25/1.60  tff(c_720, plain, (![D_523, A_525, G_524]: (r1_tmap_1(D_523, '#skF_3', k3_tmap_1(A_525, '#skF_3', '#skF_6', D_523, '#skF_7'), G_524) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_524) | ~m1_pre_topc(D_523, '#skF_6') | ~m1_subset_1(G_524, u1_struct_0(D_523)) | ~m1_subset_1(G_524, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_523, A_525) | v2_struct_0(D_523) | ~m1_pre_topc('#skF_6', A_525) | v2_struct_0('#skF_6') | v2_struct_0('#skF_3') | ~l1_pre_topc(A_525) | ~v2_pre_topc(A_525) | v2_struct_0(A_525))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_66, c_50, c_48, c_717])).
% 3.25/1.60  tff(c_795, plain, (![D_540, A_541, G_542]: (r1_tmap_1(D_540, '#skF_3', k3_tmap_1(A_541, '#skF_3', '#skF_6', D_540, '#skF_7'), G_542) | ~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', G_542) | ~m1_pre_topc(D_540, '#skF_6') | ~m1_subset_1(G_542, u1_struct_0(D_540)) | ~m1_subset_1(G_542, u1_struct_0('#skF_6')) | ~m1_pre_topc(D_540, A_541) | v2_struct_0(D_540) | ~m1_pre_topc('#skF_6', A_541) | ~l1_pre_topc(A_541) | ~v2_pre_topc(A_541) | v2_struct_0(A_541))), inference(negUnitSimplification, [status(thm)], [c_70, c_54, c_720])).
% 3.25/1.60  tff(c_459, plain, (~r1_tmap_1('#skF_5', '#skF_3', k3_tmap_1('#skF_4', '#skF_3', '#skF_6', '#skF_5', '#skF_7'), '#skF_8')), inference(splitRight, [status(thm)], [c_81])).
% 3.25/1.60  tff(c_800, plain, (~r1_tmap_1('#skF_6', '#skF_3', '#skF_7', '#skF_8') | ~m1_pre_topc('#skF_5', '#skF_6') | ~m1_subset_1('#skF_8', u1_struct_0('#skF_5')) | ~m1_subset_1('#skF_8', u1_struct_0('#skF_6')) | ~m1_pre_topc('#skF_5', '#skF_4') | v2_struct_0('#skF_5') | ~m1_pre_topc('#skF_6', '#skF_4') | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_795, c_459])).
% 3.25/1.60  tff(c_807, plain, (v2_struct_0('#skF_5') | v2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_52, c_56, c_38, c_82, c_40, c_460, c_800])).
% 3.25/1.60  tff(c_809, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_58, c_807])).
% 3.25/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.60  
% 3.25/1.60  Inference rules
% 3.25/1.60  ----------------------
% 3.25/1.60  #Ref     : 0
% 3.25/1.60  #Sup     : 128
% 3.25/1.60  #Fact    : 0
% 3.25/1.60  #Define  : 0
% 3.25/1.60  #Split   : 9
% 3.25/1.60  #Chain   : 0
% 3.25/1.60  #Close   : 0
% 3.25/1.60  
% 3.25/1.60  Ordering : KBO
% 3.25/1.60  
% 3.25/1.60  Simplification rules
% 3.25/1.60  ----------------------
% 3.25/1.60  #Subsume      : 34
% 3.25/1.60  #Demod        : 188
% 3.25/1.60  #Tautology    : 45
% 3.25/1.60  #SimpNegUnit  : 41
% 3.25/1.60  #BackRed      : 0
% 3.25/1.60  
% 3.25/1.60  #Partial instantiations: 0
% 3.25/1.60  #Strategies tried      : 1
% 3.25/1.60  
% 3.25/1.60  Timing (in seconds)
% 3.25/1.60  ----------------------
% 3.54/1.60  Preprocessing        : 0.39
% 3.54/1.60  Parsing              : 0.19
% 3.54/1.60  CNF conversion       : 0.06
% 3.54/1.60  Main loop            : 0.37
% 3.54/1.60  Inferencing          : 0.13
% 3.54/1.60  Reduction            : 0.12
% 3.54/1.60  Demodulation         : 0.08
% 3.54/1.60  BG Simplification    : 0.02
% 3.54/1.60  Subsumption          : 0.08
% 3.54/1.60  Abstraction          : 0.02
% 3.54/1.60  MUC search           : 0.00
% 3.54/1.60  Cooper               : 0.00
% 3.54/1.60  Total                : 0.80
% 3.54/1.60  Index Insertion      : 0.00
% 3.54/1.60  Index Deletion       : 0.00
% 3.54/1.60  Index Matching       : 0.00
% 3.54/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
