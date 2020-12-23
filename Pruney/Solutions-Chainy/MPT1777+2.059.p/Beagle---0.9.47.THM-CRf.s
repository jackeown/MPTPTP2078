%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:40 EST 2020

% Result     : Theorem 3.56s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :  137 ( 976 expanded)
%              Number of leaves         :   45 ( 362 expanded)
%              Depth                    :   16
%              Number of atoms          :  273 (4613 expanded)
%              Number of equality atoms :   15 ( 526 expanded)
%              Maximal formula depth    :   30 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_struct_0,type,(
    v2_struct_0: $i > $o )).

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

tff(u1_struct_0,type,(
    u1_struct_0: $i > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_224,negated_conjecture,(
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

tff(f_54,axiom,(
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

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_88,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_99,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_106,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_82,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_175,axiom,(
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

tff(c_70,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_56,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_161,plain,(
    ! [B_417,A_418] :
      ( l1_pre_topc(B_417)
      | ~ m1_pre_topc(B_417,A_418)
      | ~ l1_pre_topc(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_170,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_161])).

tff(c_177,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_170])).

tff(c_14,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_58,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_98,plain,(
    ! [A_414] :
      ( u1_struct_0(A_414) = k2_struct_0(A_414)
      | ~ l1_struct_0(A_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_102,plain,(
    ! [A_12] :
      ( u1_struct_0(A_12) = k2_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_98])).

tff(c_185,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_177,c_102])).

tff(c_18,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_216,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_18])).

tff(c_219,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_216])).

tff(c_222,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_219])).

tff(c_225,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_225])).

tff(c_230,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_219])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_212,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_46])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_243,plain,(
    ! [B_422,A_423] :
      ( v2_pre_topc(B_422)
      | ~ m1_pre_topc(B_422,A_423)
      | ~ l1_pre_topc(A_423)
      | ~ v2_pre_topc(A_423) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_252,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_243])).

tff(c_259,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_252])).

tff(c_24,plain,(
    ! [A_20] :
      ( v3_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_28,plain,(
    ! [A_24] :
      ( m1_pre_topc(A_24,A_24)
      | ~ l1_pre_topc(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_272,plain,(
    ! [B_429,A_430] :
      ( r1_tarski(u1_struct_0(B_429),u1_struct_0(A_430))
      | ~ m1_pre_topc(B_429,A_430)
      | ~ l1_pre_topc(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_278,plain,(
    ! [B_429] :
      ( r1_tarski(u1_struct_0(B_429),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_429,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_272])).

tff(c_305,plain,(
    ! [B_431] :
      ( r1_tarski(u1_struct_0(B_431),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_431,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_278])).

tff(c_308,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_305])).

tff(c_449,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_452,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_28,c_449])).

tff(c_456,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_452])).

tff(c_458,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_60,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_167,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_60,c_161])).

tff(c_174,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_167])).

tff(c_181,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_174,c_102])).

tff(c_48,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_186,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_48])).

tff(c_601,plain,(
    ! [A_445,B_446] :
      ( m1_pre_topc(A_445,B_446)
      | ~ m1_pre_topc(A_445,g1_pre_topc(u1_struct_0(B_446),u1_pre_topc(B_446)))
      | ~ l1_pre_topc(B_446)
      | ~ l1_pre_topc(A_445) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_610,plain,(
    ! [A_445] :
      ( m1_pre_topc(A_445,'#skF_3')
      | ~ m1_pre_topc(A_445,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_445) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_601])).

tff(c_631,plain,(
    ! [A_447] :
      ( m1_pre_topc(A_447,'#skF_3')
      | ~ m1_pre_topc(A_447,'#skF_4')
      | ~ l1_pre_topc(A_447) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_186,c_610])).

tff(c_284,plain,(
    ! [B_429] :
      ( r1_tarski(u1_struct_0(B_429),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_429,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_272])).

tff(c_318,plain,(
    ! [B_432] :
      ( r1_tarski(u1_struct_0(B_432),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_432,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_284])).

tff(c_321,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_318])).

tff(c_434,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_637,plain,
    ( ~ m1_pre_topc('#skF_4','#skF_4')
    | ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_631,c_434])).

tff(c_657,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_177,c_458,c_637])).

tff(c_658,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_77,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_74,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_62,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_38,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_66,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_64,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_54,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_103,plain,(
    ! [A_415] :
      ( u1_struct_0(A_415) = k2_struct_0(A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(resolution,[status(thm)],[c_14,c_98])).

tff(c_111,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_103])).

tff(c_52,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_116,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_52])).

tff(c_232,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_116])).

tff(c_50,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_145,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_50])).

tff(c_211,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_145])).

tff(c_837,plain,(
    ! [A_454,B_455] :
      ( m1_pre_topc(A_454,g1_pre_topc(u1_struct_0(B_455),u1_pre_topc(B_455)))
      | ~ m1_pre_topc(A_454,B_455)
      | ~ l1_pre_topc(B_455)
      | ~ l1_pre_topc(A_454) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_858,plain,(
    ! [A_454] :
      ( m1_pre_topc(A_454,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_454,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_454) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_837])).

tff(c_880,plain,(
    ! [A_456] :
      ( m1_pre_topc(A_456,'#skF_4')
      | ~ m1_pre_topc(A_456,'#skF_3')
      | ~ l1_pre_topc(A_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_186,c_858])).

tff(c_897,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_880])).

tff(c_910,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_174,c_897])).

tff(c_42,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_75,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_187,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_75])).

tff(c_40,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_224])).

tff(c_76,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_40])).

tff(c_1030,plain,(
    ! [B_473,H_476,A_472,F_474,C_477,D_478,E_475] :
      ( r1_tmap_1(D_478,B_473,E_475,H_476)
      | ~ r1_tmap_1(C_477,B_473,k3_tmap_1(A_472,B_473,D_478,C_477,E_475),H_476)
      | ~ r1_tarski(F_474,u1_struct_0(C_477))
      | ~ r2_hidden(H_476,F_474)
      | ~ v3_pre_topc(F_474,D_478)
      | ~ m1_subset_1(H_476,u1_struct_0(C_477))
      | ~ m1_subset_1(H_476,u1_struct_0(D_478))
      | ~ m1_subset_1(F_474,k1_zfmisc_1(u1_struct_0(D_478)))
      | ~ m1_pre_topc(C_477,D_478)
      | ~ m1_subset_1(E_475,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_478),u1_struct_0(B_473))))
      | ~ v1_funct_2(E_475,u1_struct_0(D_478),u1_struct_0(B_473))
      | ~ v1_funct_1(E_475)
      | ~ m1_pre_topc(D_478,A_472)
      | v2_struct_0(D_478)
      | ~ m1_pre_topc(C_477,A_472)
      | v2_struct_0(C_477)
      | ~ l1_pre_topc(B_473)
      | ~ v2_pre_topc(B_473)
      | v2_struct_0(B_473)
      | ~ l1_pre_topc(A_472)
      | ~ v2_pre_topc(A_472)
      | v2_struct_0(A_472) ) ),
    inference(cnfTransformation,[status(thm)],[f_175])).

tff(c_1032,plain,(
    ! [F_474] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_474,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_474)
      | ~ v3_pre_topc(F_474,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_474,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_76,c_1030])).

tff(c_1035,plain,(
    ! [F_474] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_474,k2_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_474)
      | ~ v3_pre_topc(F_474,'#skF_4')
      | ~ m1_subset_1(F_474,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_70,c_66,c_64,c_60,c_56,c_54,c_232,c_111,c_185,c_211,c_111,c_185,c_910,c_185,c_212,c_185,c_187,c_181,c_181,c_1032])).

tff(c_1054,plain,(
    ! [F_481] :
      ( ~ r1_tarski(F_481,k2_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_481)
      | ~ v3_pre_topc(F_481,'#skF_4')
      | ~ m1_subset_1(F_481,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_68,c_62,c_58,c_38,c_1035])).

tff(c_1064,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_77,c_1054])).

tff(c_1071,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_658,c_1064])).

tff(c_1073,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1071])).

tff(c_1076,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_1073])).

tff(c_1080,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_259,c_177,c_1076])).

tff(c_1081,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1071])).

tff(c_1085,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1081])).

tff(c_1088,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_1085])).

tff(c_1090,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_230,c_1088])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.18/0.34  % CPULimit   : 60
% 0.18/0.34  % DateTime   : Tue Dec  1 18:14:15 EST 2020
% 0.18/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.56/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.56  
% 3.56/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.56  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.56/1.56  
% 3.56/1.56  %Foreground sorts:
% 3.56/1.56  
% 3.56/1.56  
% 3.56/1.56  %Background operators:
% 3.56/1.56  
% 3.56/1.56  
% 3.56/1.56  %Foreground operators:
% 3.56/1.56  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.56/1.56  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.56/1.56  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.56/1.56  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.56/1.56  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.56/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.56/1.56  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.56/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.56/1.56  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.56/1.56  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.56/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.56/1.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.56/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.56/1.56  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.56/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.56/1.56  tff('#skF_2', type, '#skF_2': $i).
% 3.56/1.56  tff('#skF_3', type, '#skF_3': $i).
% 3.56/1.56  tff('#skF_1', type, '#skF_1': $i).
% 3.56/1.56  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.56/1.56  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.56/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.56/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.56/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.56/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.56/1.56  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.56/1.56  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.56/1.56  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.56/1.56  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.56/1.56  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.56/1.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.56/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.56/1.56  
% 3.56/1.59  tff(f_224, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.56/1.59  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.56/1.59  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.56/1.59  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.56/1.59  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.56/1.59  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.56/1.59  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.56/1.59  tff(f_88, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.56/1.59  tff(f_99, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.56/1.59  tff(f_106, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.56/1.59  tff(f_82, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.56/1.59  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.56/1.59  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.56/1.59  tff(f_175, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.56/1.59  tff(c_70, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_56, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_161, plain, (![B_417, A_418]: (l1_pre_topc(B_417) | ~m1_pre_topc(B_417, A_418) | ~l1_pre_topc(A_418))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.56/1.59  tff(c_170, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_161])).
% 3.56/1.59  tff(c_177, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_170])).
% 3.56/1.59  tff(c_14, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.56/1.59  tff(c_58, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_98, plain, (![A_414]: (u1_struct_0(A_414)=k2_struct_0(A_414) | ~l1_struct_0(A_414))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.56/1.59  tff(c_102, plain, (![A_12]: (u1_struct_0(A_12)=k2_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_14, c_98])).
% 3.56/1.59  tff(c_185, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_177, c_102])).
% 3.56/1.59  tff(c_18, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.56/1.59  tff(c_216, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_185, c_18])).
% 3.56/1.59  tff(c_219, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_58, c_216])).
% 3.56/1.59  tff(c_222, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_219])).
% 3.56/1.59  tff(c_225, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_222])).
% 3.56/1.59  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_225])).
% 3.56/1.59  tff(c_230, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_219])).
% 3.56/1.59  tff(c_46, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_212, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_46])).
% 3.56/1.59  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.56/1.59  tff(c_72, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_243, plain, (![B_422, A_423]: (v2_pre_topc(B_422) | ~m1_pre_topc(B_422, A_423) | ~l1_pre_topc(A_423) | ~v2_pre_topc(A_423))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.56/1.59  tff(c_252, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_56, c_243])).
% 3.56/1.59  tff(c_259, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_252])).
% 3.56/1.59  tff(c_24, plain, (![A_20]: (v3_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.56/1.59  tff(c_28, plain, (![A_24]: (m1_pre_topc(A_24, A_24) | ~l1_pre_topc(A_24))), inference(cnfTransformation, [status(thm)], [f_99])).
% 3.56/1.59  tff(c_272, plain, (![B_429, A_430]: (r1_tarski(u1_struct_0(B_429), u1_struct_0(A_430)) | ~m1_pre_topc(B_429, A_430) | ~l1_pre_topc(A_430))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.56/1.59  tff(c_278, plain, (![B_429]: (r1_tarski(u1_struct_0(B_429), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_429, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_185, c_272])).
% 3.56/1.59  tff(c_305, plain, (![B_431]: (r1_tarski(u1_struct_0(B_431), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_431, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_177, c_278])).
% 3.56/1.59  tff(c_308, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_185, c_305])).
% 3.56/1.59  tff(c_449, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_308])).
% 3.56/1.59  tff(c_452, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_28, c_449])).
% 3.56/1.59  tff(c_456, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_452])).
% 3.56/1.59  tff(c_458, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_308])).
% 3.56/1.59  tff(c_60, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_167, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_60, c_161])).
% 3.56/1.59  tff(c_174, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_167])).
% 3.56/1.59  tff(c_181, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_174, c_102])).
% 3.56/1.59  tff(c_48, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_186, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_181, c_48])).
% 3.56/1.59  tff(c_601, plain, (![A_445, B_446]: (m1_pre_topc(A_445, B_446) | ~m1_pre_topc(A_445, g1_pre_topc(u1_struct_0(B_446), u1_pre_topc(B_446))) | ~l1_pre_topc(B_446) | ~l1_pre_topc(A_445))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.56/1.59  tff(c_610, plain, (![A_445]: (m1_pre_topc(A_445, '#skF_3') | ~m1_pre_topc(A_445, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_445))), inference(superposition, [status(thm), theory('equality')], [c_181, c_601])).
% 3.56/1.59  tff(c_631, plain, (![A_447]: (m1_pre_topc(A_447, '#skF_3') | ~m1_pre_topc(A_447, '#skF_4') | ~l1_pre_topc(A_447))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_186, c_610])).
% 3.56/1.59  tff(c_284, plain, (![B_429]: (r1_tarski(u1_struct_0(B_429), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_429, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_272])).
% 3.56/1.59  tff(c_318, plain, (![B_432]: (r1_tarski(u1_struct_0(B_432), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_432, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_284])).
% 3.56/1.59  tff(c_321, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_185, c_318])).
% 3.56/1.59  tff(c_434, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_321])).
% 3.56/1.59  tff(c_637, plain, (~m1_pre_topc('#skF_4', '#skF_4') | ~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_631, c_434])).
% 3.56/1.59  tff(c_657, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_177, c_458, c_637])).
% 3.56/1.59  tff(c_658, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_321])).
% 3.56/1.59  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.56/1.59  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.56/1.59  tff(c_77, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.56/1.59  tff(c_74, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_68, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_62, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_38, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_66, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_64, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_54, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_103, plain, (![A_415]: (u1_struct_0(A_415)=k2_struct_0(A_415) | ~l1_pre_topc(A_415))), inference(resolution, [status(thm)], [c_14, c_98])).
% 3.56/1.59  tff(c_111, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_64, c_103])).
% 3.56/1.59  tff(c_52, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_116, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_52])).
% 3.56/1.59  tff(c_232, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_116])).
% 3.56/1.59  tff(c_50, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_145, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_111, c_50])).
% 3.56/1.59  tff(c_211, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_145])).
% 3.56/1.59  tff(c_837, plain, (![A_454, B_455]: (m1_pre_topc(A_454, g1_pre_topc(u1_struct_0(B_455), u1_pre_topc(B_455))) | ~m1_pre_topc(A_454, B_455) | ~l1_pre_topc(B_455) | ~l1_pre_topc(A_454))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.56/1.59  tff(c_858, plain, (![A_454]: (m1_pre_topc(A_454, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_454, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_454))), inference(superposition, [status(thm), theory('equality')], [c_181, c_837])).
% 3.56/1.59  tff(c_880, plain, (![A_456]: (m1_pre_topc(A_456, '#skF_4') | ~m1_pre_topc(A_456, '#skF_3') | ~l1_pre_topc(A_456))), inference(demodulation, [status(thm), theory('equality')], [c_174, c_186, c_858])).
% 3.56/1.59  tff(c_897, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_28, c_880])).
% 3.56/1.59  tff(c_910, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_174, c_897])).
% 3.56/1.59  tff(c_42, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_44, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_75, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 3.56/1.59  tff(c_187, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_181, c_75])).
% 3.56/1.59  tff(c_40, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_224])).
% 3.56/1.59  tff(c_76, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_40])).
% 3.56/1.59  tff(c_1030, plain, (![B_473, H_476, A_472, F_474, C_477, D_478, E_475]: (r1_tmap_1(D_478, B_473, E_475, H_476) | ~r1_tmap_1(C_477, B_473, k3_tmap_1(A_472, B_473, D_478, C_477, E_475), H_476) | ~r1_tarski(F_474, u1_struct_0(C_477)) | ~r2_hidden(H_476, F_474) | ~v3_pre_topc(F_474, D_478) | ~m1_subset_1(H_476, u1_struct_0(C_477)) | ~m1_subset_1(H_476, u1_struct_0(D_478)) | ~m1_subset_1(F_474, k1_zfmisc_1(u1_struct_0(D_478))) | ~m1_pre_topc(C_477, D_478) | ~m1_subset_1(E_475, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_478), u1_struct_0(B_473)))) | ~v1_funct_2(E_475, u1_struct_0(D_478), u1_struct_0(B_473)) | ~v1_funct_1(E_475) | ~m1_pre_topc(D_478, A_472) | v2_struct_0(D_478) | ~m1_pre_topc(C_477, A_472) | v2_struct_0(C_477) | ~l1_pre_topc(B_473) | ~v2_pre_topc(B_473) | v2_struct_0(B_473) | ~l1_pre_topc(A_472) | ~v2_pre_topc(A_472) | v2_struct_0(A_472))), inference(cnfTransformation, [status(thm)], [f_175])).
% 3.56/1.59  tff(c_1032, plain, (![F_474]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_474, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_474) | ~v3_pre_topc(F_474, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_474, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_76, c_1030])).
% 3.56/1.59  tff(c_1035, plain, (![F_474]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_474, k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_474) | ~v3_pre_topc(F_474, '#skF_4') | ~m1_subset_1(F_474, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_70, c_66, c_64, c_60, c_56, c_54, c_232, c_111, c_185, c_211, c_111, c_185, c_910, c_185, c_212, c_185, c_187, c_181, c_181, c_1032])).
% 3.56/1.59  tff(c_1054, plain, (![F_481]: (~r1_tarski(F_481, k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_481) | ~v3_pre_topc(F_481, '#skF_4') | ~m1_subset_1(F_481, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_74, c_68, c_62, c_58, c_38, c_1035])).
% 3.56/1.59  tff(c_1064, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_77, c_1054])).
% 3.56/1.59  tff(c_1071, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_658, c_1064])).
% 3.56/1.59  tff(c_1073, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1071])).
% 3.56/1.59  tff(c_1076, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_1073])).
% 3.56/1.59  tff(c_1080, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_259, c_177, c_1076])).
% 3.56/1.59  tff(c_1081, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1071])).
% 3.56/1.59  tff(c_1085, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1081])).
% 3.56/1.59  tff(c_1088, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_212, c_1085])).
% 3.56/1.59  tff(c_1090, plain, $false, inference(negUnitSimplification, [status(thm)], [c_230, c_1088])).
% 3.56/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.56/1.59  
% 3.56/1.59  Inference rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Ref     : 0
% 3.56/1.59  #Sup     : 202
% 3.56/1.59  #Fact    : 0
% 3.56/1.59  #Define  : 0
% 3.56/1.59  #Split   : 20
% 3.56/1.59  #Chain   : 0
% 3.56/1.59  #Close   : 0
% 3.56/1.59  
% 3.56/1.59  Ordering : KBO
% 3.56/1.59  
% 3.56/1.59  Simplification rules
% 3.56/1.59  ----------------------
% 3.56/1.59  #Subsume      : 15
% 3.56/1.59  #Demod        : 199
% 3.56/1.59  #Tautology    : 69
% 3.56/1.59  #SimpNegUnit  : 11
% 3.56/1.59  #BackRed      : 5
% 3.56/1.59  
% 3.56/1.59  #Partial instantiations: 0
% 3.56/1.59  #Strategies tried      : 1
% 3.56/1.59  
% 3.56/1.59  Timing (in seconds)
% 3.56/1.59  ----------------------
% 3.56/1.59  Preprocessing        : 0.38
% 3.56/1.59  Parsing              : 0.19
% 3.56/1.59  CNF conversion       : 0.05
% 3.56/1.59  Main loop            : 0.44
% 3.56/1.59  Inferencing          : 0.15
% 3.56/1.59  Reduction            : 0.15
% 3.56/1.59  Demodulation         : 0.10
% 3.56/1.59  BG Simplification    : 0.02
% 3.56/1.59  Subsumption          : 0.08
% 3.56/1.59  Abstraction          : 0.02
% 3.56/1.59  MUC search           : 0.00
% 3.56/1.59  Cooper               : 0.00
% 3.56/1.59  Total                : 0.87
% 3.56/1.59  Index Insertion      : 0.00
% 3.56/1.59  Index Deletion       : 0.00
% 3.56/1.59  Index Matching       : 0.00
% 3.56/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------
