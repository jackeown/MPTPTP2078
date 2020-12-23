%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:40 EST 2020

% Result     : Theorem 5.13s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :  151 (1203 expanded)
%              Number of leaves         :   49 ( 440 expanded)
%              Depth                    :   17
%              Number of atoms          :  316 (5646 expanded)
%              Number of equality atoms :   15 ( 638 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_237,negated_conjecture,(
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

tff(f_59,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_52,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_48,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_67,axiom,(
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

tff(f_44,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_82,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_114,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_110,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_121,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_76,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_188,axiom,(
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

tff(f_101,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(u1_struct_0(A)))
         => ! [C] :
              ( m1_subset_1(C,u1_struct_0(A))
             => ( ( v3_pre_topc(B,A)
                  & r2_hidden(C,B) )
               => m1_connsp_2(B,A,C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_163,plain,(
    ! [B_421,A_422] :
      ( l1_pre_topc(B_421)
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_172,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_179,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_172])).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_100,plain,(
    ! [A_418] :
      ( u1_struct_0(A_418) = k2_struct_0(A_418)
      | ~ l1_struct_0(A_418) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_104,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_187,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_104])).

tff(c_16,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_218,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_16])).

tff(c_221,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_218])).

tff(c_224,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_227,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_227])).

tff(c_232,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_214,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_48])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_245,plain,(
    ! [B_426,A_427] :
      ( v2_pre_topc(B_426)
      | ~ m1_pre_topc(B_426,A_427)
      | ~ l1_pre_topc(A_427)
      | ~ v2_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_254,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_245])).

tff(c_261,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_254])).

tff(c_22,plain,(
    ! [A_17] :
      ( v3_pre_topc(k2_struct_0(A_17),A_17)
      | ~ l1_pre_topc(A_17)
      | ~ v2_pre_topc(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_169,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_163])).

tff(c_176,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_169])).

tff(c_30,plain,(
    ! [A_28] :
      ( m1_pre_topc(A_28,A_28)
      | ~ l1_pre_topc(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_183,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_104])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_188,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_50])).

tff(c_388,plain,(
    ! [B_437,A_438] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_437),u1_pre_topc(B_437)),A_438)
      | ~ m1_pre_topc(B_437,A_438)
      | ~ l1_pre_topc(A_438) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_402,plain,(
    ! [A_438] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_438)
      | ~ m1_pre_topc('#skF_3',A_438)
      | ~ l1_pre_topc(A_438) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_388])).

tff(c_413,plain,(
    ! [A_439] :
      ( m1_pre_topc('#skF_4',A_439)
      | ~ m1_pre_topc('#skF_3',A_439)
      | ~ l1_pre_topc(A_439) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_402])).

tff(c_417,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_413])).

tff(c_423,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_417])).

tff(c_262,plain,(
    ! [B_428,A_429] :
      ( r1_tarski(u1_struct_0(B_428),u1_struct_0(A_429))
      | ~ m1_pre_topc(B_428,A_429)
      | ~ l1_pre_topc(A_429) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_274,plain,(
    ! [B_428] :
      ( r1_tarski(u1_struct_0(B_428),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_428,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_262])).

tff(c_325,plain,(
    ! [B_432] :
      ( r1_tarski(u1_struct_0(B_432),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_432,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_274])).

tff(c_328,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_325])).

tff(c_446,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_328])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_79,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_76,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_105,plain,(
    ! [A_419] :
      ( u1_struct_0(A_419) = k2_struct_0(A_419)
      | ~ l1_pre_topc(A_419) ) ),
    inference(resolution,[status(thm)],[c_12,c_100])).

tff(c_113,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_105])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_118,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_54])).

tff(c_234,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_118])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_147,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_52])).

tff(c_213,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_147])).

tff(c_268,plain,(
    ! [B_428] :
      ( r1_tarski(u1_struct_0(B_428),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_428,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_262])).

tff(c_295,plain,(
    ! [B_430] :
      ( r1_tarski(u1_struct_0(B_430),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_430,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_268])).

tff(c_301,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_295])).

tff(c_493,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_301])).

tff(c_331,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_325])).

tff(c_523,plain,(
    ~ m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_331])).

tff(c_529,plain,(
    ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_523])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_529])).

tff(c_538,plain,(
    m1_pre_topc('#skF_3','#skF_3') ),
    inference(splitRight,[status(thm)],[c_331])).

tff(c_539,plain,(
    ! [A_444,B_445] :
      ( m1_pre_topc(A_444,g1_pre_topc(u1_struct_0(B_445),u1_pre_topc(B_445)))
      | ~ m1_pre_topc(A_444,B_445)
      | ~ l1_pre_topc(B_445)
      | ~ l1_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_559,plain,(
    ! [A_444] :
      ( m1_pre_topc(A_444,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_444,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_444) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_539])).

tff(c_607,plain,(
    ! [A_446] :
      ( m1_pre_topc(A_446,'#skF_4')
      | ~ m1_pre_topc(A_446,'#skF_3')
      | ~ l1_pre_topc(A_446) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_188,c_559])).

tff(c_610,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_538,c_607])).

tff(c_628,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_610])).

tff(c_630,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_493,c_628])).

tff(c_632,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_301])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_189,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_77])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_237])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_1272,plain,(
    ! [H_482,E_483,B_479,D_484,A_478,C_481,F_480] :
      ( r1_tmap_1(D_484,B_479,E_483,H_482)
      | ~ r1_tmap_1(C_481,B_479,k3_tmap_1(A_478,B_479,D_484,C_481,E_483),H_482)
      | ~ m1_connsp_2(F_480,D_484,H_482)
      | ~ r1_tarski(F_480,u1_struct_0(C_481))
      | ~ m1_subset_1(H_482,u1_struct_0(C_481))
      | ~ m1_subset_1(H_482,u1_struct_0(D_484))
      | ~ m1_subset_1(F_480,k1_zfmisc_1(u1_struct_0(D_484)))
      | ~ m1_pre_topc(C_481,D_484)
      | ~ m1_subset_1(E_483,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_484),u1_struct_0(B_479))))
      | ~ v1_funct_2(E_483,u1_struct_0(D_484),u1_struct_0(B_479))
      | ~ v1_funct_1(E_483)
      | ~ m1_pre_topc(D_484,A_478)
      | v2_struct_0(D_484)
      | ~ m1_pre_topc(C_481,A_478)
      | v2_struct_0(C_481)
      | ~ l1_pre_topc(B_479)
      | ~ v2_pre_topc(B_479)
      | v2_struct_0(B_479)
      | ~ l1_pre_topc(A_478)
      | ~ v2_pre_topc(A_478)
      | v2_struct_0(A_478) ) ),
    inference(cnfTransformation,[status(thm)],[f_188])).

tff(c_1274,plain,(
    ! [F_480] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_480,'#skF_4','#skF_6')
      | ~ r1_tarski(F_480,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_480,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_78,c_1272])).

tff(c_1277,plain,(
    ! [F_480] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_480,'#skF_4','#skF_6')
      | ~ r1_tarski(F_480,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(F_480,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_234,c_113,c_187,c_213,c_113,c_187,c_632,c_187,c_214,c_187,c_189,c_183,c_183,c_1274])).

tff(c_1359,plain,(
    ! [F_487] :
      ( ~ m1_connsp_2(F_487,'#skF_4','#skF_6')
      | ~ r1_tarski(F_487,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(F_487,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_1277])).

tff(c_1363,plain,
    ( ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_79,c_1359])).

tff(c_1366,plain,(
    ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_446,c_1363])).

tff(c_1003,plain,(
    ! [B_456,A_457,C_458] :
      ( m1_connsp_2(B_456,A_457,C_458)
      | ~ r2_hidden(C_458,B_456)
      | ~ v3_pre_topc(B_456,A_457)
      | ~ m1_subset_1(C_458,u1_struct_0(A_457))
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0(A_457)))
      | ~ l1_pre_topc(A_457)
      | ~ v2_pre_topc(A_457)
      | v2_struct_0(A_457) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1005,plain,(
    ! [B_456,C_458] :
      ( m1_connsp_2(B_456,'#skF_4',C_458)
      | ~ r2_hidden(C_458,B_456)
      | ~ v3_pre_topc(B_456,'#skF_4')
      | ~ m1_subset_1(C_458,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_456,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_1003])).

tff(c_1013,plain,(
    ! [B_456,C_458] :
      ( m1_connsp_2(B_456,'#skF_4',C_458)
      | ~ r2_hidden(C_458,B_456)
      | ~ v3_pre_topc(B_456,'#skF_4')
      | ~ m1_subset_1(C_458,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_456,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_179,c_187,c_1005])).

tff(c_1888,plain,(
    ! [B_499,C_500] :
      ( m1_connsp_2(B_499,'#skF_4',C_500)
      | ~ r2_hidden(C_500,B_499)
      | ~ v3_pre_topc(B_499,'#skF_4')
      | ~ m1_subset_1(C_500,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_499,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_1013])).

tff(c_3633,plain,(
    ! [B_535] :
      ( m1_connsp_2(B_535,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_535)
      | ~ v3_pre_topc(B_535,'#skF_4')
      | ~ m1_subset_1(B_535,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_214,c_1888])).

tff(c_3637,plain,
    ( m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_3633])).

tff(c_3640,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1366,c_3637])).

tff(c_3641,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_3640])).

tff(c_3644,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_3641])).

tff(c_3648,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_179,c_3644])).

tff(c_3649,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_3640])).

tff(c_3653,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_3649])).

tff(c_3656,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_3653])).

tff(c_3658,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_3656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:48:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.13/1.95  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.97  
% 5.13/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.13/1.97  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.13/1.97  
% 5.13/1.97  %Foreground sorts:
% 5.13/1.97  
% 5.13/1.97  
% 5.13/1.97  %Background operators:
% 5.13/1.97  
% 5.13/1.97  
% 5.13/1.97  %Foreground operators:
% 5.13/1.97  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.13/1.97  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.13/1.97  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.13/1.97  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.13/1.97  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.13/1.97  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.13/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.13/1.97  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.13/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.13/1.97  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.13/1.97  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.13/1.97  tff('#skF_7', type, '#skF_7': $i).
% 5.13/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.13/1.97  tff('#skF_5', type, '#skF_5': $i).
% 5.13/1.97  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.13/1.97  tff('#skF_6', type, '#skF_6': $i).
% 5.13/1.97  tff('#skF_2', type, '#skF_2': $i).
% 5.13/1.97  tff('#skF_3', type, '#skF_3': $i).
% 5.13/1.97  tff('#skF_1', type, '#skF_1': $i).
% 5.13/1.97  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.13/1.97  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.13/1.97  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.13/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.13/1.97  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.13/1.97  tff('#skF_4', type, '#skF_4': $i).
% 5.13/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.13/1.97  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.13/1.97  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.13/1.97  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.13/1.97  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.13/1.97  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.13/1.97  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.13/1.97  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.13/1.97  
% 5.46/2.00  tff(f_237, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.46/2.00  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.46/2.00  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.46/2.00  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.46/2.00  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.46/2.00  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.46/2.00  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.46/2.00  tff(f_82, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.46/2.00  tff(f_114, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.46/2.00  tff(f_110, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 5.46/2.00  tff(f_121, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 5.46/2.00  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 5.46/2.00  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.46/2.00  tff(f_76, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.46/2.00  tff(f_188, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 5.46/2.00  tff(f_101, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.46/2.00  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_163, plain, (![B_421, A_422]: (l1_pre_topc(B_421) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.46/2.00  tff(c_172, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_163])).
% 5.46/2.00  tff(c_179, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_172])).
% 5.46/2.00  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.46/2.00  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_100, plain, (![A_418]: (u1_struct_0(A_418)=k2_struct_0(A_418) | ~l1_struct_0(A_418))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.46/2.00  tff(c_104, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_12, c_100])).
% 5.46/2.00  tff(c_187, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_179, c_104])).
% 5.46/2.00  tff(c_16, plain, (![A_13]: (~v1_xboole_0(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.46/2.00  tff(c_218, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_187, c_16])).
% 5.46/2.00  tff(c_221, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_218])).
% 5.46/2.00  tff(c_224, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_221])).
% 5.46/2.00  tff(c_227, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_224])).
% 5.46/2.00  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_227])).
% 5.46/2.00  tff(c_232, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_221])).
% 5.46/2.00  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_214, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_48])).
% 5.46/2.00  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.46/2.00  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_245, plain, (![B_426, A_427]: (v2_pre_topc(B_426) | ~m1_pre_topc(B_426, A_427) | ~l1_pre_topc(A_427) | ~v2_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_44])).
% 5.46/2.00  tff(c_254, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_245])).
% 5.46/2.00  tff(c_261, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_254])).
% 5.46/2.00  tff(c_22, plain, (![A_17]: (v3_pre_topc(k2_struct_0(A_17), A_17) | ~l1_pre_topc(A_17) | ~v2_pre_topc(A_17))), inference(cnfTransformation, [status(thm)], [f_82])).
% 5.46/2.00  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_169, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_163])).
% 5.46/2.00  tff(c_176, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_169])).
% 5.46/2.00  tff(c_30, plain, (![A_28]: (m1_pre_topc(A_28, A_28) | ~l1_pre_topc(A_28))), inference(cnfTransformation, [status(thm)], [f_114])).
% 5.46/2.00  tff(c_183, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_176, c_104])).
% 5.46/2.00  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_188, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_50])).
% 5.46/2.00  tff(c_388, plain, (![B_437, A_438]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_437), u1_pre_topc(B_437)), A_438) | ~m1_pre_topc(B_437, A_438) | ~l1_pre_topc(A_438))), inference(cnfTransformation, [status(thm)], [f_110])).
% 5.46/2.00  tff(c_402, plain, (![A_438]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_438) | ~m1_pre_topc('#skF_3', A_438) | ~l1_pre_topc(A_438))), inference(superposition, [status(thm), theory('equality')], [c_183, c_388])).
% 5.46/2.00  tff(c_413, plain, (![A_439]: (m1_pre_topc('#skF_4', A_439) | ~m1_pre_topc('#skF_3', A_439) | ~l1_pre_topc(A_439))), inference(demodulation, [status(thm), theory('equality')], [c_188, c_402])).
% 5.46/2.00  tff(c_417, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_413])).
% 5.46/2.00  tff(c_423, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_417])).
% 5.46/2.00  tff(c_262, plain, (![B_428, A_429]: (r1_tarski(u1_struct_0(B_428), u1_struct_0(A_429)) | ~m1_pre_topc(B_428, A_429) | ~l1_pre_topc(A_429))), inference(cnfTransformation, [status(thm)], [f_121])).
% 5.46/2.00  tff(c_274, plain, (![B_428]: (r1_tarski(u1_struct_0(B_428), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_428, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_262])).
% 5.46/2.00  tff(c_325, plain, (![B_432]: (r1_tarski(u1_struct_0(B_432), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_432, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_274])).
% 5.46/2.00  tff(c_328, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_187, c_325])).
% 5.46/2.00  tff(c_446, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_423, c_328])).
% 5.46/2.00  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.46/2.00  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.46/2.00  tff(c_79, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 5.46/2.00  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_105, plain, (![A_419]: (u1_struct_0(A_419)=k2_struct_0(A_419) | ~l1_pre_topc(A_419))), inference(resolution, [status(thm)], [c_12, c_100])).
% 5.46/2.00  tff(c_113, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_105])).
% 5.46/2.00  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_118, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_54])).
% 5.46/2.00  tff(c_234, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_118])).
% 5.46/2.00  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_147, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_52])).
% 5.46/2.00  tff(c_213, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_147])).
% 5.46/2.00  tff(c_268, plain, (![B_428]: (r1_tarski(u1_struct_0(B_428), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_428, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_262])).
% 5.46/2.00  tff(c_295, plain, (![B_430]: (r1_tarski(u1_struct_0(B_430), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_430, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_268])).
% 5.46/2.00  tff(c_301, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_183, c_295])).
% 5.46/2.00  tff(c_493, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_301])).
% 5.46/2.00  tff(c_331, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_3', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_325])).
% 5.46/2.00  tff(c_523, plain, (~m1_pre_topc('#skF_3', '#skF_3')), inference(splitLeft, [status(thm)], [c_331])).
% 5.46/2.00  tff(c_529, plain, (~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_523])).
% 5.46/2.00  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_176, c_529])).
% 5.46/2.00  tff(c_538, plain, (m1_pre_topc('#skF_3', '#skF_3')), inference(splitRight, [status(thm)], [c_331])).
% 5.46/2.00  tff(c_539, plain, (![A_444, B_445]: (m1_pre_topc(A_444, g1_pre_topc(u1_struct_0(B_445), u1_pre_topc(B_445))) | ~m1_pre_topc(A_444, B_445) | ~l1_pre_topc(B_445) | ~l1_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.46/2.00  tff(c_559, plain, (![A_444]: (m1_pre_topc(A_444, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_444, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_444))), inference(superposition, [status(thm), theory('equality')], [c_183, c_539])).
% 5.46/2.00  tff(c_607, plain, (![A_446]: (m1_pre_topc(A_446, '#skF_4') | ~m1_pre_topc(A_446, '#skF_3') | ~l1_pre_topc(A_446))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_188, c_559])).
% 5.46/2.00  tff(c_610, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_538, c_607])).
% 5.46/2.00  tff(c_628, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_610])).
% 5.46/2.00  tff(c_630, plain, $false, inference(negUnitSimplification, [status(thm)], [c_493, c_628])).
% 5.46/2.00  tff(c_632, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_301])).
% 5.46/2.00  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 5.46/2.00  tff(c_189, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_77])).
% 5.46/2.00  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_237])).
% 5.46/2.00  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 5.46/2.00  tff(c_1272, plain, (![H_482, E_483, B_479, D_484, A_478, C_481, F_480]: (r1_tmap_1(D_484, B_479, E_483, H_482) | ~r1_tmap_1(C_481, B_479, k3_tmap_1(A_478, B_479, D_484, C_481, E_483), H_482) | ~m1_connsp_2(F_480, D_484, H_482) | ~r1_tarski(F_480, u1_struct_0(C_481)) | ~m1_subset_1(H_482, u1_struct_0(C_481)) | ~m1_subset_1(H_482, u1_struct_0(D_484)) | ~m1_subset_1(F_480, k1_zfmisc_1(u1_struct_0(D_484))) | ~m1_pre_topc(C_481, D_484) | ~m1_subset_1(E_483, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_484), u1_struct_0(B_479)))) | ~v1_funct_2(E_483, u1_struct_0(D_484), u1_struct_0(B_479)) | ~v1_funct_1(E_483) | ~m1_pre_topc(D_484, A_478) | v2_struct_0(D_484) | ~m1_pre_topc(C_481, A_478) | v2_struct_0(C_481) | ~l1_pre_topc(B_479) | ~v2_pre_topc(B_479) | v2_struct_0(B_479) | ~l1_pre_topc(A_478) | ~v2_pre_topc(A_478) | v2_struct_0(A_478))), inference(cnfTransformation, [status(thm)], [f_188])).
% 5.46/2.00  tff(c_1274, plain, (![F_480]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_480, '#skF_4', '#skF_6') | ~r1_tarski(F_480, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_480, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_1272])).
% 5.46/2.00  tff(c_1277, plain, (![F_480]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_480, '#skF_4', '#skF_6') | ~r1_tarski(F_480, k2_struct_0('#skF_3')) | ~m1_subset_1(F_480, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_234, c_113, c_187, c_213, c_113, c_187, c_632, c_187, c_214, c_187, c_189, c_183, c_183, c_1274])).
% 5.46/2.00  tff(c_1359, plain, (![F_487]: (~m1_connsp_2(F_487, '#skF_4', '#skF_6') | ~r1_tarski(F_487, k2_struct_0('#skF_3')) | ~m1_subset_1(F_487, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_1277])).
% 5.46/2.00  tff(c_1363, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_79, c_1359])).
% 5.46/2.00  tff(c_1366, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_446, c_1363])).
% 5.46/2.00  tff(c_1003, plain, (![B_456, A_457, C_458]: (m1_connsp_2(B_456, A_457, C_458) | ~r2_hidden(C_458, B_456) | ~v3_pre_topc(B_456, A_457) | ~m1_subset_1(C_458, u1_struct_0(A_457)) | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0(A_457))) | ~l1_pre_topc(A_457) | ~v2_pre_topc(A_457) | v2_struct_0(A_457))), inference(cnfTransformation, [status(thm)], [f_101])).
% 5.46/2.00  tff(c_1005, plain, (![B_456, C_458]: (m1_connsp_2(B_456, '#skF_4', C_458) | ~r2_hidden(C_458, B_456) | ~v3_pre_topc(B_456, '#skF_4') | ~m1_subset_1(C_458, k2_struct_0('#skF_4')) | ~m1_subset_1(B_456, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_1003])).
% 5.46/2.00  tff(c_1013, plain, (![B_456, C_458]: (m1_connsp_2(B_456, '#skF_4', C_458) | ~r2_hidden(C_458, B_456) | ~v3_pre_topc(B_456, '#skF_4') | ~m1_subset_1(C_458, k2_struct_0('#skF_4')) | ~m1_subset_1(B_456, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_179, c_187, c_1005])).
% 5.46/2.00  tff(c_1888, plain, (![B_499, C_500]: (m1_connsp_2(B_499, '#skF_4', C_500) | ~r2_hidden(C_500, B_499) | ~v3_pre_topc(B_499, '#skF_4') | ~m1_subset_1(C_500, k2_struct_0('#skF_4')) | ~m1_subset_1(B_499, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_1013])).
% 5.46/2.00  tff(c_3633, plain, (![B_535]: (m1_connsp_2(B_535, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_535) | ~v3_pre_topc(B_535, '#skF_4') | ~m1_subset_1(B_535, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_214, c_1888])).
% 5.46/2.00  tff(c_3637, plain, (m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_79, c_3633])).
% 5.46/2.00  tff(c_3640, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1366, c_3637])).
% 5.46/2.00  tff(c_3641, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_3640])).
% 5.46/2.00  tff(c_3644, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_22, c_3641])).
% 5.46/2.00  tff(c_3648, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_179, c_3644])).
% 5.46/2.00  tff(c_3649, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_3640])).
% 5.46/2.00  tff(c_3653, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_3649])).
% 5.46/2.00  tff(c_3656, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_3653])).
% 5.46/2.00  tff(c_3658, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_3656])).
% 5.46/2.00  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.46/2.00  
% 5.46/2.00  Inference rules
% 5.46/2.00  ----------------------
% 5.46/2.00  #Ref     : 0
% 5.46/2.00  #Sup     : 709
% 5.46/2.00  #Fact    : 0
% 5.46/2.00  #Define  : 0
% 5.46/2.00  #Split   : 19
% 5.46/2.00  #Chain   : 0
% 5.46/2.00  #Close   : 0
% 5.46/2.00  
% 5.46/2.00  Ordering : KBO
% 5.46/2.00  
% 5.46/2.00  Simplification rules
% 5.46/2.00  ----------------------
% 5.46/2.00  #Subsume      : 115
% 5.46/2.00  #Demod        : 1098
% 5.46/2.00  #Tautology    : 225
% 5.46/2.00  #SimpNegUnit  : 15
% 5.46/2.00  #BackRed      : 6
% 5.46/2.00  
% 5.46/2.00  #Partial instantiations: 0
% 5.46/2.00  #Strategies tried      : 1
% 5.46/2.00  
% 5.46/2.00  Timing (in seconds)
% 5.46/2.00  ----------------------
% 5.46/2.00  Preprocessing        : 0.39
% 5.46/2.00  Parsing              : 0.20
% 5.46/2.00  CNF conversion       : 0.05
% 5.46/2.00  Main loop            : 0.82
% 5.46/2.00  Inferencing          : 0.26
% 5.46/2.00  Reduction            : 0.32
% 5.46/2.00  Demodulation         : 0.24
% 5.46/2.00  BG Simplification    : 0.03
% 5.46/2.00  Subsumption          : 0.15
% 5.46/2.00  Abstraction          : 0.03
% 5.46/2.00  MUC search           : 0.00
% 5.46/2.00  Cooper               : 0.00
% 5.46/2.00  Total                : 1.27
% 5.46/2.00  Index Insertion      : 0.00
% 5.46/2.00  Index Deletion       : 0.00
% 5.46/2.00  Index Matching       : 0.00
% 5.46/2.00  BG Taut test         : 0.00
%------------------------------------------------------------------------------
