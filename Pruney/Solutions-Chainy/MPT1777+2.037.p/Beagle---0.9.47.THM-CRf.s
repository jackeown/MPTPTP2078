%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:37 EST 2020

% Result     : Theorem 5.97s
% Output     : CNFRefutation 5.97s
% Verified   : 
% Statistics : Number of formulae       :  149 (2409 expanded)
%              Number of leaves         :   48 ( 839 expanded)
%              Depth                    :   22
%              Number of atoms          :  322 (10755 expanded)
%              Number of equality atoms :   18 (1218 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_struct_0,type,(
    k2_struct_0: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_249,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_64,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_60,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_79,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_94,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_129,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => m1_subset_1(u1_struct_0(B),k1_zfmisc_1(u1_struct_0(A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_133,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_88,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_122,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => ( v1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)))
            & m1_pre_topc(g1_pre_topc(u1_struct_0(B),u1_pre_topc(B)),A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tmap_1)).

tff(f_200,axiom,(
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

tff(f_113,axiom,(
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

tff(c_80,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_66,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_167,plain,(
    ! [B_427,A_428] :
      ( l1_pre_topc(B_427)
      | ~ m1_pre_topc(B_427,A_428)
      | ~ l1_pre_topc(A_428) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_173,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_167])).

tff(c_180,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_173])).

tff(c_20,plain,(
    ! [A_14] :
      ( l1_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_68,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_99,plain,(
    ! [A_422] :
      ( u1_struct_0(A_422) = k2_struct_0(A_422)
      | ~ l1_struct_0(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    ! [A_14] :
      ( u1_struct_0(A_14) = k2_struct_0(A_14)
      | ~ l1_pre_topc(A_14) ) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_187,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_180,c_103])).

tff(c_24,plain,(
    ! [A_18] :
      ( ~ v1_xboole_0(u1_struct_0(A_18))
      | ~ l1_struct_0(A_18)
      | v2_struct_0(A_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_198,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_24])).

tff(c_201,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_198])).

tff(c_213,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_201])).

tff(c_221,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_213])).

tff(c_225,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_221])).

tff(c_226,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_201])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_194,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_56])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_82,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_275,plain,(
    ! [B_438,A_439] :
      ( v2_pre_topc(B_438)
      | ~ m1_pre_topc(B_438,A_439)
      | ~ l1_pre_topc(A_439)
      | ~ v2_pre_topc(A_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_281,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_275])).

tff(c_288,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_281])).

tff(c_30,plain,(
    ! [A_22] :
      ( v3_pre_topc(k2_struct_0(A_22),A_22)
      | ~ l1_pre_topc(A_22)
      | ~ v2_pre_topc(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_176,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_167])).

tff(c_183,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_176])).

tff(c_191,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_183,c_103])).

tff(c_299,plain,(
    ! [B_443,A_444] :
      ( m1_subset_1(u1_struct_0(B_443),k1_zfmisc_1(u1_struct_0(A_444)))
      | ~ m1_pre_topc(B_443,A_444)
      | ~ l1_pre_topc(A_444) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_316,plain,(
    ! [B_443] :
      ( m1_subset_1(u1_struct_0(B_443),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_443,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_299])).

tff(c_343,plain,(
    ! [B_448] :
      ( m1_subset_1(u1_struct_0(B_448),k1_zfmisc_1(k2_struct_0('#skF_4')))
      | ~ m1_pre_topc(B_448,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_316])).

tff(c_10,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_363,plain,(
    ! [B_449] :
      ( r1_tarski(u1_struct_0(B_449),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_449,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_343,c_10])).

tff(c_368,plain,
    ( r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_363])).

tff(c_382,plain,(
    ~ m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_368])).

tff(c_40,plain,(
    ! [A_36] :
      ( m1_pre_topc(A_36,A_36)
      | ~ l1_pre_topc(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_58,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_203,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_58])).

tff(c_823,plain,(
    ! [A_474,B_475] :
      ( m1_pre_topc(A_474,g1_pre_topc(u1_struct_0(B_475),u1_pre_topc(B_475)))
      | ~ m1_pre_topc(A_474,B_475)
      | ~ l1_pre_topc(B_475)
      | ~ l1_pre_topc(A_474) ) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_847,plain,(
    ! [A_474] :
      ( m1_pre_topc(A_474,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_474,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_474) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_823])).

tff(c_876,plain,(
    ! [A_476] :
      ( m1_pre_topc(A_476,'#skF_4')
      | ~ m1_pre_topc(A_476,'#skF_3')
      | ~ l1_pre_topc(A_476) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_203,c_847])).

tff(c_894,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_876])).

tff(c_908,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_894])).

tff(c_910,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_908])).

tff(c_911,plain,(
    r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_1048,plain,(
    ! [B_481,A_482] :
      ( m1_pre_topc(g1_pre_topc(u1_struct_0(B_481),u1_pre_topc(B_481)),A_482)
      | ~ m1_pre_topc(B_481,A_482)
      | ~ l1_pre_topc(A_482) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_1059,plain,(
    ! [A_482] :
      ( m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')),A_482)
      | ~ m1_pre_topc('#skF_3',A_482)
      | ~ l1_pre_topc(A_482) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_1048])).

tff(c_1073,plain,(
    ! [A_483] :
      ( m1_pre_topc('#skF_4',A_483)
      | ~ m1_pre_topc('#skF_3',A_483)
      | ~ l1_pre_topc(A_483) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_1059])).

tff(c_1080,plain,
    ( m1_pre_topc('#skF_4','#skF_3')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_1073])).

tff(c_1089,plain,(
    m1_pre_topc('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_1080])).

tff(c_310,plain,(
    ! [B_443] :
      ( m1_subset_1(u1_struct_0(B_443),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_443,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_299])).

tff(c_1227,plain,(
    ! [B_494] :
      ( m1_subset_1(u1_struct_0(B_494),k1_zfmisc_1(k2_struct_0('#skF_3')))
      | ~ m1_pre_topc(B_494,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_310])).

tff(c_1238,plain,
    ( m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3')))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_1227])).

tff(c_1248,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_1238])).

tff(c_1255,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_1248,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1257,plain,
    ( k2_struct_0('#skF_3') = k2_struct_0('#skF_4')
    | ~ r1_tarski(k2_struct_0('#skF_3'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1255,c_2])).

tff(c_1260,plain,(
    k2_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_911,c_1257])).

tff(c_1262,plain,(
    m1_subset_1(k2_struct_0('#skF_4'),k1_zfmisc_1(k2_struct_0('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_1248])).

tff(c_84,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_78,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_48,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_76,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_74,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_64,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_104,plain,(
    ! [A_423] :
      ( u1_struct_0(A_423) = k2_struct_0(A_423)
      | ~ l1_pre_topc(A_423) ) ),
    inference(resolution,[status(thm)],[c_20,c_99])).

tff(c_112,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_74,c_104])).

tff(c_62,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_117,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_62])).

tff(c_193,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_117])).

tff(c_60,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_142,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_112,c_60])).

tff(c_192,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_142])).

tff(c_912,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(splitRight,[status(thm)],[c_368])).

tff(c_1272,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1260,c_191])).

tff(c_52,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_50,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_249])).

tff(c_86,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_50])).

tff(c_1690,plain,(
    ! [D_522,B_527,F_521,H_524,C_526,A_525,E_523] :
      ( r1_tmap_1(D_522,B_527,E_523,H_524)
      | ~ r1_tmap_1(C_526,B_527,k3_tmap_1(A_525,B_527,D_522,C_526,E_523),H_524)
      | ~ m1_connsp_2(F_521,D_522,H_524)
      | ~ r1_tarski(F_521,u1_struct_0(C_526))
      | ~ m1_subset_1(H_524,u1_struct_0(C_526))
      | ~ m1_subset_1(H_524,u1_struct_0(D_522))
      | ~ m1_subset_1(F_521,k1_zfmisc_1(u1_struct_0(D_522)))
      | ~ m1_pre_topc(C_526,D_522)
      | ~ m1_subset_1(E_523,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_522),u1_struct_0(B_527))))
      | ~ v1_funct_2(E_523,u1_struct_0(D_522),u1_struct_0(B_527))
      | ~ v1_funct_1(E_523)
      | ~ m1_pre_topc(D_522,A_525)
      | v2_struct_0(D_522)
      | ~ m1_pre_topc(C_526,A_525)
      | v2_struct_0(C_526)
      | ~ l1_pre_topc(B_527)
      | ~ v2_pre_topc(B_527)
      | v2_struct_0(B_527)
      | ~ l1_pre_topc(A_525)
      | ~ v2_pre_topc(A_525)
      | v2_struct_0(A_525) ) ),
    inference(cnfTransformation,[status(thm)],[f_200])).

tff(c_1692,plain,(
    ! [F_521] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_521,'#skF_4','#skF_6')
      | ~ r1_tarski(F_521,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_521,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_86,c_1690])).

tff(c_1695,plain,(
    ! [F_521] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_521,'#skF_4','#skF_6')
      | ~ r1_tarski(F_521,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(F_521,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_80,c_76,c_74,c_70,c_66,c_64,c_193,c_112,c_187,c_192,c_112,c_187,c_912,c_187,c_194,c_187,c_194,c_1272,c_1272,c_1692])).

tff(c_1700,plain,(
    ! [F_528] :
      ( ~ m1_connsp_2(F_528,'#skF_4','#skF_6')
      | ~ r1_tarski(F_528,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(F_528,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_84,c_78,c_72,c_68,c_48,c_1695])).

tff(c_1703,plain,
    ( ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_1262,c_1700])).

tff(c_1713,plain,(
    ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1703])).

tff(c_1601,plain,(
    ! [B_506,A_507,C_508] :
      ( m1_connsp_2(B_506,A_507,C_508)
      | ~ r2_hidden(C_508,B_506)
      | ~ v3_pre_topc(B_506,A_507)
      | ~ m1_subset_1(C_508,u1_struct_0(A_507))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(u1_struct_0(A_507)))
      | ~ l1_pre_topc(A_507)
      | ~ v2_pre_topc(A_507)
      | v2_struct_0(A_507) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_1605,plain,(
    ! [B_506,C_508] :
      ( m1_connsp_2(B_506,'#skF_4',C_508)
      | ~ r2_hidden(C_508,B_506)
      | ~ v3_pre_topc(B_506,'#skF_4')
      | ~ m1_subset_1(C_508,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_1601])).

tff(c_1614,plain,(
    ! [B_506,C_508] :
      ( m1_connsp_2(B_506,'#skF_4',C_508)
      | ~ r2_hidden(C_508,B_506)
      | ~ v3_pre_topc(B_506,'#skF_4')
      | ~ m1_subset_1(C_508,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_506,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_180,c_187,c_1605])).

tff(c_1824,plain,(
    ! [B_535,C_536] :
      ( m1_connsp_2(B_535,'#skF_4',C_536)
      | ~ r2_hidden(C_536,B_535)
      | ~ v3_pre_topc(B_535,'#skF_4')
      | ~ m1_subset_1(C_536,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_535,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_1614])).

tff(c_4613,plain,(
    ! [B_611] :
      ( m1_connsp_2(B_611,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_611)
      | ~ v3_pre_topc(B_611,'#skF_4')
      | ~ m1_subset_1(B_611,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_194,c_1824])).

tff(c_4619,plain,
    ( m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_1262,c_4613])).

tff(c_4630,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1713,c_4619])).

tff(c_4633,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_4630])).

tff(c_4636,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_4633])).

tff(c_4640,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_288,c_180,c_4636])).

tff(c_4641,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_4630])).

tff(c_4645,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_8,c_4641])).

tff(c_4648,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_194,c_4645])).

tff(c_4650,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_226,c_4648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n006.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:25:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.97/2.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.18  
% 5.97/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.18  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_pre_topc > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 5.97/2.18  
% 5.97/2.18  %Foreground sorts:
% 5.97/2.18  
% 5.97/2.18  
% 5.97/2.18  %Background operators:
% 5.97/2.18  
% 5.97/2.18  
% 5.97/2.18  %Foreground operators:
% 5.97/2.18  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 5.97/2.18  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 5.97/2.18  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 5.97/2.18  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 5.97/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.97/2.18  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 5.97/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.97/2.18  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 5.97/2.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.97/2.18  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 5.97/2.18  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 5.97/2.18  tff('#skF_7', type, '#skF_7': $i).
% 5.97/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.97/2.18  tff('#skF_5', type, '#skF_5': $i).
% 5.97/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.97/2.18  tff('#skF_6', type, '#skF_6': $i).
% 5.97/2.18  tff('#skF_2', type, '#skF_2': $i).
% 5.97/2.18  tff('#skF_3', type, '#skF_3': $i).
% 5.97/2.18  tff('#skF_1', type, '#skF_1': $i).
% 5.97/2.18  tff(v1_pre_topc, type, v1_pre_topc: $i > $o).
% 5.97/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.97/2.18  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 5.97/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.97/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.97/2.18  tff('#skF_4', type, '#skF_4': $i).
% 5.97/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.97/2.18  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 5.97/2.18  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 5.97/2.18  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 5.97/2.18  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 5.97/2.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 5.97/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.97/2.18  
% 5.97/2.21  tff(f_249, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 5.97/2.21  tff(f_71, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 5.97/2.21  tff(f_64, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 5.97/2.21  tff(f_60, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 5.97/2.21  tff(f_79, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 5.97/2.21  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 5.97/2.21  tff(f_56, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 5.97/2.21  tff(f_94, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 5.97/2.21  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.97/2.21  tff(f_129, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => m1_subset_1(u1_struct_0(B), k1_zfmisc_1(u1_struct_0(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tsep_1)).
% 5.97/2.21  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.97/2.21  tff(f_133, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 5.97/2.21  tff(f_88, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 5.97/2.21  tff(f_122, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => (v1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B))) & m1_pre_topc(g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)), A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_tmap_1)).
% 5.97/2.21  tff(f_200, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_tmap_1)).
% 5.97/2.21  tff(f_113, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_connsp_2)).
% 5.97/2.21  tff(c_80, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_66, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_167, plain, (![B_427, A_428]: (l1_pre_topc(B_427) | ~m1_pre_topc(B_427, A_428) | ~l1_pre_topc(A_428))), inference(cnfTransformation, [status(thm)], [f_71])).
% 5.97/2.21  tff(c_173, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_167])).
% 5.97/2.21  tff(c_180, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_173])).
% 5.97/2.21  tff(c_20, plain, (![A_14]: (l1_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.97/2.21  tff(c_68, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_99, plain, (![A_422]: (u1_struct_0(A_422)=k2_struct_0(A_422) | ~l1_struct_0(A_422))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.97/2.21  tff(c_103, plain, (![A_14]: (u1_struct_0(A_14)=k2_struct_0(A_14) | ~l1_pre_topc(A_14))), inference(resolution, [status(thm)], [c_20, c_99])).
% 5.97/2.21  tff(c_187, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_180, c_103])).
% 5.97/2.21  tff(c_24, plain, (![A_18]: (~v1_xboole_0(u1_struct_0(A_18)) | ~l1_struct_0(A_18) | v2_struct_0(A_18))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.97/2.21  tff(c_198, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_187, c_24])).
% 5.97/2.21  tff(c_201, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_68, c_198])).
% 5.97/2.21  tff(c_213, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_201])).
% 5.97/2.21  tff(c_221, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_20, c_213])).
% 5.97/2.21  tff(c_225, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_221])).
% 5.97/2.21  tff(c_226, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_201])).
% 5.97/2.21  tff(c_56, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_194, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_56])).
% 5.97/2.21  tff(c_8, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.97/2.21  tff(c_82, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_275, plain, (![B_438, A_439]: (v2_pre_topc(B_438) | ~m1_pre_topc(B_438, A_439) | ~l1_pre_topc(A_439) | ~v2_pre_topc(A_439))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.97/2.21  tff(c_281, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_66, c_275])).
% 5.97/2.21  tff(c_288, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_281])).
% 5.97/2.21  tff(c_30, plain, (![A_22]: (v3_pre_topc(k2_struct_0(A_22), A_22) | ~l1_pre_topc(A_22) | ~v2_pre_topc(A_22))), inference(cnfTransformation, [status(thm)], [f_94])).
% 5.97/2.21  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.21  tff(c_70, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_176, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_70, c_167])).
% 5.97/2.21  tff(c_183, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80, c_176])).
% 5.97/2.21  tff(c_191, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_183, c_103])).
% 5.97/2.21  tff(c_299, plain, (![B_443, A_444]: (m1_subset_1(u1_struct_0(B_443), k1_zfmisc_1(u1_struct_0(A_444))) | ~m1_pre_topc(B_443, A_444) | ~l1_pre_topc(A_444))), inference(cnfTransformation, [status(thm)], [f_129])).
% 5.97/2.21  tff(c_316, plain, (![B_443]: (m1_subset_1(u1_struct_0(B_443), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_443, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_299])).
% 5.97/2.21  tff(c_343, plain, (![B_448]: (m1_subset_1(u1_struct_0(B_448), k1_zfmisc_1(k2_struct_0('#skF_4'))) | ~m1_pre_topc(B_448, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_316])).
% 5.97/2.21  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.97/2.21  tff(c_363, plain, (![B_449]: (r1_tarski(u1_struct_0(B_449), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_449, '#skF_4'))), inference(resolution, [status(thm)], [c_343, c_10])).
% 5.97/2.21  tff(c_368, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_191, c_363])).
% 5.97/2.21  tff(c_382, plain, (~m1_pre_topc('#skF_3', '#skF_4')), inference(splitLeft, [status(thm)], [c_368])).
% 5.97/2.21  tff(c_40, plain, (![A_36]: (m1_pre_topc(A_36, A_36) | ~l1_pre_topc(A_36))), inference(cnfTransformation, [status(thm)], [f_133])).
% 5.97/2.21  tff(c_58, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_203, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_191, c_58])).
% 5.97/2.21  tff(c_823, plain, (![A_474, B_475]: (m1_pre_topc(A_474, g1_pre_topc(u1_struct_0(B_475), u1_pre_topc(B_475))) | ~m1_pre_topc(A_474, B_475) | ~l1_pre_topc(B_475) | ~l1_pre_topc(A_474))), inference(cnfTransformation, [status(thm)], [f_88])).
% 5.97/2.21  tff(c_847, plain, (![A_474]: (m1_pre_topc(A_474, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_474, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_474))), inference(superposition, [status(thm), theory('equality')], [c_191, c_823])).
% 5.97/2.21  tff(c_876, plain, (![A_476]: (m1_pre_topc(A_476, '#skF_4') | ~m1_pre_topc(A_476, '#skF_3') | ~l1_pre_topc(A_476))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_203, c_847])).
% 5.97/2.21  tff(c_894, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_876])).
% 5.97/2.21  tff(c_908, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_894])).
% 5.97/2.21  tff(c_910, plain, $false, inference(negUnitSimplification, [status(thm)], [c_382, c_908])).
% 5.97/2.21  tff(c_911, plain, (r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_368])).
% 5.97/2.21  tff(c_1048, plain, (![B_481, A_482]: (m1_pre_topc(g1_pre_topc(u1_struct_0(B_481), u1_pre_topc(B_481)), A_482) | ~m1_pre_topc(B_481, A_482) | ~l1_pre_topc(A_482))), inference(cnfTransformation, [status(thm)], [f_122])).
% 5.97/2.21  tff(c_1059, plain, (![A_482]: (m1_pre_topc(g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3')), A_482) | ~m1_pre_topc('#skF_3', A_482) | ~l1_pre_topc(A_482))), inference(superposition, [status(thm), theory('equality')], [c_191, c_1048])).
% 5.97/2.21  tff(c_1073, plain, (![A_483]: (m1_pre_topc('#skF_4', A_483) | ~m1_pre_topc('#skF_3', A_483) | ~l1_pre_topc(A_483))), inference(demodulation, [status(thm), theory('equality')], [c_203, c_1059])).
% 5.97/2.21  tff(c_1080, plain, (m1_pre_topc('#skF_4', '#skF_3') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_40, c_1073])).
% 5.97/2.21  tff(c_1089, plain, (m1_pre_topc('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_183, c_1080])).
% 5.97/2.21  tff(c_310, plain, (![B_443]: (m1_subset_1(u1_struct_0(B_443), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_443, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_191, c_299])).
% 5.97/2.21  tff(c_1227, plain, (![B_494]: (m1_subset_1(u1_struct_0(B_494), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc(B_494, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_310])).
% 5.97/2.21  tff(c_1238, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3'))) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_187, c_1227])).
% 5.97/2.21  tff(c_1248, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_1238])).
% 5.97/2.21  tff(c_1255, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_1248, c_10])).
% 5.97/2.21  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.97/2.21  tff(c_1257, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4') | ~r1_tarski(k2_struct_0('#skF_3'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1255, c_2])).
% 5.97/2.21  tff(c_1260, plain, (k2_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_911, c_1257])).
% 5.97/2.21  tff(c_1262, plain, (m1_subset_1(k2_struct_0('#skF_4'), k1_zfmisc_1(k2_struct_0('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_1248])).
% 5.97/2.21  tff(c_84, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_78, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_72, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_48, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_76, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_74, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_64, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_104, plain, (![A_423]: (u1_struct_0(A_423)=k2_struct_0(A_423) | ~l1_pre_topc(A_423))), inference(resolution, [status(thm)], [c_20, c_99])).
% 5.97/2.21  tff(c_112, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_74, c_104])).
% 5.97/2.21  tff(c_62, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_117, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_62])).
% 5.97/2.21  tff(c_193, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_117])).
% 5.97/2.21  tff(c_60, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_142, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_112, c_60])).
% 5.97/2.21  tff(c_192, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_142])).
% 5.97/2.21  tff(c_912, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(splitRight, [status(thm)], [c_368])).
% 5.97/2.21  tff(c_1272, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1260, c_191])).
% 5.97/2.21  tff(c_52, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_50, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_249])).
% 5.97/2.21  tff(c_86, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_50])).
% 5.97/2.21  tff(c_1690, plain, (![D_522, B_527, F_521, H_524, C_526, A_525, E_523]: (r1_tmap_1(D_522, B_527, E_523, H_524) | ~r1_tmap_1(C_526, B_527, k3_tmap_1(A_525, B_527, D_522, C_526, E_523), H_524) | ~m1_connsp_2(F_521, D_522, H_524) | ~r1_tarski(F_521, u1_struct_0(C_526)) | ~m1_subset_1(H_524, u1_struct_0(C_526)) | ~m1_subset_1(H_524, u1_struct_0(D_522)) | ~m1_subset_1(F_521, k1_zfmisc_1(u1_struct_0(D_522))) | ~m1_pre_topc(C_526, D_522) | ~m1_subset_1(E_523, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_522), u1_struct_0(B_527)))) | ~v1_funct_2(E_523, u1_struct_0(D_522), u1_struct_0(B_527)) | ~v1_funct_1(E_523) | ~m1_pre_topc(D_522, A_525) | v2_struct_0(D_522) | ~m1_pre_topc(C_526, A_525) | v2_struct_0(C_526) | ~l1_pre_topc(B_527) | ~v2_pre_topc(B_527) | v2_struct_0(B_527) | ~l1_pre_topc(A_525) | ~v2_pre_topc(A_525) | v2_struct_0(A_525))), inference(cnfTransformation, [status(thm)], [f_200])).
% 5.97/2.21  tff(c_1692, plain, (![F_521]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_521, '#skF_4', '#skF_6') | ~r1_tarski(F_521, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_521, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_86, c_1690])).
% 5.97/2.21  tff(c_1695, plain, (![F_521]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_521, '#skF_4', '#skF_6') | ~r1_tarski(F_521, k2_struct_0('#skF_4')) | ~m1_subset_1(F_521, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_80, c_76, c_74, c_70, c_66, c_64, c_193, c_112, c_187, c_192, c_112, c_187, c_912, c_187, c_194, c_187, c_194, c_1272, c_1272, c_1692])).
% 5.97/2.21  tff(c_1700, plain, (![F_528]: (~m1_connsp_2(F_528, '#skF_4', '#skF_6') | ~r1_tarski(F_528, k2_struct_0('#skF_4')) | ~m1_subset_1(F_528, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_84, c_78, c_72, c_68, c_48, c_1695])).
% 5.97/2.21  tff(c_1703, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_1262, c_1700])).
% 5.97/2.21  tff(c_1713, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1703])).
% 5.97/2.21  tff(c_1601, plain, (![B_506, A_507, C_508]: (m1_connsp_2(B_506, A_507, C_508) | ~r2_hidden(C_508, B_506) | ~v3_pre_topc(B_506, A_507) | ~m1_subset_1(C_508, u1_struct_0(A_507)) | ~m1_subset_1(B_506, k1_zfmisc_1(u1_struct_0(A_507))) | ~l1_pre_topc(A_507) | ~v2_pre_topc(A_507) | v2_struct_0(A_507))), inference(cnfTransformation, [status(thm)], [f_113])).
% 5.97/2.21  tff(c_1605, plain, (![B_506, C_508]: (m1_connsp_2(B_506, '#skF_4', C_508) | ~r2_hidden(C_508, B_506) | ~v3_pre_topc(B_506, '#skF_4') | ~m1_subset_1(C_508, k2_struct_0('#skF_4')) | ~m1_subset_1(B_506, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_1601])).
% 5.97/2.21  tff(c_1614, plain, (![B_506, C_508]: (m1_connsp_2(B_506, '#skF_4', C_508) | ~r2_hidden(C_508, B_506) | ~v3_pre_topc(B_506, '#skF_4') | ~m1_subset_1(C_508, k2_struct_0('#skF_4')) | ~m1_subset_1(B_506, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_288, c_180, c_187, c_1605])).
% 5.97/2.21  tff(c_1824, plain, (![B_535, C_536]: (m1_connsp_2(B_535, '#skF_4', C_536) | ~r2_hidden(C_536, B_535) | ~v3_pre_topc(B_535, '#skF_4') | ~m1_subset_1(C_536, k2_struct_0('#skF_4')) | ~m1_subset_1(B_535, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_68, c_1614])).
% 5.97/2.21  tff(c_4613, plain, (![B_611]: (m1_connsp_2(B_611, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_611) | ~v3_pre_topc(B_611, '#skF_4') | ~m1_subset_1(B_611, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_194, c_1824])).
% 5.97/2.21  tff(c_4619, plain, (m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_1262, c_4613])).
% 5.97/2.21  tff(c_4630, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1713, c_4619])).
% 5.97/2.21  tff(c_4633, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_4630])).
% 5.97/2.21  tff(c_4636, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_4633])).
% 5.97/2.21  tff(c_4640, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_288, c_180, c_4636])).
% 5.97/2.21  tff(c_4641, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_4630])).
% 5.97/2.21  tff(c_4645, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_8, c_4641])).
% 5.97/2.21  tff(c_4648, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_194, c_4645])).
% 5.97/2.21  tff(c_4650, plain, $false, inference(negUnitSimplification, [status(thm)], [c_226, c_4648])).
% 5.97/2.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.97/2.21  
% 5.97/2.21  Inference rules
% 5.97/2.21  ----------------------
% 5.97/2.21  #Ref     : 0
% 5.97/2.21  #Sup     : 955
% 5.97/2.21  #Fact    : 0
% 5.97/2.21  #Define  : 0
% 5.97/2.21  #Split   : 20
% 5.97/2.21  #Chain   : 0
% 5.97/2.21  #Close   : 0
% 5.97/2.21  
% 5.97/2.21  Ordering : KBO
% 5.97/2.21  
% 5.97/2.21  Simplification rules
% 5.97/2.21  ----------------------
% 5.97/2.21  #Subsume      : 181
% 5.97/2.21  #Demod        : 1214
% 5.97/2.21  #Tautology    : 278
% 5.97/2.21  #SimpNegUnit  : 36
% 5.97/2.21  #BackRed      : 21
% 5.97/2.21  
% 5.97/2.21  #Partial instantiations: 0
% 5.97/2.21  #Strategies tried      : 1
% 5.97/2.21  
% 5.97/2.21  Timing (in seconds)
% 5.97/2.21  ----------------------
% 5.97/2.21  Preprocessing        : 0.38
% 5.97/2.21  Parsing              : 0.19
% 5.97/2.21  CNF conversion       : 0.06
% 5.97/2.21  Main loop            : 0.98
% 5.97/2.21  Inferencing          : 0.31
% 5.97/2.21  Reduction            : 0.38
% 5.97/2.21  Demodulation         : 0.28
% 5.97/2.21  BG Simplification    : 0.04
% 5.97/2.21  Subsumption          : 0.19
% 5.97/2.21  Abstraction          : 0.04
% 5.97/2.21  MUC search           : 0.00
% 5.97/2.21  Cooper               : 0.00
% 5.97/2.21  Total                : 1.41
% 5.97/2.21  Index Insertion      : 0.00
% 5.97/2.21  Index Deletion       : 0.00
% 5.97/2.21  Index Matching       : 0.00
% 5.97/2.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
