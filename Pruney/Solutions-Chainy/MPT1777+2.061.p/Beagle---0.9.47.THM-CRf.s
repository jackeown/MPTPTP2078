%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:41 EST 2020

% Result     : Theorem 3.97s
% Output     : CNFRefutation 4.31s
% Verified   : 
% Statistics : Number of formulae       :  147 (1125 expanded)
%              Number of leaves         :   48 ( 414 expanded)
%              Depth                    :   17
%              Number of atoms          :  309 (5327 expanded)
%              Number of equality atoms :   15 ( 602 expanded)
%              Maximal formula depth    :   29 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_241,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => l1_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

tff(f_58,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => l1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

tff(f_54,axiom,(
    ! [A] :
      ( l1_struct_0(A)
     => k2_struct_0(A) = u1_struct_0(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

tff(f_73,axiom,(
    ! [A] :
      ( ( ~ v2_struct_0(A)
        & l1_struct_0(A) )
     => ~ v1_xboole_0(u1_struct_0(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_50,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => ! [B] :
          ( m1_pre_topc(B,A)
         => v2_pre_topc(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

tff(f_95,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_118,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_125,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_80,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_89,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_192,axiom,(
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

tff(f_114,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_connsp_2)).

tff(c_72,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_58,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_163,plain,(
    ! [B_424,A_425] :
      ( l1_pre_topc(B_424)
      | ~ m1_pre_topc(B_424,A_425)
      | ~ l1_pre_topc(A_425) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_172,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_163])).

tff(c_179,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_172])).

tff(c_14,plain,(
    ! [A_12] :
      ( l1_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_100,plain,(
    ! [A_421] :
      ( u1_struct_0(A_421) = k2_struct_0(A_421)
      | ~ l1_struct_0(A_421) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_104,plain,(
    ! [A_12] :
      ( u1_struct_0(A_12) = k2_struct_0(A_12)
      | ~ l1_pre_topc(A_12) ) ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_187,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_179,c_104])).

tff(c_18,plain,(
    ! [A_16] :
      ( ~ v1_xboole_0(u1_struct_0(A_16))
      | ~ l1_struct_0(A_16)
      | v2_struct_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_218,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_18])).

tff(c_221,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_218])).

tff(c_224,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_221])).

tff(c_227,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_224])).

tff(c_231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_227])).

tff(c_232,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_221])).

tff(c_48,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

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
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_245,plain,(
    ! [B_429,A_430] :
      ( v2_pre_topc(B_429)
      | ~ m1_pre_topc(B_429,A_430)
      | ~ l1_pre_topc(A_430)
      | ~ v2_pre_topc(A_430) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_254,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_245])).

tff(c_261,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_254])).

tff(c_26,plain,(
    ! [A_23] :
      ( v3_pre_topc(k2_struct_0(A_23),A_23)
      | ~ l1_pre_topc(A_23)
      | ~ v2_pre_topc(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_30,plain,(
    ! [A_31] :
      ( m1_pre_topc(A_31,A_31)
      | ~ l1_pre_topc(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_274,plain,(
    ! [B_436,A_437] :
      ( r1_tarski(u1_struct_0(B_436),u1_struct_0(A_437))
      | ~ m1_pre_topc(B_436,A_437)
      | ~ l1_pre_topc(A_437) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_280,plain,(
    ! [B_436] :
      ( r1_tarski(u1_struct_0(B_436),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_436,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_274])).

tff(c_307,plain,(
    ! [B_438] :
      ( r1_tarski(u1_struct_0(B_438),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_438,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_280])).

tff(c_310,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_307])).

tff(c_614,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_310])).

tff(c_617,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_614])).

tff(c_621,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_617])).

tff(c_623,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_310])).

tff(c_62,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_169,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_62,c_163])).

tff(c_176,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_169])).

tff(c_183,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_176,c_104])).

tff(c_50,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_188,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_50])).

tff(c_346,plain,(
    ! [B_441,A_442] :
      ( m1_pre_topc(B_441,A_442)
      | ~ m1_pre_topc(B_441,g1_pre_topc(u1_struct_0(A_442),u1_pre_topc(A_442)))
      | ~ l1_pre_topc(A_442) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_352,plain,(
    ! [B_441] :
      ( m1_pre_topc(B_441,'#skF_3')
      | ~ m1_pre_topc(B_441,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_346])).

tff(c_366,plain,(
    ! [B_441] :
      ( m1_pre_topc(B_441,'#skF_3')
      | ~ m1_pre_topc(B_441,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_188,c_352])).

tff(c_286,plain,(
    ! [B_436] :
      ( r1_tarski(u1_struct_0(B_436),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_436,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_274])).

tff(c_320,plain,(
    ! [B_439] :
      ( r1_tarski(u1_struct_0(B_439),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_439,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_286])).

tff(c_323,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_320])).

tff(c_716,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_323])).

tff(c_719,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_366,c_716])).

tff(c_723,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_719])).

tff(c_724,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_323])).

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
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_70,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_64,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_40,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_68,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_66,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_105,plain,(
    ! [A_422] :
      ( u1_struct_0(A_422) = k2_struct_0(A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(resolution,[status(thm)],[c_14,c_100])).

tff(c_113,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_105])).

tff(c_54,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_118,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_54])).

tff(c_234,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_118])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_147,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_52])).

tff(c_213,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_147])).

tff(c_467,plain,(
    ! [A_451,B_452] :
      ( m1_pre_topc(A_451,g1_pre_topc(u1_struct_0(B_452),u1_pre_topc(B_452)))
      | ~ m1_pre_topc(A_451,B_452)
      | ~ l1_pre_topc(B_452)
      | ~ l1_pre_topc(A_451) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_488,plain,(
    ! [A_451] :
      ( m1_pre_topc(A_451,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_451,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_451) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_467])).

tff(c_531,plain,(
    ! [A_453] :
      ( m1_pre_topc(A_453,'#skF_4')
      | ~ m1_pre_topc(A_453,'#skF_3')
      | ~ l1_pre_topc(A_453) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_188,c_488])).

tff(c_538,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_531])).

tff(c_542,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_176,c_538])).

tff(c_44,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_46,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_77,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_46])).

tff(c_189,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_77])).

tff(c_42,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_241])).

tff(c_78,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42])).

tff(c_702,plain,(
    ! [C_464,E_465,F_460,A_462,H_466,D_461,B_463] :
      ( r1_tmap_1(D_461,B_463,E_465,H_466)
      | ~ r1_tmap_1(C_464,B_463,k3_tmap_1(A_462,B_463,D_461,C_464,E_465),H_466)
      | ~ m1_connsp_2(F_460,D_461,H_466)
      | ~ r1_tarski(F_460,u1_struct_0(C_464))
      | ~ m1_subset_1(H_466,u1_struct_0(C_464))
      | ~ m1_subset_1(H_466,u1_struct_0(D_461))
      | ~ m1_subset_1(F_460,k1_zfmisc_1(u1_struct_0(D_461)))
      | ~ m1_pre_topc(C_464,D_461)
      | ~ m1_subset_1(E_465,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_461),u1_struct_0(B_463))))
      | ~ v1_funct_2(E_465,u1_struct_0(D_461),u1_struct_0(B_463))
      | ~ v1_funct_1(E_465)
      | ~ m1_pre_topc(D_461,A_462)
      | v2_struct_0(D_461)
      | ~ m1_pre_topc(C_464,A_462)
      | v2_struct_0(C_464)
      | ~ l1_pre_topc(B_463)
      | ~ v2_pre_topc(B_463)
      | v2_struct_0(B_463)
      | ~ l1_pre_topc(A_462)
      | ~ v2_pre_topc(A_462)
      | v2_struct_0(A_462) ) ),
    inference(cnfTransformation,[status(thm)],[f_192])).

tff(c_704,plain,(
    ! [F_460] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_460,'#skF_4','#skF_6')
      | ~ r1_tarski(F_460,u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_460,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_78,c_702])).

tff(c_707,plain,(
    ! [F_460] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ m1_connsp_2(F_460,'#skF_4','#skF_6')
      | ~ r1_tarski(F_460,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(F_460,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_68,c_66,c_62,c_58,c_56,c_234,c_113,c_187,c_213,c_113,c_187,c_542,c_187,c_214,c_187,c_189,c_183,c_183,c_704])).

tff(c_710,plain,(
    ! [F_467] :
      ( ~ m1_connsp_2(F_467,'#skF_4','#skF_6')
      | ~ r1_tarski(F_467,k2_struct_0('#skF_3'))
      | ~ m1_subset_1(F_467,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_70,c_64,c_60,c_40,c_707])).

tff(c_715,plain,
    ( ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(resolution,[status(thm)],[c_79,c_710])).

tff(c_1033,plain,(
    ~ m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_715])).

tff(c_649,plain,(
    ! [B_455,A_456,C_457] :
      ( m1_connsp_2(B_455,A_456,C_457)
      | ~ r2_hidden(C_457,B_455)
      | ~ v3_pre_topc(B_455,A_456)
      | ~ m1_subset_1(C_457,u1_struct_0(A_456))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0(A_456)))
      | ~ l1_pre_topc(A_456)
      | ~ v2_pre_topc(A_456)
      | v2_struct_0(A_456) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_651,plain,(
    ! [B_455,C_457] :
      ( m1_connsp_2(B_455,'#skF_4',C_457)
      | ~ r2_hidden(C_457,B_455)
      | ~ v3_pre_topc(B_455,'#skF_4')
      | ~ m1_subset_1(C_457,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(u1_struct_0('#skF_4')))
      | ~ l1_pre_topc('#skF_4')
      | ~ v2_pre_topc('#skF_4')
      | v2_struct_0('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_187,c_649])).

tff(c_659,plain,(
    ! [B_455,C_457] :
      ( m1_connsp_2(B_455,'#skF_4',C_457)
      | ~ r2_hidden(C_457,B_455)
      | ~ v3_pre_topc(B_455,'#skF_4')
      | ~ m1_subset_1(C_457,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_455,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_179,c_187,c_651])).

tff(c_680,plain,(
    ! [B_458,C_459] :
      ( m1_connsp_2(B_458,'#skF_4',C_459)
      | ~ r2_hidden(C_459,B_458)
      | ~ v3_pre_topc(B_458,'#skF_4')
      | ~ m1_subset_1(C_459,k2_struct_0('#skF_4'))
      | ~ m1_subset_1(B_458,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_659])).

tff(c_1305,plain,(
    ! [B_501] :
      ( m1_connsp_2(B_501,'#skF_4','#skF_6')
      | ~ r2_hidden('#skF_6',B_501)
      | ~ v3_pre_topc(B_501,'#skF_4')
      | ~ m1_subset_1(B_501,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(resolution,[status(thm)],[c_214,c_680])).

tff(c_1309,plain,
    ( m1_connsp_2(k2_struct_0('#skF_4'),'#skF_4','#skF_6')
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_79,c_1305])).

tff(c_1312,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1033,c_1309])).

tff(c_1313,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_1312])).

tff(c_1316,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_1313])).

tff(c_1320,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_179,c_1316])).

tff(c_1321,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_1312])).

tff(c_1325,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_1321])).

tff(c_1328,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_214,c_1325])).

tff(c_1330,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_232,c_1328])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.97/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.63  
% 3.97/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.97/1.64  %$ r1_tmap_1 > v1_funct_2 > m1_connsp_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.97/1.64  
% 3.97/1.64  %Foreground sorts:
% 3.97/1.64  
% 3.97/1.64  
% 3.97/1.64  %Background operators:
% 3.97/1.64  
% 3.97/1.64  
% 3.97/1.64  %Foreground operators:
% 3.97/1.64  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.97/1.64  tff(m1_connsp_2, type, m1_connsp_2: ($i * $i * $i) > $o).
% 3.97/1.64  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.97/1.64  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.97/1.64  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.97/1.64  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.97/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.97/1.64  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.97/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.97/1.64  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.97/1.64  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.97/1.64  tff('#skF_7', type, '#skF_7': $i).
% 3.97/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.97/1.64  tff('#skF_5', type, '#skF_5': $i).
% 3.97/1.64  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.97/1.64  tff('#skF_6', type, '#skF_6': $i).
% 3.97/1.64  tff('#skF_2', type, '#skF_2': $i).
% 3.97/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.97/1.64  tff('#skF_1', type, '#skF_1': $i).
% 3.97/1.64  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.97/1.64  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.97/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.97/1.64  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.97/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.97/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.97/1.64  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.97/1.64  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.97/1.64  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.97/1.64  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.97/1.64  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.97/1.64  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.97/1.64  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.97/1.64  
% 4.31/1.67  tff(f_241, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_tmap_1)).
% 4.31/1.67  tff(f_65, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 4.31/1.67  tff(f_58, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 4.31/1.67  tff(f_54, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_struct_0)).
% 4.31/1.67  tff(f_73, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc2_struct_0)).
% 4.31/1.67  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 4.31/1.67  tff(f_50, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_pre_topc)).
% 4.31/1.67  tff(f_95, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_tops_1)).
% 4.31/1.67  tff(f_118, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tsep_1)).
% 4.31/1.67  tff(f_125, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_borsuk_1)).
% 4.31/1.67  tff(f_80, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_pre_topc)).
% 4.31/1.67  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.31/1.67  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.31/1.67  tff(f_89, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_pre_topc)).
% 4.31/1.67  tff(f_192, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => (((r1_tarski(F, u1_struct_0(C)) & m1_connsp_2(F, D, G)) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_tmap_1)).
% 4.31/1.67  tff(f_114, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(u1_struct_0(A))) => (![C]: (m1_subset_1(C, u1_struct_0(A)) => ((v3_pre_topc(B, A) & r2_hidden(C, B)) => m1_connsp_2(B, A, C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_connsp_2)).
% 4.31/1.67  tff(c_72, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_58, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_163, plain, (![B_424, A_425]: (l1_pre_topc(B_424) | ~m1_pre_topc(B_424, A_425) | ~l1_pre_topc(A_425))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.31/1.67  tff(c_172, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_163])).
% 4.31/1.67  tff(c_179, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_172])).
% 4.31/1.67  tff(c_14, plain, (![A_12]: (l1_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.31/1.67  tff(c_60, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_100, plain, (![A_421]: (u1_struct_0(A_421)=k2_struct_0(A_421) | ~l1_struct_0(A_421))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.31/1.67  tff(c_104, plain, (![A_12]: (u1_struct_0(A_12)=k2_struct_0(A_12) | ~l1_pre_topc(A_12))), inference(resolution, [status(thm)], [c_14, c_100])).
% 4.31/1.67  tff(c_187, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_179, c_104])).
% 4.31/1.67  tff(c_18, plain, (![A_16]: (~v1_xboole_0(u1_struct_0(A_16)) | ~l1_struct_0(A_16) | v2_struct_0(A_16))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.31/1.67  tff(c_218, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_187, c_18])).
% 4.31/1.67  tff(c_221, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_60, c_218])).
% 4.31/1.67  tff(c_224, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_221])).
% 4.31/1.67  tff(c_227, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_14, c_224])).
% 4.31/1.67  tff(c_231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_227])).
% 4.31/1.67  tff(c_232, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_221])).
% 4.31/1.67  tff(c_48, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_214, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_48])).
% 4.31/1.67  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.31/1.67  tff(c_74, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_245, plain, (![B_429, A_430]: (v2_pre_topc(B_429) | ~m1_pre_topc(B_429, A_430) | ~l1_pre_topc(A_430) | ~v2_pre_topc(A_430))), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.31/1.67  tff(c_254, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_245])).
% 4.31/1.67  tff(c_261, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_254])).
% 4.31/1.67  tff(c_26, plain, (![A_23]: (v3_pre_topc(k2_struct_0(A_23), A_23) | ~l1_pre_topc(A_23) | ~v2_pre_topc(A_23))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.31/1.67  tff(c_30, plain, (![A_31]: (m1_pre_topc(A_31, A_31) | ~l1_pre_topc(A_31))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.31/1.67  tff(c_274, plain, (![B_436, A_437]: (r1_tarski(u1_struct_0(B_436), u1_struct_0(A_437)) | ~m1_pre_topc(B_436, A_437) | ~l1_pre_topc(A_437))), inference(cnfTransformation, [status(thm)], [f_125])).
% 4.31/1.67  tff(c_280, plain, (![B_436]: (r1_tarski(u1_struct_0(B_436), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_436, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_274])).
% 4.31/1.67  tff(c_307, plain, (![B_438]: (r1_tarski(u1_struct_0(B_438), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_438, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_280])).
% 4.31/1.67  tff(c_310, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_187, c_307])).
% 4.31/1.67  tff(c_614, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_310])).
% 4.31/1.67  tff(c_617, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_30, c_614])).
% 4.31/1.67  tff(c_621, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_617])).
% 4.31/1.67  tff(c_623, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_310])).
% 4.31/1.67  tff(c_62, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_169, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_62, c_163])).
% 4.31/1.67  tff(c_176, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_169])).
% 4.31/1.67  tff(c_183, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_176, c_104])).
% 4.31/1.67  tff(c_50, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_188, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_183, c_50])).
% 4.31/1.67  tff(c_346, plain, (![B_441, A_442]: (m1_pre_topc(B_441, A_442) | ~m1_pre_topc(B_441, g1_pre_topc(u1_struct_0(A_442), u1_pre_topc(A_442))) | ~l1_pre_topc(A_442))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.31/1.67  tff(c_352, plain, (![B_441]: (m1_pre_topc(B_441, '#skF_3') | ~m1_pre_topc(B_441, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_346])).
% 4.31/1.67  tff(c_366, plain, (![B_441]: (m1_pre_topc(B_441, '#skF_3') | ~m1_pre_topc(B_441, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_188, c_352])).
% 4.31/1.67  tff(c_286, plain, (![B_436]: (r1_tarski(u1_struct_0(B_436), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_436, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_274])).
% 4.31/1.67  tff(c_320, plain, (![B_439]: (r1_tarski(u1_struct_0(B_439), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_439, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_286])).
% 4.31/1.67  tff(c_323, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_187, c_320])).
% 4.31/1.67  tff(c_716, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_323])).
% 4.31/1.67  tff(c_719, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_366, c_716])).
% 4.31/1.67  tff(c_723, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_623, c_719])).
% 4.31/1.67  tff(c_724, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_323])).
% 4.31/1.67  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.31/1.67  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.31/1.67  tff(c_79, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 4.31/1.67  tff(c_76, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_70, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_64, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_40, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_68, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_66, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_105, plain, (![A_422]: (u1_struct_0(A_422)=k2_struct_0(A_422) | ~l1_pre_topc(A_422))), inference(resolution, [status(thm)], [c_14, c_100])).
% 4.31/1.67  tff(c_113, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_66, c_105])).
% 4.31/1.67  tff(c_54, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_118, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_54])).
% 4.31/1.67  tff(c_234, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_118])).
% 4.31/1.67  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_147, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_52])).
% 4.31/1.67  tff(c_213, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_187, c_147])).
% 4.31/1.67  tff(c_467, plain, (![A_451, B_452]: (m1_pre_topc(A_451, g1_pre_topc(u1_struct_0(B_452), u1_pre_topc(B_452))) | ~m1_pre_topc(A_451, B_452) | ~l1_pre_topc(B_452) | ~l1_pre_topc(A_451))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.31/1.67  tff(c_488, plain, (![A_451]: (m1_pre_topc(A_451, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_451, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_451))), inference(superposition, [status(thm), theory('equality')], [c_183, c_467])).
% 4.31/1.67  tff(c_531, plain, (![A_453]: (m1_pre_topc(A_453, '#skF_4') | ~m1_pre_topc(A_453, '#skF_3') | ~l1_pre_topc(A_453))), inference(demodulation, [status(thm), theory('equality')], [c_176, c_188, c_488])).
% 4.31/1.67  tff(c_538, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_30, c_531])).
% 4.31/1.67  tff(c_542, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_176, c_538])).
% 4.31/1.67  tff(c_44, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_46, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_77, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_46])).
% 4.31/1.67  tff(c_189, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_77])).
% 4.31/1.67  tff(c_42, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_241])).
% 4.31/1.67  tff(c_78, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_42])).
% 4.31/1.67  tff(c_702, plain, (![C_464, E_465, F_460, A_462, H_466, D_461, B_463]: (r1_tmap_1(D_461, B_463, E_465, H_466) | ~r1_tmap_1(C_464, B_463, k3_tmap_1(A_462, B_463, D_461, C_464, E_465), H_466) | ~m1_connsp_2(F_460, D_461, H_466) | ~r1_tarski(F_460, u1_struct_0(C_464)) | ~m1_subset_1(H_466, u1_struct_0(C_464)) | ~m1_subset_1(H_466, u1_struct_0(D_461)) | ~m1_subset_1(F_460, k1_zfmisc_1(u1_struct_0(D_461))) | ~m1_pre_topc(C_464, D_461) | ~m1_subset_1(E_465, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_461), u1_struct_0(B_463)))) | ~v1_funct_2(E_465, u1_struct_0(D_461), u1_struct_0(B_463)) | ~v1_funct_1(E_465) | ~m1_pre_topc(D_461, A_462) | v2_struct_0(D_461) | ~m1_pre_topc(C_464, A_462) | v2_struct_0(C_464) | ~l1_pre_topc(B_463) | ~v2_pre_topc(B_463) | v2_struct_0(B_463) | ~l1_pre_topc(A_462) | ~v2_pre_topc(A_462) | v2_struct_0(A_462))), inference(cnfTransformation, [status(thm)], [f_192])).
% 4.31/1.67  tff(c_704, plain, (![F_460]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_460, '#skF_4', '#skF_6') | ~r1_tarski(F_460, u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_460, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_78, c_702])).
% 4.31/1.67  tff(c_707, plain, (![F_460]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~m1_connsp_2(F_460, '#skF_4', '#skF_6') | ~r1_tarski(F_460, k2_struct_0('#skF_3')) | ~m1_subset_1(F_460, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_68, c_66, c_62, c_58, c_56, c_234, c_113, c_187, c_213, c_113, c_187, c_542, c_187, c_214, c_187, c_189, c_183, c_183, c_704])).
% 4.31/1.67  tff(c_710, plain, (![F_467]: (~m1_connsp_2(F_467, '#skF_4', '#skF_6') | ~r1_tarski(F_467, k2_struct_0('#skF_3')) | ~m1_subset_1(F_467, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_76, c_70, c_64, c_60, c_40, c_707])).
% 4.31/1.67  tff(c_715, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(resolution, [status(thm)], [c_79, c_710])).
% 4.31/1.67  tff(c_1033, plain, (~m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_724, c_715])).
% 4.31/1.67  tff(c_649, plain, (![B_455, A_456, C_457]: (m1_connsp_2(B_455, A_456, C_457) | ~r2_hidden(C_457, B_455) | ~v3_pre_topc(B_455, A_456) | ~m1_subset_1(C_457, u1_struct_0(A_456)) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0(A_456))) | ~l1_pre_topc(A_456) | ~v2_pre_topc(A_456) | v2_struct_0(A_456))), inference(cnfTransformation, [status(thm)], [f_114])).
% 4.31/1.67  tff(c_651, plain, (![B_455, C_457]: (m1_connsp_2(B_455, '#skF_4', C_457) | ~r2_hidden(C_457, B_455) | ~v3_pre_topc(B_455, '#skF_4') | ~m1_subset_1(C_457, k2_struct_0('#skF_4')) | ~m1_subset_1(B_455, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4') | v2_struct_0('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_187, c_649])).
% 4.31/1.67  tff(c_659, plain, (![B_455, C_457]: (m1_connsp_2(B_455, '#skF_4', C_457) | ~r2_hidden(C_457, B_455) | ~v3_pre_topc(B_455, '#skF_4') | ~m1_subset_1(C_457, k2_struct_0('#skF_4')) | ~m1_subset_1(B_455, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_261, c_179, c_187, c_651])).
% 4.31/1.67  tff(c_680, plain, (![B_458, C_459]: (m1_connsp_2(B_458, '#skF_4', C_459) | ~r2_hidden(C_459, B_458) | ~v3_pre_topc(B_458, '#skF_4') | ~m1_subset_1(C_459, k2_struct_0('#skF_4')) | ~m1_subset_1(B_458, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_60, c_659])).
% 4.31/1.67  tff(c_1305, plain, (![B_501]: (m1_connsp_2(B_501, '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', B_501) | ~v3_pre_topc(B_501, '#skF_4') | ~m1_subset_1(B_501, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(resolution, [status(thm)], [c_214, c_680])).
% 4.31/1.67  tff(c_1309, plain, (m1_connsp_2(k2_struct_0('#skF_4'), '#skF_4', '#skF_6') | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_79, c_1305])).
% 4.31/1.67  tff(c_1312, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1033, c_1309])).
% 4.31/1.67  tff(c_1313, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_1312])).
% 4.31/1.67  tff(c_1316, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_1313])).
% 4.31/1.67  tff(c_1320, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_261, c_179, c_1316])).
% 4.31/1.67  tff(c_1321, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_1312])).
% 4.31/1.67  tff(c_1325, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_1321])).
% 4.31/1.67  tff(c_1328, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_214, c_1325])).
% 4.31/1.67  tff(c_1330, plain, $false, inference(negUnitSimplification, [status(thm)], [c_232, c_1328])).
% 4.31/1.67  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.31/1.67  
% 4.31/1.67  Inference rules
% 4.31/1.67  ----------------------
% 4.31/1.67  #Ref     : 0
% 4.31/1.67  #Sup     : 240
% 4.31/1.67  #Fact    : 0
% 4.31/1.67  #Define  : 0
% 4.31/1.67  #Split   : 18
% 4.31/1.67  #Chain   : 0
% 4.31/1.67  #Close   : 0
% 4.31/1.67  
% 4.31/1.67  Ordering : KBO
% 4.31/1.67  
% 4.31/1.67  Simplification rules
% 4.31/1.67  ----------------------
% 4.31/1.67  #Subsume      : 32
% 4.31/1.67  #Demod        : 293
% 4.31/1.67  #Tautology    : 92
% 4.31/1.67  #SimpNegUnit  : 13
% 4.31/1.68  #BackRed      : 5
% 4.31/1.68  
% 4.31/1.68  #Partial instantiations: 0
% 4.31/1.68  #Strategies tried      : 1
% 4.31/1.68  
% 4.31/1.68  Timing (in seconds)
% 4.31/1.68  ----------------------
% 4.41/1.68  Preprocessing        : 0.41
% 4.41/1.68  Parsing              : 0.21
% 4.41/1.68  CNF conversion       : 0.06
% 4.41/1.68  Main loop            : 0.45
% 4.41/1.68  Inferencing          : 0.15
% 4.41/1.68  Reduction            : 0.16
% 4.41/1.68  Demodulation         : 0.11
% 4.41/1.68  BG Simplification    : 0.02
% 4.41/1.68  Subsumption          : 0.09
% 4.41/1.68  Abstraction          : 0.02
% 4.41/1.68  MUC search           : 0.00
% 4.41/1.68  Cooper               : 0.00
% 4.41/1.68  Total                : 0.93
% 4.41/1.68  Index Insertion      : 0.00
% 4.41/1.68  Index Deletion       : 0.00
% 4.41/1.68  Index Matching       : 0.00
% 4.41/1.68  BG Taut test         : 0.00
%------------------------------------------------------------------------------
