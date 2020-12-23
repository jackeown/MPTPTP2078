%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:27:41 EST 2020

% Result     : Theorem 3.60s
% Output     : CNFRefutation 3.87s
% Verified   : 
% Statistics : Number of formulae       :  138 ( 968 expanded)
%              Number of leaves         :   46 ( 359 expanded)
%              Depth                    :   16
%              Number of atoms          :  272 (4559 expanded)
%              Number of equality atoms :   15 ( 522 expanded)
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

tff(f_218,negated_conjecture,(
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

tff(f_89,axiom,(
    ! [A] :
      ( ( v2_pre_topc(A)
        & l1_pre_topc(A) )
     => v3_pre_topc(k2_struct_0(A),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

tff(f_93,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => m1_pre_topc(A,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

tff(f_100,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,A)
         => r1_tarski(u1_struct_0(B),u1_struct_0(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

tff(f_74,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( m1_pre_topc(B,g1_pre_topc(u1_struct_0(A),u1_pre_topc(A)))
         => m1_pre_topc(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_pre_topc)).

tff(f_27,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_29,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_83,axiom,(
    ! [A] :
      ( l1_pre_topc(A)
     => ! [B] :
          ( l1_pre_topc(B)
         => ( m1_pre_topc(A,B)
          <=> m1_pre_topc(A,g1_pre_topc(u1_struct_0(B),u1_pre_topc(B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

tff(f_169,axiom,(
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

tff(c_68,plain,(
    l1_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_54,plain,(
    m1_pre_topc('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_159,plain,(
    ! [B_414,A_415] :
      ( l1_pre_topc(B_414)
      | ~ m1_pre_topc(B_414,A_415)
      | ~ l1_pre_topc(A_415) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_168,plain,
    ( l1_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_159])).

tff(c_175,plain,(
    l1_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_168])).

tff(c_12,plain,(
    ! [A_9] :
      ( l1_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_56,plain,(
    ~ v2_struct_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_96,plain,(
    ! [A_411] :
      ( u1_struct_0(A_411) = k2_struct_0(A_411)
      | ~ l1_struct_0(A_411) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_100,plain,(
    ! [A_9] :
      ( u1_struct_0(A_9) = k2_struct_0(A_9)
      | ~ l1_pre_topc(A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_183,plain,(
    u1_struct_0('#skF_4') = k2_struct_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_175,c_100])).

tff(c_16,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(u1_struct_0(A_13))
      | ~ l1_struct_0(A_13)
      | v2_struct_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_214,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4')
    | v2_struct_0('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_16])).

tff(c_217,plain,
    ( ~ v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ l1_struct_0('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_214])).

tff(c_220,plain,(
    ~ l1_struct_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_217])).

tff(c_223,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_12,c_220])).

tff(c_227,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_223])).

tff(c_228,plain,(
    ~ v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_217])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_210,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_44])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r2_hidden(A_3,B_4)
      | v1_xboole_0(B_4)
      | ~ m1_subset_1(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_70,plain,(
    v2_pre_topc('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_241,plain,(
    ! [B_419,A_420] :
      ( v2_pre_topc(B_419)
      | ~ m1_pre_topc(B_419,A_420)
      | ~ l1_pre_topc(A_420)
      | ~ v2_pre_topc(A_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_250,plain,
    ( v2_pre_topc('#skF_4')
    | ~ l1_pre_topc('#skF_1')
    | ~ v2_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_241])).

tff(c_257,plain,(
    v2_pre_topc('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_250])).

tff(c_24,plain,(
    ! [A_20] :
      ( v3_pre_topc(k2_struct_0(A_20),A_20)
      | ~ l1_pre_topc(A_20)
      | ~ v2_pre_topc(A_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_26,plain,(
    ! [A_21] :
      ( m1_pre_topc(A_21,A_21)
      | ~ l1_pre_topc(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_258,plain,(
    ! [B_421,A_422] :
      ( r1_tarski(u1_struct_0(B_421),u1_struct_0(A_422))
      | ~ m1_pre_topc(B_421,A_422)
      | ~ l1_pre_topc(A_422) ) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_264,plain,(
    ! [B_421] :
      ( r1_tarski(u1_struct_0(B_421),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_421,'#skF_4')
      | ~ l1_pre_topc('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_258])).

tff(c_321,plain,(
    ! [B_425] :
      ( r1_tarski(u1_struct_0(B_425),k2_struct_0('#skF_4'))
      | ~ m1_pre_topc(B_425,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_264])).

tff(c_324,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_4'))
    | ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_321])).

tff(c_736,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitLeft,[status(thm)],[c_324])).

tff(c_745,plain,(
    ~ l1_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_736])).

tff(c_749,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_745])).

tff(c_751,plain,(
    m1_pre_topc('#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_324])).

tff(c_58,plain,(
    m1_pre_topc('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_165,plain,
    ( l1_pre_topc('#skF_3')
    | ~ l1_pre_topc('#skF_1') ),
    inference(resolution,[status(thm)],[c_58,c_159])).

tff(c_172,plain,(
    l1_pre_topc('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_165])).

tff(c_179,plain,(
    u1_struct_0('#skF_3') = k2_struct_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_172,c_100])).

tff(c_46,plain,(
    g1_pre_topc(u1_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_184,plain,(
    g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_46])).

tff(c_334,plain,(
    ! [B_426,A_427] :
      ( m1_pre_topc(B_426,A_427)
      | ~ m1_pre_topc(B_426,g1_pre_topc(u1_struct_0(A_427),u1_pre_topc(A_427)))
      | ~ l1_pre_topc(A_427) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_340,plain,(
    ! [B_426] :
      ( m1_pre_topc(B_426,'#skF_3')
      | ~ m1_pre_topc(B_426,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_334])).

tff(c_354,plain,(
    ! [B_426] :
      ( m1_pre_topc(B_426,'#skF_3')
      | ~ m1_pre_topc(B_426,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_184,c_340])).

tff(c_270,plain,(
    ! [B_421] :
      ( r1_tarski(u1_struct_0(B_421),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_421,'#skF_3')
      | ~ l1_pre_topc('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_258])).

tff(c_390,plain,(
    ! [B_431] :
      ( r1_tarski(u1_struct_0(B_431),k2_struct_0('#skF_3'))
      | ~ m1_pre_topc(B_431,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_270])).

tff(c_393,plain,
    ( r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_183,c_390])).

tff(c_777,plain,(
    ~ m1_pre_topc('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_780,plain,(
    ~ m1_pre_topc('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_354,c_777])).

tff(c_784,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_780])).

tff(c_785,plain,(
    r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_2,plain,(
    ! [A_1] : k2_subset_1(A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2] : m1_subset_1(k2_subset_1(A_2),k1_zfmisc_1(A_2)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [A_2] : m1_subset_1(A_2,k1_zfmisc_1(A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_4])).

tff(c_72,plain,(
    ~ v2_struct_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_66,plain,(
    ~ v2_struct_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_60,plain,(
    ~ v2_struct_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_36,plain,(
    ~ r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_64,plain,(
    v2_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_62,plain,(
    l1_pre_topc('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_52,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_101,plain,(
    ! [A_412] :
      ( u1_struct_0(A_412) = k2_struct_0(A_412)
      | ~ l1_pre_topc(A_412) ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_109,plain,(
    u1_struct_0('#skF_2') = k2_struct_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_101])).

tff(c_50,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),u1_struct_0('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_114,plain,(
    v1_funct_2('#skF_5',u1_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_50])).

tff(c_239,plain,(
    v1_funct_2('#skF_5',k2_struct_0('#skF_4'),k2_struct_0('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_114])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),u1_struct_0('#skF_2')))) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_143,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_48])).

tff(c_209,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'),k2_struct_0('#skF_2')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_183,c_143])).

tff(c_469,plain,(
    ! [A_436,B_437] :
      ( m1_pre_topc(A_436,g1_pre_topc(u1_struct_0(B_437),u1_pre_topc(B_437)))
      | ~ m1_pre_topc(A_436,B_437)
      | ~ l1_pre_topc(B_437)
      | ~ l1_pre_topc(A_436) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_490,plain,(
    ! [A_436] :
      ( m1_pre_topc(A_436,g1_pre_topc(k2_struct_0('#skF_3'),u1_pre_topc('#skF_3')))
      | ~ m1_pre_topc(A_436,'#skF_3')
      | ~ l1_pre_topc('#skF_3')
      | ~ l1_pre_topc(A_436) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_469])).

tff(c_512,plain,(
    ! [A_438] :
      ( m1_pre_topc(A_438,'#skF_4')
      | ~ m1_pre_topc(A_438,'#skF_3')
      | ~ l1_pre_topc(A_438) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_184,c_490])).

tff(c_519,plain,
    ( m1_pre_topc('#skF_3','#skF_4')
    | ~ l1_pre_topc('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_512])).

tff(c_523,plain,(
    m1_pre_topc('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_519])).

tff(c_40,plain,(
    '#skF_7' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',u1_struct_0('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_73,plain,(
    m1_subset_1('#skF_6',u1_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_42])).

tff(c_185,plain,(
    m1_subset_1('#skF_6',k2_struct_0('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_73])).

tff(c_38,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_218])).

tff(c_74,plain,(
    r1_tmap_1('#skF_3','#skF_2',k3_tmap_1('#skF_1','#skF_2','#skF_4','#skF_3','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_714,plain,(
    ! [A_448,H_453,F_454,D_450,E_449,B_452,C_451] :
      ( r1_tmap_1(D_450,B_452,E_449,H_453)
      | ~ r1_tmap_1(C_451,B_452,k3_tmap_1(A_448,B_452,D_450,C_451,E_449),H_453)
      | ~ r1_tarski(F_454,u1_struct_0(C_451))
      | ~ r2_hidden(H_453,F_454)
      | ~ v3_pre_topc(F_454,D_450)
      | ~ m1_subset_1(H_453,u1_struct_0(C_451))
      | ~ m1_subset_1(H_453,u1_struct_0(D_450))
      | ~ m1_subset_1(F_454,k1_zfmisc_1(u1_struct_0(D_450)))
      | ~ m1_pre_topc(C_451,D_450)
      | ~ m1_subset_1(E_449,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_450),u1_struct_0(B_452))))
      | ~ v1_funct_2(E_449,u1_struct_0(D_450),u1_struct_0(B_452))
      | ~ v1_funct_1(E_449)
      | ~ m1_pre_topc(D_450,A_448)
      | v2_struct_0(D_450)
      | ~ m1_pre_topc(C_451,A_448)
      | v2_struct_0(C_451)
      | ~ l1_pre_topc(B_452)
      | ~ v2_pre_topc(B_452)
      | v2_struct_0(B_452)
      | ~ l1_pre_topc(A_448)
      | ~ v2_pre_topc(A_448)
      | v2_struct_0(A_448) ) ),
    inference(cnfTransformation,[status(thm)],[f_169])).

tff(c_716,plain,(
    ! [F_454] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_454,u1_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_454)
      | ~ v3_pre_topc(F_454,'#skF_4')
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_3'))
      | ~ m1_subset_1('#skF_6',u1_struct_0('#skF_4'))
      | ~ m1_subset_1(F_454,k1_zfmisc_1(u1_struct_0('#skF_4')))
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
    inference(resolution,[status(thm)],[c_74,c_714])).

tff(c_719,plain,(
    ! [F_454] :
      ( r1_tmap_1('#skF_4','#skF_2','#skF_5','#skF_6')
      | ~ r1_tarski(F_454,k2_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_454)
      | ~ v3_pre_topc(F_454,'#skF_4')
      | ~ m1_subset_1(F_454,k1_zfmisc_1(k2_struct_0('#skF_4')))
      | v2_struct_0('#skF_4')
      | v2_struct_0('#skF_3')
      | v2_struct_0('#skF_2')
      | v2_struct_0('#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_68,c_64,c_62,c_58,c_54,c_52,c_239,c_109,c_183,c_209,c_109,c_183,c_523,c_183,c_210,c_183,c_185,c_179,c_179,c_716])).

tff(c_867,plain,(
    ! [F_457] :
      ( ~ r1_tarski(F_457,k2_struct_0('#skF_3'))
      | ~ r2_hidden('#skF_6',F_457)
      | ~ v3_pre_topc(F_457,'#skF_4')
      | ~ m1_subset_1(F_457,k1_zfmisc_1(k2_struct_0('#skF_4'))) ) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_66,c_60,c_56,c_36,c_719])).

tff(c_871,plain,
    ( ~ r1_tarski(k2_struct_0('#skF_4'),k2_struct_0('#skF_3'))
    | ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_75,c_867])).

tff(c_874,plain,
    ( ~ r2_hidden('#skF_6',k2_struct_0('#skF_4'))
    | ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_785,c_871])).

tff(c_875,plain,(
    ~ v3_pre_topc(k2_struct_0('#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_874])).

tff(c_878,plain,
    ( ~ l1_pre_topc('#skF_4')
    | ~ v2_pre_topc('#skF_4') ),
    inference(resolution,[status(thm)],[c_24,c_875])).

tff(c_882,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_257,c_175,c_878])).

tff(c_883,plain,(
    ~ r2_hidden('#skF_6',k2_struct_0('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_874])).

tff(c_887,plain,
    ( v1_xboole_0(k2_struct_0('#skF_4'))
    | ~ m1_subset_1('#skF_6',k2_struct_0('#skF_4')) ),
    inference(resolution,[status(thm)],[c_6,c_883])).

tff(c_890,plain,(
    v1_xboole_0(k2_struct_0('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_887])).

tff(c_892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_228,c_890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:26:44 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.60/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.70  
% 3.87/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.70  %$ r1_tmap_1 > v1_funct_2 > v3_pre_topc > r2_hidden > r1_tarski > m1_subset_1 > m1_pre_topc > v2_struct_0 > v2_pre_topc > v1_xboole_0 > v1_funct_1 > l1_struct_0 > l1_pre_topc > k3_tmap_1 > k2_zfmisc_1 > g1_pre_topc > #nlpp > u1_struct_0 > u1_pre_topc > k2_subset_1 > k2_struct_0 > k1_zfmisc_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.87/1.70  
% 3.87/1.70  %Foreground sorts:
% 3.87/1.70  
% 3.87/1.70  
% 3.87/1.70  %Background operators:
% 3.87/1.70  
% 3.87/1.70  
% 3.87/1.70  %Foreground operators:
% 3.87/1.70  tff(v2_struct_0, type, v2_struct_0: $i > $o).
% 3.87/1.70  tff(k3_tmap_1, type, k3_tmap_1: ($i * $i * $i * $i * $i) > $i).
% 3.87/1.70  tff(u1_pre_topc, type, u1_pre_topc: $i > $i).
% 3.87/1.70  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.87/1.70  tff(v3_pre_topc, type, v3_pre_topc: ($i * $i) > $o).
% 3.87/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.87/1.70  tff(g1_pre_topc, type, g1_pre_topc: ($i * $i) > $i).
% 3.87/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.87/1.70  tff(r1_tmap_1, type, r1_tmap_1: ($i * $i * $i * $i) > $o).
% 3.87/1.70  tff(l1_pre_topc, type, l1_pre_topc: $i > $o).
% 3.87/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.87/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.87/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.87/1.70  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.87/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.87/1.70  tff('#skF_2', type, '#skF_2': $i).
% 3.87/1.70  tff('#skF_3', type, '#skF_3': $i).
% 3.87/1.70  tff('#skF_1', type, '#skF_1': $i).
% 3.87/1.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.87/1.70  tff(l1_struct_0, type, l1_struct_0: $i > $o).
% 3.87/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.87/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.87/1.70  tff('#skF_4', type, '#skF_4': $i).
% 3.87/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.87/1.70  tff(m1_pre_topc, type, m1_pre_topc: ($i * $i) > $o).
% 3.87/1.70  tff(v2_pre_topc, type, v2_pre_topc: $i > $o).
% 3.87/1.70  tff(u1_struct_0, type, u1_struct_0: $i > $i).
% 3.87/1.70  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.87/1.70  tff(k2_struct_0, type, k2_struct_0: $i > $i).
% 3.87/1.70  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.87/1.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.87/1.70  
% 3.87/1.72  tff(f_218, negated_conjecture, ~(![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => ((g1_pre_topc(u1_struct_0(C), u1_pre_topc(C)) = D) => (![F]: (m1_subset_1(F, u1_struct_0(D)) => (![G]: (m1_subset_1(G, u1_struct_0(C)) => (((F = G) & r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), G)) => r1_tmap_1(D, B, E, F))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_tmap_1)).
% 3.87/1.72  tff(f_59, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => l1_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_m1_pre_topc)).
% 3.87/1.72  tff(f_52, axiom, (![A]: (l1_pre_topc(A) => l1_struct_0(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_l1_pre_topc)).
% 3.87/1.72  tff(f_48, axiom, (![A]: (l1_struct_0(A) => (k2_struct_0(A) = u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_struct_0)).
% 3.87/1.72  tff(f_67, axiom, (![A]: ((~v2_struct_0(A) & l1_struct_0(A)) => ~v1_xboole_0(u1_struct_0(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_struct_0)).
% 3.87/1.72  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.87/1.72  tff(f_44, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => (![B]: (m1_pre_topc(B, A) => v2_pre_topc(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_pre_topc)).
% 3.87/1.72  tff(f_89, axiom, (![A]: ((v2_pre_topc(A) & l1_pre_topc(A)) => v3_pre_topc(k2_struct_0(A), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_tops_1)).
% 3.87/1.72  tff(f_93, axiom, (![A]: (l1_pre_topc(A) => m1_pre_topc(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tsep_1)).
% 3.87/1.72  tff(f_100, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, A) => r1_tarski(u1_struct_0(B), u1_struct_0(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_borsuk_1)).
% 3.87/1.72  tff(f_74, axiom, (![A]: (l1_pre_topc(A) => (![B]: (m1_pre_topc(B, g1_pre_topc(u1_struct_0(A), u1_pre_topc(A))) => m1_pre_topc(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_pre_topc)).
% 3.87/1.72  tff(f_27, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.87/1.72  tff(f_29, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.87/1.72  tff(f_83, axiom, (![A]: (l1_pre_topc(A) => (![B]: (l1_pre_topc(B) => (m1_pre_topc(A, B) <=> m1_pre_topc(A, g1_pre_topc(u1_struct_0(B), u1_pre_topc(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_pre_topc)).
% 3.87/1.72  tff(f_169, axiom, (![A]: (((~v2_struct_0(A) & v2_pre_topc(A)) & l1_pre_topc(A)) => (![B]: (((~v2_struct_0(B) & v2_pre_topc(B)) & l1_pre_topc(B)) => (![C]: ((~v2_struct_0(C) & m1_pre_topc(C, A)) => (![D]: ((~v2_struct_0(D) & m1_pre_topc(D, A)) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, u1_struct_0(D), u1_struct_0(B))) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D), u1_struct_0(B))))) => (m1_pre_topc(C, D) => (![F]: (m1_subset_1(F, k1_zfmisc_1(u1_struct_0(D))) => (![G]: (m1_subset_1(G, u1_struct_0(D)) => (![H]: (m1_subset_1(H, u1_struct_0(C)) => ((((v3_pre_topc(F, D) & r2_hidden(G, F)) & r1_tarski(F, u1_struct_0(C))) & (G = H)) => (r1_tmap_1(D, B, E, G) <=> r1_tmap_1(C, B, k3_tmap_1(A, B, D, C, E), H)))))))))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t84_tmap_1)).
% 3.87/1.72  tff(c_68, plain, (l1_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_54, plain, (m1_pre_topc('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_159, plain, (![B_414, A_415]: (l1_pre_topc(B_414) | ~m1_pre_topc(B_414, A_415) | ~l1_pre_topc(A_415))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.87/1.72  tff(c_168, plain, (l1_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_159])).
% 3.87/1.72  tff(c_175, plain, (l1_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_168])).
% 3.87/1.72  tff(c_12, plain, (![A_9]: (l1_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.87/1.72  tff(c_56, plain, (~v2_struct_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_96, plain, (![A_411]: (u1_struct_0(A_411)=k2_struct_0(A_411) | ~l1_struct_0(A_411))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.87/1.72  tff(c_100, plain, (![A_9]: (u1_struct_0(A_9)=k2_struct_0(A_9) | ~l1_pre_topc(A_9))), inference(resolution, [status(thm)], [c_12, c_96])).
% 3.87/1.72  tff(c_183, plain, (u1_struct_0('#skF_4')=k2_struct_0('#skF_4')), inference(resolution, [status(thm)], [c_175, c_100])).
% 3.87/1.72  tff(c_16, plain, (![A_13]: (~v1_xboole_0(u1_struct_0(A_13)) | ~l1_struct_0(A_13) | v2_struct_0(A_13))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.87/1.72  tff(c_214, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4') | v2_struct_0('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_183, c_16])).
% 3.87/1.72  tff(c_217, plain, (~v1_xboole_0(k2_struct_0('#skF_4')) | ~l1_struct_0('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_56, c_214])).
% 3.87/1.72  tff(c_220, plain, (~l1_struct_0('#skF_4')), inference(splitLeft, [status(thm)], [c_217])).
% 3.87/1.72  tff(c_223, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_12, c_220])).
% 3.87/1.72  tff(c_227, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_223])).
% 3.87/1.72  tff(c_228, plain, (~v1_xboole_0(k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_217])).
% 3.87/1.72  tff(c_44, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_210, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_44])).
% 3.87/1.72  tff(c_6, plain, (![A_3, B_4]: (r2_hidden(A_3, B_4) | v1_xboole_0(B_4) | ~m1_subset_1(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.87/1.72  tff(c_70, plain, (v2_pre_topc('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_241, plain, (![B_419, A_420]: (v2_pre_topc(B_419) | ~m1_pre_topc(B_419, A_420) | ~l1_pre_topc(A_420) | ~v2_pre_topc(A_420))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.87/1.72  tff(c_250, plain, (v2_pre_topc('#skF_4') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_54, c_241])).
% 3.87/1.72  tff(c_257, plain, (v2_pre_topc('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_250])).
% 3.87/1.72  tff(c_24, plain, (![A_20]: (v3_pre_topc(k2_struct_0(A_20), A_20) | ~l1_pre_topc(A_20) | ~v2_pre_topc(A_20))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.87/1.72  tff(c_26, plain, (![A_21]: (m1_pre_topc(A_21, A_21) | ~l1_pre_topc(A_21))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.87/1.72  tff(c_258, plain, (![B_421, A_422]: (r1_tarski(u1_struct_0(B_421), u1_struct_0(A_422)) | ~m1_pre_topc(B_421, A_422) | ~l1_pre_topc(A_422))), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.87/1.72  tff(c_264, plain, (![B_421]: (r1_tarski(u1_struct_0(B_421), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_421, '#skF_4') | ~l1_pre_topc('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_183, c_258])).
% 3.87/1.72  tff(c_321, plain, (![B_425]: (r1_tarski(u1_struct_0(B_425), k2_struct_0('#skF_4')) | ~m1_pre_topc(B_425, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_264])).
% 3.87/1.72  tff(c_324, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_4')) | ~m1_pre_topc('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_183, c_321])).
% 3.87/1.72  tff(c_736, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(splitLeft, [status(thm)], [c_324])).
% 3.87/1.72  tff(c_745, plain, (~l1_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_26, c_736])).
% 3.87/1.72  tff(c_749, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_175, c_745])).
% 3.87/1.72  tff(c_751, plain, (m1_pre_topc('#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_324])).
% 3.87/1.72  tff(c_58, plain, (m1_pre_topc('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_165, plain, (l1_pre_topc('#skF_3') | ~l1_pre_topc('#skF_1')), inference(resolution, [status(thm)], [c_58, c_159])).
% 3.87/1.72  tff(c_172, plain, (l1_pre_topc('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_165])).
% 3.87/1.72  tff(c_179, plain, (u1_struct_0('#skF_3')=k2_struct_0('#skF_3')), inference(resolution, [status(thm)], [c_172, c_100])).
% 3.87/1.72  tff(c_46, plain, (g1_pre_topc(u1_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_184, plain, (g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_46])).
% 3.87/1.72  tff(c_334, plain, (![B_426, A_427]: (m1_pre_topc(B_426, A_427) | ~m1_pre_topc(B_426, g1_pre_topc(u1_struct_0(A_427), u1_pre_topc(A_427))) | ~l1_pre_topc(A_427))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.87/1.72  tff(c_340, plain, (![B_426]: (m1_pre_topc(B_426, '#skF_3') | ~m1_pre_topc(B_426, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_334])).
% 3.87/1.72  tff(c_354, plain, (![B_426]: (m1_pre_topc(B_426, '#skF_3') | ~m1_pre_topc(B_426, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_184, c_340])).
% 3.87/1.72  tff(c_270, plain, (![B_421]: (r1_tarski(u1_struct_0(B_421), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_421, '#skF_3') | ~l1_pre_topc('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_179, c_258])).
% 3.87/1.72  tff(c_390, plain, (![B_431]: (r1_tarski(u1_struct_0(B_431), k2_struct_0('#skF_3')) | ~m1_pre_topc(B_431, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_270])).
% 3.87/1.72  tff(c_393, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~m1_pre_topc('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_183, c_390])).
% 3.87/1.72  tff(c_777, plain, (~m1_pre_topc('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_393])).
% 3.87/1.72  tff(c_780, plain, (~m1_pre_topc('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_354, c_777])).
% 3.87/1.72  tff(c_784, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_751, c_780])).
% 3.87/1.72  tff(c_785, plain, (r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3'))), inference(splitRight, [status(thm)], [c_393])).
% 3.87/1.72  tff(c_2, plain, (![A_1]: (k2_subset_1(A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.87/1.72  tff(c_4, plain, (![A_2]: (m1_subset_1(k2_subset_1(A_2), k1_zfmisc_1(A_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.87/1.72  tff(c_75, plain, (![A_2]: (m1_subset_1(A_2, k1_zfmisc_1(A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_4])).
% 3.87/1.72  tff(c_72, plain, (~v2_struct_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_66, plain, (~v2_struct_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_60, plain, (~v2_struct_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_36, plain, (~r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_64, plain, (v2_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_62, plain, (l1_pre_topc('#skF_2')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_52, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_101, plain, (![A_412]: (u1_struct_0(A_412)=k2_struct_0(A_412) | ~l1_pre_topc(A_412))), inference(resolution, [status(thm)], [c_12, c_96])).
% 3.87/1.72  tff(c_109, plain, (u1_struct_0('#skF_2')=k2_struct_0('#skF_2')), inference(resolution, [status(thm)], [c_62, c_101])).
% 3.87/1.72  tff(c_50, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_114, plain, (v1_funct_2('#skF_5', u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_50])).
% 3.87/1.72  tff(c_239, plain, (v1_funct_2('#skF_5', k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_114])).
% 3.87/1.72  tff(c_48, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2'))))), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_143, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_48])).
% 3.87/1.72  tff(c_209, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k2_struct_0('#skF_4'), k2_struct_0('#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_183, c_143])).
% 3.87/1.72  tff(c_469, plain, (![A_436, B_437]: (m1_pre_topc(A_436, g1_pre_topc(u1_struct_0(B_437), u1_pre_topc(B_437))) | ~m1_pre_topc(A_436, B_437) | ~l1_pre_topc(B_437) | ~l1_pre_topc(A_436))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.87/1.72  tff(c_490, plain, (![A_436]: (m1_pre_topc(A_436, g1_pre_topc(k2_struct_0('#skF_3'), u1_pre_topc('#skF_3'))) | ~m1_pre_topc(A_436, '#skF_3') | ~l1_pre_topc('#skF_3') | ~l1_pre_topc(A_436))), inference(superposition, [status(thm), theory('equality')], [c_179, c_469])).
% 3.87/1.72  tff(c_512, plain, (![A_438]: (m1_pre_topc(A_438, '#skF_4') | ~m1_pre_topc(A_438, '#skF_3') | ~l1_pre_topc(A_438))), inference(demodulation, [status(thm), theory('equality')], [c_172, c_184, c_490])).
% 3.87/1.72  tff(c_519, plain, (m1_pre_topc('#skF_3', '#skF_4') | ~l1_pre_topc('#skF_3')), inference(resolution, [status(thm)], [c_26, c_512])).
% 3.87/1.72  tff(c_523, plain, (m1_pre_topc('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_172, c_519])).
% 3.87/1.72  tff(c_40, plain, ('#skF_7'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_42, plain, (m1_subset_1('#skF_7', u1_struct_0('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_73, plain, (m1_subset_1('#skF_6', u1_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_42])).
% 3.87/1.72  tff(c_185, plain, (m1_subset_1('#skF_6', k2_struct_0('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_73])).
% 3.87/1.72  tff(c_38, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_218])).
% 3.87/1.72  tff(c_74, plain, (r1_tmap_1('#skF_3', '#skF_2', k3_tmap_1('#skF_1', '#skF_2', '#skF_4', '#skF_3', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 3.87/1.72  tff(c_714, plain, (![A_448, H_453, F_454, D_450, E_449, B_452, C_451]: (r1_tmap_1(D_450, B_452, E_449, H_453) | ~r1_tmap_1(C_451, B_452, k3_tmap_1(A_448, B_452, D_450, C_451, E_449), H_453) | ~r1_tarski(F_454, u1_struct_0(C_451)) | ~r2_hidden(H_453, F_454) | ~v3_pre_topc(F_454, D_450) | ~m1_subset_1(H_453, u1_struct_0(C_451)) | ~m1_subset_1(H_453, u1_struct_0(D_450)) | ~m1_subset_1(F_454, k1_zfmisc_1(u1_struct_0(D_450))) | ~m1_pre_topc(C_451, D_450) | ~m1_subset_1(E_449, k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(D_450), u1_struct_0(B_452)))) | ~v1_funct_2(E_449, u1_struct_0(D_450), u1_struct_0(B_452)) | ~v1_funct_1(E_449) | ~m1_pre_topc(D_450, A_448) | v2_struct_0(D_450) | ~m1_pre_topc(C_451, A_448) | v2_struct_0(C_451) | ~l1_pre_topc(B_452) | ~v2_pre_topc(B_452) | v2_struct_0(B_452) | ~l1_pre_topc(A_448) | ~v2_pre_topc(A_448) | v2_struct_0(A_448))), inference(cnfTransformation, [status(thm)], [f_169])).
% 3.87/1.72  tff(c_716, plain, (![F_454]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_454, u1_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_454) | ~v3_pre_topc(F_454, '#skF_4') | ~m1_subset_1('#skF_6', u1_struct_0('#skF_3')) | ~m1_subset_1('#skF_6', u1_struct_0('#skF_4')) | ~m1_subset_1(F_454, k1_zfmisc_1(u1_struct_0('#skF_4'))) | ~m1_pre_topc('#skF_3', '#skF_4') | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(u1_struct_0('#skF_4'), u1_struct_0('#skF_2')))) | ~v1_funct_2('#skF_5', u1_struct_0('#skF_4'), u1_struct_0('#skF_2')) | ~v1_funct_1('#skF_5') | ~m1_pre_topc('#skF_4', '#skF_1') | v2_struct_0('#skF_4') | ~m1_pre_topc('#skF_3', '#skF_1') | v2_struct_0('#skF_3') | ~l1_pre_topc('#skF_2') | ~v2_pre_topc('#skF_2') | v2_struct_0('#skF_2') | ~l1_pre_topc('#skF_1') | ~v2_pre_topc('#skF_1') | v2_struct_0('#skF_1'))), inference(resolution, [status(thm)], [c_74, c_714])).
% 3.87/1.72  tff(c_719, plain, (![F_454]: (r1_tmap_1('#skF_4', '#skF_2', '#skF_5', '#skF_6') | ~r1_tarski(F_454, k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_454) | ~v3_pre_topc(F_454, '#skF_4') | ~m1_subset_1(F_454, k1_zfmisc_1(k2_struct_0('#skF_4'))) | v2_struct_0('#skF_4') | v2_struct_0('#skF_3') | v2_struct_0('#skF_2') | v2_struct_0('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_68, c_64, c_62, c_58, c_54, c_52, c_239, c_109, c_183, c_209, c_109, c_183, c_523, c_183, c_210, c_183, c_185, c_179, c_179, c_716])).
% 3.87/1.72  tff(c_867, plain, (![F_457]: (~r1_tarski(F_457, k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', F_457) | ~v3_pre_topc(F_457, '#skF_4') | ~m1_subset_1(F_457, k1_zfmisc_1(k2_struct_0('#skF_4'))))), inference(negUnitSimplification, [status(thm)], [c_72, c_66, c_60, c_56, c_36, c_719])).
% 3.87/1.72  tff(c_871, plain, (~r1_tarski(k2_struct_0('#skF_4'), k2_struct_0('#skF_3')) | ~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_75, c_867])).
% 3.87/1.72  tff(c_874, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4')) | ~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_785, c_871])).
% 3.87/1.72  tff(c_875, plain, (~v3_pre_topc(k2_struct_0('#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_874])).
% 3.87/1.72  tff(c_878, plain, (~l1_pre_topc('#skF_4') | ~v2_pre_topc('#skF_4')), inference(resolution, [status(thm)], [c_24, c_875])).
% 3.87/1.72  tff(c_882, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_257, c_175, c_878])).
% 3.87/1.72  tff(c_883, plain, (~r2_hidden('#skF_6', k2_struct_0('#skF_4'))), inference(splitRight, [status(thm)], [c_874])).
% 3.87/1.72  tff(c_887, plain, (v1_xboole_0(k2_struct_0('#skF_4')) | ~m1_subset_1('#skF_6', k2_struct_0('#skF_4'))), inference(resolution, [status(thm)], [c_6, c_883])).
% 3.87/1.72  tff(c_890, plain, (v1_xboole_0(k2_struct_0('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_887])).
% 3.87/1.72  tff(c_892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_228, c_890])).
% 3.87/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.87/1.72  
% 3.87/1.72  Inference rules
% 3.87/1.72  ----------------------
% 3.87/1.72  #Ref     : 0
% 3.87/1.72  #Sup     : 159
% 3.87/1.72  #Fact    : 0
% 3.87/1.72  #Define  : 0
% 3.87/1.72  #Split   : 17
% 3.87/1.72  #Chain   : 0
% 3.87/1.72  #Close   : 0
% 3.87/1.72  
% 3.87/1.72  Ordering : KBO
% 3.87/1.72  
% 3.87/1.72  Simplification rules
% 3.87/1.72  ----------------------
% 3.87/1.72  #Subsume      : 13
% 3.87/1.72  #Demod        : 180
% 3.87/1.72  #Tautology    : 59
% 3.87/1.72  #SimpNegUnit  : 10
% 3.87/1.72  #BackRed      : 5
% 3.87/1.72  
% 3.87/1.72  #Partial instantiations: 0
% 3.87/1.72  #Strategies tried      : 1
% 3.87/1.72  
% 3.87/1.72  Timing (in seconds)
% 3.87/1.72  ----------------------
% 3.87/1.73  Preprocessing        : 0.48
% 3.87/1.73  Parsing              : 0.24
% 3.87/1.73  CNF conversion       : 0.06
% 3.87/1.73  Main loop            : 0.40
% 3.87/1.73  Inferencing          : 0.13
% 3.87/1.73  Reduction            : 0.14
% 3.87/1.73  Demodulation         : 0.10
% 3.87/1.73  BG Simplification    : 0.02
% 3.87/1.73  Subsumption          : 0.07
% 3.87/1.73  Abstraction          : 0.01
% 3.87/1.73  MUC search           : 0.00
% 3.87/1.73  Cooper               : 0.00
% 3.87/1.73  Total                : 0.93
% 3.87/1.73  Index Insertion      : 0.00
% 3.87/1.73  Index Deletion       : 0.00
% 3.87/1.73  Index Matching       : 0.00
% 3.87/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
