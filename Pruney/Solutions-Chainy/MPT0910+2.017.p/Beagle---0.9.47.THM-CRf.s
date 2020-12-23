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
% DateTime   : Thu Dec  3 10:10:01 EST 2020

% Result     : Theorem 4.56s
% Output     : CNFRefutation 4.56s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 361 expanded)
%              Number of leaves         :   25 ( 151 expanded)
%              Depth                    :   18
%              Number of atoms          :  172 (2064 expanded)
%              Number of equality atoms :  128 (1364 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

tff(f_94,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
     => ( ! [F] :
            ( m1_subset_1(F,A)
           => ! [G] :
                ( m1_subset_1(G,B)
               => ! [H] :
                    ( m1_subset_1(H,C)
                   => ( E = k3_mcart_1(F,G,H)
                     => D = F ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [E,F,G] :
              ( D = k3_mcart_1(E,F,G)
              & ~ ( k5_mcart_1(A,B,C,D) = E
                  & k6_mcart_1(A,B,C,D) = F
                  & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_1'(A_22,C_24,E_26,D_25,B_23),A_22)
      | k5_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_3'(A_22,C_24,E_26,D_25,B_23),C_24)
      | k5_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_2'(A_22,C_24,E_26,D_25,B_23),B_23)
      | k5_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_289,plain,(
    ! [E_140,D_141,A_138,B_142,C_139] :
      ( k3_mcart_1('#skF_1'(A_138,C_139,E_140,D_141,B_142),'#skF_2'(A_138,C_139,E_140,D_141,B_142),'#skF_3'(A_138,C_139,E_140,D_141,B_142)) = E_140
      | k5_mcart_1(A_138,B_142,C_139,E_140) = D_141
      | k1_xboole_0 = C_139
      | k1_xboole_0 = B_142
      | k1_xboole_0 = A_138
      | ~ m1_subset_1(E_140,k3_zfmisc_1(A_138,B_142,C_139)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ! [G_49,F_45,H_51] :
      ( G_49 = '#skF_7'
      | k3_mcart_1(F_45,G_49,H_51) != '#skF_8'
      | ~ m1_subset_1(H_51,'#skF_6')
      | ~ m1_subset_1(G_49,'#skF_5')
      | ~ m1_subset_1(F_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_370,plain,(
    ! [B_180,C_181,D_178,A_179,E_182] :
      ( '#skF_2'(A_179,C_181,E_182,D_178,B_180) = '#skF_7'
      | E_182 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_179,C_181,E_182,D_178,B_180),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_179,C_181,E_182,D_178,B_180),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_179,C_181,E_182,D_178,B_180),'#skF_4')
      | k5_mcart_1(A_179,B_180,C_181,E_182) = D_178
      | k1_xboole_0 = C_181
      | k1_xboole_0 = B_180
      | k1_xboole_0 = A_179
      | ~ m1_subset_1(E_182,k3_zfmisc_1(A_179,B_180,C_181)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_36])).

tff(c_374,plain,(
    ! [A_22,C_24,E_26,D_25] :
      ( '#skF_2'(A_22,C_24,E_26,D_25,'#skF_5') = '#skF_7'
      | E_26 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_22,C_24,E_26,D_25,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_22,C_24,E_26,D_25,'#skF_5'),'#skF_4')
      | k5_mcart_1(A_22,'#skF_5',C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,'#skF_5',C_24)) ) ),
    inference(resolution,[status(thm)],[c_24,c_370])).

tff(c_414,plain,(
    ! [A_206,C_207,E_208,D_209] :
      ( '#skF_2'(A_206,C_207,E_208,D_209,'#skF_5') = '#skF_7'
      | E_208 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_206,C_207,E_208,D_209,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_206,C_207,E_208,D_209,'#skF_5'),'#skF_4')
      | k5_mcart_1(A_206,'#skF_5',C_207,E_208) = D_209
      | k1_xboole_0 = C_207
      | k1_xboole_0 = A_206
      | ~ m1_subset_1(E_208,k3_zfmisc_1(A_206,'#skF_5',C_207)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_374])).

tff(c_418,plain,(
    ! [A_22,E_26,D_25] :
      ( '#skF_2'(A_22,'#skF_6',E_26,D_25,'#skF_5') = '#skF_7'
      | E_26 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_22,'#skF_6',E_26,D_25,'#skF_5'),'#skF_4')
      | k5_mcart_1(A_22,'#skF_5','#skF_6',E_26) = D_25
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,'#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_22,c_414])).

tff(c_423,plain,(
    ! [A_210,E_211,D_212] :
      ( '#skF_2'(A_210,'#skF_6',E_211,D_212,'#skF_5') = '#skF_7'
      | E_211 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_210,'#skF_6',E_211,D_212,'#skF_5'),'#skF_4')
      | k5_mcart_1(A_210,'#skF_5','#skF_6',E_211) = D_212
      | k1_xboole_0 = A_210
      | ~ m1_subset_1(E_211,k3_zfmisc_1(A_210,'#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_30,c_418])).

tff(c_427,plain,(
    ! [E_26,D_25] :
      ( '#skF_2'('#skF_4','#skF_6',E_26,D_25,'#skF_5') = '#skF_7'
      | E_26 != '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6',E_26) = D_25
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(E_26,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_26,c_423])).

tff(c_432,plain,(
    ! [E_213,D_214] :
      ( '#skF_2'('#skF_4','#skF_6',E_213,D_214,'#skF_5') = '#skF_7'
      | E_213 != '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6',E_213) = D_214
      | ~ m1_subset_1(E_213,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_34,c_427])).

tff(c_450,plain,(
    ! [D_215] :
      ( '#skF_2'('#skF_4','#skF_6','#skF_8',D_215,'#skF_5') = '#skF_7'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215 ) ),
    inference(resolution,[status(thm)],[c_38,c_432])).

tff(c_20,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( k3_mcart_1('#skF_1'(A_22,C_24,E_26,D_25,B_23),'#skF_2'(A_22,C_24,E_26,D_25,B_23),'#skF_3'(A_22,C_24,E_26,D_25,B_23)) = E_26
      | k5_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_459,plain,(
    ! [D_215] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_215,'#skF_5'),'#skF_7','#skF_3'('#skF_4','#skF_6','#skF_8',D_215,'#skF_5')) = '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_450,c_20])).

tff(c_837,plain,(
    ! [D_215] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_215,'#skF_5'),'#skF_7','#skF_3'('#skF_4','#skF_6','#skF_8',D_215,'#skF_5')) = '#skF_8'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_459])).

tff(c_838,plain,(
    ! [D_215] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_215,'#skF_5'),'#skF_7','#skF_3'('#skF_4','#skF_6','#skF_8',D_215,'#skF_5')) = '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_837])).

tff(c_909,plain,(
    ! [D_2028] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_2028,'#skF_5'),'#skF_7','#skF_3'('#skF_4','#skF_6','#skF_8',D_2028,'#skF_5')) = '#skF_8'
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_2028 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_837])).

tff(c_14,plain,(
    ! [G_21,E_19,C_14,A_12,B_13,F_20] :
      ( k6_mcart_1(A_12,B_13,C_14,k3_mcart_1(E_19,F_20,G_21)) = F_20
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | ~ m1_subset_1(k3_mcart_1(E_19,F_20,G_21),k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1188,plain,(
    ! [A_2355,B_2356,C_2357,D_2358] :
      ( k6_mcart_1(A_2355,B_2356,C_2357,k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_2358,'#skF_5'),'#skF_7','#skF_3'('#skF_4','#skF_6','#skF_8',D_2358,'#skF_5'))) = '#skF_7'
      | k1_xboole_0 = C_2357
      | k1_xboole_0 = B_2356
      | k1_xboole_0 = A_2355
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_2355,B_2356,C_2357))
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_2358 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_14])).

tff(c_1197,plain,(
    ! [A_2355,B_2356,C_2357,D_215] :
      ( k6_mcart_1(A_2355,B_2356,C_2357,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_2357
      | k1_xboole_0 = B_2356
      | k1_xboole_0 = A_2355
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_2355,B_2356,C_2357))
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_1188])).

tff(c_1220,plain,(
    ! [D_215] :
      ( k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215
      | k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215 ) ),
    inference(splitLeft,[status(thm)],[c_1197])).

tff(c_2277,plain,(
    k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_6' ),
    inference(factorization,[status(thm),theory(equality)],[c_1220])).

tff(c_1241,plain,(
    ! [D_215] : k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_215 ),
    inference(factorization,[status(thm),theory(equality)],[c_1220])).

tff(c_2789,plain,(
    ! [D_8718] : D_8718 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2277,c_1241])).

tff(c_3090,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2789,c_30])).

tff(c_3092,plain,(
    ! [A_10786,B_10787,C_10788] :
      ( k6_mcart_1(A_10786,B_10787,C_10788,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_10788
      | k1_xboole_0 = B_10787
      | k1_xboole_0 = A_10786
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_10786,B_10787,C_10788)) ) ),
    inference(splitRight,[status(thm)],[c_1197])).

tff(c_3099,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_3092])).

tff(c_3103,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_28,c_3099])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:48:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.56/1.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.79  
% 4.56/1.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.80  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.56/1.80  
% 4.56/1.80  %Foreground sorts:
% 4.56/1.80  
% 4.56/1.80  
% 4.56/1.80  %Background operators:
% 4.56/1.80  
% 4.56/1.80  
% 4.56/1.80  %Foreground operators:
% 4.56/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.56/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.56/1.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.56/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.56/1.80  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.56/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.56/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.56/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.56/1.80  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.56/1.80  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.56/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 4.56/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 4.56/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.56/1.80  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.56/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.56/1.80  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.56/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.56/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.56/1.80  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.56/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.56/1.80  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.56/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.56/1.80  
% 4.56/1.81  tff(f_118, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_mcart_1)).
% 4.56/1.81  tff(f_94, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_mcart_1)).
% 4.56/1.81  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_mcart_1)).
% 4.56/1.81  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.56/1.81  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.56/1.81  tff(c_30, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.56/1.81  tff(c_28, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.56/1.81  tff(c_38, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.56/1.81  tff(c_26, plain, (![E_26, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_1'(A_22, C_24, E_26, D_25, B_23), A_22) | k5_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.81  tff(c_22, plain, (![E_26, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_3'(A_22, C_24, E_26, D_25, B_23), C_24) | k5_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.81  tff(c_24, plain, (![E_26, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_2'(A_22, C_24, E_26, D_25, B_23), B_23) | k5_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.81  tff(c_289, plain, (![E_140, D_141, A_138, B_142, C_139]: (k3_mcart_1('#skF_1'(A_138, C_139, E_140, D_141, B_142), '#skF_2'(A_138, C_139, E_140, D_141, B_142), '#skF_3'(A_138, C_139, E_140, D_141, B_142))=E_140 | k5_mcart_1(A_138, B_142, C_139, E_140)=D_141 | k1_xboole_0=C_139 | k1_xboole_0=B_142 | k1_xboole_0=A_138 | ~m1_subset_1(E_140, k3_zfmisc_1(A_138, B_142, C_139)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.81  tff(c_36, plain, (![G_49, F_45, H_51]: (G_49='#skF_7' | k3_mcart_1(F_45, G_49, H_51)!='#skF_8' | ~m1_subset_1(H_51, '#skF_6') | ~m1_subset_1(G_49, '#skF_5') | ~m1_subset_1(F_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.56/1.81  tff(c_370, plain, (![B_180, C_181, D_178, A_179, E_182]: ('#skF_2'(A_179, C_181, E_182, D_178, B_180)='#skF_7' | E_182!='#skF_8' | ~m1_subset_1('#skF_3'(A_179, C_181, E_182, D_178, B_180), '#skF_6') | ~m1_subset_1('#skF_2'(A_179, C_181, E_182, D_178, B_180), '#skF_5') | ~m1_subset_1('#skF_1'(A_179, C_181, E_182, D_178, B_180), '#skF_4') | k5_mcart_1(A_179, B_180, C_181, E_182)=D_178 | k1_xboole_0=C_181 | k1_xboole_0=B_180 | k1_xboole_0=A_179 | ~m1_subset_1(E_182, k3_zfmisc_1(A_179, B_180, C_181)))), inference(superposition, [status(thm), theory('equality')], [c_289, c_36])).
% 4.56/1.81  tff(c_374, plain, (![A_22, C_24, E_26, D_25]: ('#skF_2'(A_22, C_24, E_26, D_25, '#skF_5')='#skF_7' | E_26!='#skF_8' | ~m1_subset_1('#skF_3'(A_22, C_24, E_26, D_25, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'(A_22, C_24, E_26, D_25, '#skF_5'), '#skF_4') | k5_mcart_1(A_22, '#skF_5', C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0='#skF_5' | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, '#skF_5', C_24)))), inference(resolution, [status(thm)], [c_24, c_370])).
% 4.56/1.81  tff(c_414, plain, (![A_206, C_207, E_208, D_209]: ('#skF_2'(A_206, C_207, E_208, D_209, '#skF_5')='#skF_7' | E_208!='#skF_8' | ~m1_subset_1('#skF_3'(A_206, C_207, E_208, D_209, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'(A_206, C_207, E_208, D_209, '#skF_5'), '#skF_4') | k5_mcart_1(A_206, '#skF_5', C_207, E_208)=D_209 | k1_xboole_0=C_207 | k1_xboole_0=A_206 | ~m1_subset_1(E_208, k3_zfmisc_1(A_206, '#skF_5', C_207)))), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_374])).
% 4.56/1.81  tff(c_418, plain, (![A_22, E_26, D_25]: ('#skF_2'(A_22, '#skF_6', E_26, D_25, '#skF_5')='#skF_7' | E_26!='#skF_8' | ~m1_subset_1('#skF_1'(A_22, '#skF_6', E_26, D_25, '#skF_5'), '#skF_4') | k5_mcart_1(A_22, '#skF_5', '#skF_6', E_26)=D_25 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_22, c_414])).
% 4.56/1.81  tff(c_423, plain, (![A_210, E_211, D_212]: ('#skF_2'(A_210, '#skF_6', E_211, D_212, '#skF_5')='#skF_7' | E_211!='#skF_8' | ~m1_subset_1('#skF_1'(A_210, '#skF_6', E_211, D_212, '#skF_5'), '#skF_4') | k5_mcart_1(A_210, '#skF_5', '#skF_6', E_211)=D_212 | k1_xboole_0=A_210 | ~m1_subset_1(E_211, k3_zfmisc_1(A_210, '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_30, c_418])).
% 4.56/1.81  tff(c_427, plain, (![E_26, D_25]: ('#skF_2'('#skF_4', '#skF_6', E_26, D_25, '#skF_5')='#skF_7' | E_26!='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', E_26)=D_25 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1(E_26, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_26, c_423])).
% 4.56/1.81  tff(c_432, plain, (![E_213, D_214]: ('#skF_2'('#skF_4', '#skF_6', E_213, D_214, '#skF_5')='#skF_7' | E_213!='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', E_213)=D_214 | ~m1_subset_1(E_213, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_34, c_427])).
% 4.56/1.81  tff(c_450, plain, (![D_215]: ('#skF_2'('#skF_4', '#skF_6', '#skF_8', D_215, '#skF_5')='#skF_7' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215)), inference(resolution, [status(thm)], [c_38, c_432])).
% 4.56/1.81  tff(c_20, plain, (![E_26, A_22, B_23, D_25, C_24]: (k3_mcart_1('#skF_1'(A_22, C_24, E_26, D_25, B_23), '#skF_2'(A_22, C_24, E_26, D_25, B_23), '#skF_3'(A_22, C_24, E_26, D_25, B_23))=E_26 | k5_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.56/1.81  tff(c_459, plain, (![D_215]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_215, '#skF_5'), '#skF_7', '#skF_3'('#skF_4', '#skF_6', '#skF_8', D_215, '#skF_5'))='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215)), inference(superposition, [status(thm), theory('equality')], [c_450, c_20])).
% 4.56/1.81  tff(c_837, plain, (![D_215]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_215, '#skF_5'), '#skF_7', '#skF_3'('#skF_4', '#skF_6', '#skF_8', D_215, '#skF_5'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_459])).
% 4.56/1.81  tff(c_838, plain, (![D_215]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_215, '#skF_5'), '#skF_7', '#skF_3'('#skF_4', '#skF_6', '#skF_8', D_215, '#skF_5'))='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_837])).
% 4.56/1.81  tff(c_909, plain, (![D_2028]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_2028, '#skF_5'), '#skF_7', '#skF_3'('#skF_4', '#skF_6', '#skF_8', D_2028, '#skF_5'))='#skF_8' | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_2028)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_837])).
% 4.56/1.81  tff(c_14, plain, (![G_21, E_19, C_14, A_12, B_13, F_20]: (k6_mcart_1(A_12, B_13, C_14, k3_mcart_1(E_19, F_20, G_21))=F_20 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12 | ~m1_subset_1(k3_mcart_1(E_19, F_20, G_21), k3_zfmisc_1(A_12, B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.56/1.81  tff(c_1188, plain, (![A_2355, B_2356, C_2357, D_2358]: (k6_mcart_1(A_2355, B_2356, C_2357, k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_2358, '#skF_5'), '#skF_7', '#skF_3'('#skF_4', '#skF_6', '#skF_8', D_2358, '#skF_5')))='#skF_7' | k1_xboole_0=C_2357 | k1_xboole_0=B_2356 | k1_xboole_0=A_2355 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_2355, B_2356, C_2357)) | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_2358)), inference(superposition, [status(thm), theory('equality')], [c_909, c_14])).
% 4.56/1.81  tff(c_1197, plain, (![A_2355, B_2356, C_2357, D_215]: (k6_mcart_1(A_2355, B_2356, C_2357, '#skF_8')='#skF_7' | k1_xboole_0=C_2357 | k1_xboole_0=B_2356 | k1_xboole_0=A_2355 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_2355, B_2356, C_2357)) | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215 | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215)), inference(superposition, [status(thm), theory('equality')], [c_838, c_1188])).
% 4.56/1.81  tff(c_1220, plain, (![D_215]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215 | k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215)), inference(splitLeft, [status(thm)], [c_1197])).
% 4.56/1.81  tff(c_2277, plain, (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_6'), inference(factorization, [status(thm), theory('equality')], [c_1220])).
% 4.56/1.81  tff(c_1241, plain, (![D_215]: (k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_215)), inference(factorization, [status(thm), theory('equality')], [c_1220])).
% 4.56/1.81  tff(c_2789, plain, (![D_8718]: (D_8718='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2277, c_1241])).
% 4.56/1.81  tff(c_3090, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2789, c_30])).
% 4.56/1.81  tff(c_3092, plain, (![A_10786, B_10787, C_10788]: (k6_mcart_1(A_10786, B_10787, C_10788, '#skF_8')='#skF_7' | k1_xboole_0=C_10788 | k1_xboole_0=B_10787 | k1_xboole_0=A_10786 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_10786, B_10787, C_10788)))), inference(splitRight, [status(thm)], [c_1197])).
% 4.56/1.81  tff(c_3099, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_3092])).
% 4.56/1.81  tff(c_3103, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_28, c_3099])).
% 4.56/1.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.56/1.81  
% 4.56/1.81  Inference rules
% 4.56/1.81  ----------------------
% 4.56/1.81  #Ref     : 0
% 4.56/1.81  #Sup     : 422
% 4.56/1.81  #Fact    : 4
% 4.56/1.81  #Define  : 0
% 4.56/1.81  #Split   : 8
% 4.56/1.81  #Chain   : 0
% 4.56/1.81  #Close   : 0
% 4.56/1.81  
% 4.56/1.81  Ordering : KBO
% 4.56/1.81  
% 4.56/1.81  Simplification rules
% 4.56/1.81  ----------------------
% 4.56/1.81  #Subsume      : 48
% 4.56/1.81  #Demod        : 133
% 4.56/1.81  #Tautology    : 74
% 4.56/1.81  #SimpNegUnit  : 28
% 4.56/1.81  #BackRed      : 0
% 4.56/1.81  
% 4.56/1.81  #Partial instantiations: 3592
% 4.56/1.81  #Strategies tried      : 1
% 4.56/1.81  
% 4.56/1.81  Timing (in seconds)
% 4.56/1.81  ----------------------
% 4.56/1.81  Preprocessing        : 0.33
% 4.56/1.81  Parsing              : 0.17
% 4.56/1.81  CNF conversion       : 0.02
% 4.56/1.81  Main loop            : 0.72
% 4.56/1.81  Inferencing          : 0.34
% 4.56/1.81  Reduction            : 0.18
% 4.56/1.81  Demodulation         : 0.13
% 4.56/1.81  BG Simplification    : 0.04
% 4.69/1.81  Subsumption          : 0.11
% 4.69/1.81  Abstraction          : 0.05
% 4.69/1.81  MUC search           : 0.00
% 4.69/1.81  Cooper               : 0.00
% 4.69/1.81  Total                : 1.07
% 4.69/1.81  Index Insertion      : 0.00
% 4.69/1.81  Index Deletion       : 0.00
% 4.69/1.81  Index Matching       : 0.00
% 4.69/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
