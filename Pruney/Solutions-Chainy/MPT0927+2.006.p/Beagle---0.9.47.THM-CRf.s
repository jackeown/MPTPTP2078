%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:24 EST 2020

% Result     : Theorem 9.63s
% Output     : CNFRefutation 9.76s
% Verified   : 
% Statistics : Number of formulae       :  342 (1417 expanded)
%              Number of leaves         :   37 ( 463 expanded)
%              Depth                    :   14
%              Number of atoms          :  625 (4763 expanded)
%              Number of equality atoms :  235 (1799 expanded)
%              Maximal formula depth    :   20 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_109,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(A))
       => ! [F] :
            ( m1_subset_1(F,k1_zfmisc_1(B))
           => ! [G] :
                ( m1_subset_1(G,k1_zfmisc_1(C))
               => ! [H] :
                    ( m1_subset_1(H,k1_zfmisc_1(D))
                   => ! [I] :
                        ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
                       => ( r2_hidden(I,k4_zfmisc_1(E,F,G,H))
                         => ( r2_hidden(k8_mcart_1(A,B,C,D,I),E)
                            & r2_hidden(k9_mcart_1(A,B,C,D,I),F)
                            & r2_hidden(k10_mcart_1(A,B,C,D,I),G)
                            & r2_hidden(k11_mcart_1(A,B,C,D,I),H) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_34,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_84,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C)) )
     => m1_subset_1(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

tff(c_81,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_1'(A_66,B_67),A_66)
      | r1_tarski(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_89,plain,(
    ! [A_66] : r1_tarski(A_66,A_66) ),
    inference(resolution,[status(thm)],[c_81,c_4])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_53,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(A_59,B_60)
      | ~ m1_subset_1(A_59,k1_zfmisc_1(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_8,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_70,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(resolution,[status(thm)],[c_8,c_53])).

tff(c_40,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_71,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_36,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4776,plain,(
    ! [A_644,B_645,C_646,D_647] : k2_zfmisc_1(k3_zfmisc_1(A_644,B_645,C_646),D_647) = k4_zfmisc_1(A_644,B_645,C_646,D_647) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_22,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(k2_mcart_1(A_21),C_23)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4913,plain,(
    ! [C_674,D_678,A_675,B_676,A_677] :
      ( r2_hidden(k2_mcart_1(A_675),D_678)
      | ~ r2_hidden(A_675,k4_zfmisc_1(A_677,B_676,C_674,D_678)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4776,c_22])).

tff(c_4924,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_4913])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_73,plain,(
    r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_46,c_53])).

tff(c_38,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4824,plain,(
    ! [B_658,A_659,C_657,D_661,E_660] :
      ( k11_mcart_1(A_659,B_658,C_657,D_661,E_660) = k2_mcart_1(E_660)
      | ~ m1_subset_1(E_660,k4_zfmisc_1(A_659,B_658,C_657,D_661))
      | k1_xboole_0 = D_661
      | k1_xboole_0 = C_657
      | k1_xboole_0 = B_658
      | k1_xboole_0 = A_659 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4828,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_4824])).

tff(c_5021,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4828])).

tff(c_5025,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5021,c_70])).

tff(c_34,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_92,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_72,plain,(
    r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_252,plain,(
    ! [B_115,C_114,A_116,E_117,D_118] :
      ( k11_mcart_1(A_116,B_115,C_114,D_118,E_117) = k2_mcart_1(E_117)
      | ~ m1_subset_1(E_117,k4_zfmisc_1(A_116,B_115,C_114,D_118))
      | k1_xboole_0 = D_118
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_115
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_260,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_252])).

tff(c_329,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_260])).

tff(c_332,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_100,plain,(
    ! [C_71,B_72,A_73] :
      ( r2_hidden(C_71,B_72)
      | ~ r2_hidden(C_71,A_73)
      | ~ r1_tarski(A_73,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_584,plain,(
    ! [A_150,B_151,B_152] :
      ( r2_hidden('#skF_1'(A_150,B_151),B_152)
      | ~ r1_tarski(A_150,B_152)
      | r1_tarski(A_150,B_151) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_16,plain,(
    ! [B_13,A_12] :
      ( ~ r1_tarski(B_13,A_12)
      | ~ r2_hidden(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_735,plain,(
    ! [B_167,A_168,B_169] :
      ( ~ r1_tarski(B_167,'#skF_1'(A_168,B_169))
      | ~ r1_tarski(A_168,B_167)
      | r1_tarski(A_168,B_169) ) ),
    inference(resolution,[status(thm)],[c_584,c_16])).

tff(c_756,plain,(
    ! [A_170,B_171] :
      ( ~ r1_tarski(A_170,'#skF_2')
      | r1_tarski(A_170,B_171) ) ),
    inference(resolution,[status(thm)],[c_332,c_735])).

tff(c_777,plain,(
    ! [B_171] : r1_tarski('#skF_6',B_171) ),
    inference(resolution,[status(thm)],[c_73,c_756])).

tff(c_107,plain,(
    ! [A_74,B_75,C_76] :
      ( r2_hidden(k1_mcart_1(A_74),B_75)
      | ~ r2_hidden(A_74,k2_zfmisc_1(B_75,C_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1039,plain,(
    ! [B_212,C_213,B_214] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_212,C_213),B_214)),B_212)
      | r1_tarski(k2_zfmisc_1(B_212,C_213),B_214) ) ),
    inference(resolution,[status(thm)],[c_6,c_107])).

tff(c_1232,plain,(
    ! [B_235,C_236,B_237] :
      ( ~ r1_tarski(B_235,k1_mcart_1('#skF_1'(k2_zfmisc_1(B_235,C_236),B_237)))
      | r1_tarski(k2_zfmisc_1(B_235,C_236),B_237) ) ),
    inference(resolution,[status(thm)],[c_1039,c_16])).

tff(c_1327,plain,(
    ! [C_242,B_243] : r1_tarski(k2_zfmisc_1('#skF_6',C_242),B_243) ),
    inference(resolution,[status(thm)],[c_777,c_1232])).

tff(c_1111,plain,(
    ! [B_212,C_213,B_214] :
      ( ~ r1_tarski(B_212,k1_mcart_1('#skF_1'(k2_zfmisc_1(B_212,C_213),B_214)))
      | r1_tarski(k2_zfmisc_1(B_212,C_213),B_214) ) ),
    inference(resolution,[status(thm)],[c_1039,c_16])).

tff(c_1331,plain,(
    ! [C_242,C_213,B_214] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1('#skF_6',C_242),C_213),B_214) ),
    inference(resolution,[status(thm)],[c_1327,c_1111])).

tff(c_1363,plain,(
    ! [C_242,C_213,B_214] : r1_tarski(k3_zfmisc_1('#skF_6',C_242,C_213),B_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1331])).

tff(c_188,plain,(
    ! [A_95,B_96,C_97,D_98] : k2_zfmisc_1(k3_zfmisc_1(A_95,B_96,C_97),D_98) = k4_zfmisc_1(A_95,B_96,C_97,D_98) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1579,plain,(
    ! [C_277,B_279,A_278,D_280,A_276] :
      ( r2_hidden(k1_mcart_1(A_276),k3_zfmisc_1(A_278,B_279,C_277))
      | ~ r2_hidden(A_276,k4_zfmisc_1(A_278,B_279,C_277,D_280)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_24])).

tff(c_1606,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_1579])).

tff(c_1617,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_mcart_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_1606,c_16])).

tff(c_1629,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1363,c_1617])).

tff(c_1631,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_260])).

tff(c_1636,plain,(
    ! [D_285,A_283,C_281,E_284,B_282] :
      ( k2_mcart_1(k1_mcart_1(E_284)) = k10_mcart_1(A_283,B_282,C_281,D_285,E_284)
      | ~ m1_subset_1(E_284,k4_zfmisc_1(A_283,B_282,C_281,D_285))
      | k1_xboole_0 = D_285
      | k1_xboole_0 = C_281
      | k1_xboole_0 = B_282
      | k1_xboole_0 = A_283 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1646,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_1636])).

tff(c_1651,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1631,c_1646])).

tff(c_1885,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1651])).

tff(c_1894,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1885,c_70])).

tff(c_1957,plain,(
    ! [A_314,B_315,B_316] :
      ( r2_hidden('#skF_1'(A_314,B_315),B_316)
      | ~ r1_tarski(A_314,B_316)
      | r1_tarski(A_314,B_315) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_2086,plain,(
    ! [B_330,A_331,B_332] :
      ( ~ r1_tarski(B_330,'#skF_1'(A_331,B_332))
      | ~ r1_tarski(A_331,B_330)
      | r1_tarski(A_331,B_332) ) ),
    inference(resolution,[status(thm)],[c_1957,c_16])).

tff(c_2107,plain,(
    ! [A_333,B_334] :
      ( ~ r1_tarski(A_333,'#skF_3')
      | r1_tarski(A_333,B_334) ) ),
    inference(resolution,[status(thm)],[c_1894,c_2086])).

tff(c_2128,plain,(
    ! [B_334] : r1_tarski('#skF_7',B_334) ),
    inference(resolution,[status(thm)],[c_72,c_2107])).

tff(c_2713,plain,(
    ! [D_416,B_415,C_413,A_414,A_412] :
      ( r2_hidden(k1_mcart_1(A_412),k3_zfmisc_1(A_414,B_415,C_413))
      | ~ r2_hidden(A_412,k4_zfmisc_1(A_414,B_415,C_413,D_416)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_24])).

tff(c_2740,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_2713])).

tff(c_112,plain,(
    ! [A_77,B_78,C_79] : k2_zfmisc_1(k2_zfmisc_1(A_77,B_78),C_79) = k3_zfmisc_1(A_77,B_78,C_79) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_120,plain,(
    ! [A_21,A_77,B_78,C_79] :
      ( r2_hidden(k1_mcart_1(A_21),k2_zfmisc_1(A_77,B_78))
      | ~ r2_hidden(A_21,k3_zfmisc_1(A_77,B_78,C_79)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_24])).

tff(c_2853,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2740,c_120])).

tff(c_2920,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_2853,c_22])).

tff(c_3000,plain,(
    ~ r1_tarski('#skF_7',k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))) ),
    inference(resolution,[status(thm)],[c_2920,c_16])).

tff(c_3011,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2128,c_3000])).

tff(c_3013,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1651])).

tff(c_1737,plain,(
    ! [D_296,B_293,A_294,C_292,E_295] :
      ( k8_mcart_1(A_294,B_293,C_292,D_296,E_295) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_295)))
      | ~ m1_subset_1(E_295,k4_zfmisc_1(A_294,B_293,C_292,D_296))
      | k1_xboole_0 = D_296
      | k1_xboole_0 = C_292
      | k1_xboole_0 = B_293
      | k1_xboole_0 = A_294 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1744,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_1737])).

tff(c_1749,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1631,c_1744])).

tff(c_3279,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_3013,c_1749])).

tff(c_3280,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3279])).

tff(c_3299,plain,(
    ! [A_483] : r1_tarski('#skF_4',A_483) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3280,c_70])).

tff(c_3029,plain,(
    ! [A_443,B_444,B_445] :
      ( r2_hidden('#skF_1'(A_443,B_444),B_445)
      | ~ r1_tarski(A_443,B_445)
      | r1_tarski(A_443,B_444) ) ),
    inference(resolution,[status(thm)],[c_6,c_100])).

tff(c_3084,plain,(
    ! [B_445,A_443,B_444] :
      ( ~ r1_tarski(B_445,'#skF_1'(A_443,B_444))
      | ~ r1_tarski(A_443,B_445)
      | r1_tarski(A_443,B_444) ) ),
    inference(resolution,[status(thm)],[c_3029,c_16])).

tff(c_3362,plain,(
    ! [A_487,B_488] :
      ( ~ r1_tarski(A_487,'#skF_4')
      | r1_tarski(A_487,B_488) ) ),
    inference(resolution,[status(thm)],[c_3299,c_3084])).

tff(c_3383,plain,(
    ! [B_488] : r1_tarski('#skF_8',B_488) ),
    inference(resolution,[status(thm)],[c_69,c_3362])).

tff(c_4097,plain,(
    ! [B_573,C_571,A_570,D_574,A_572] :
      ( r2_hidden(k1_mcart_1(A_570),k3_zfmisc_1(A_572,B_573,C_571))
      | ~ r2_hidden(A_570,k4_zfmisc_1(A_572,B_573,C_571,D_574)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_24])).

tff(c_4124,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_4097])).

tff(c_129,plain,(
    ! [A_80,C_81,B_82] :
      ( r2_hidden(k2_mcart_1(A_80),C_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_82,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_131,plain,(
    ! [A_80,C_16,A_14,B_15] :
      ( r2_hidden(k2_mcart_1(A_80),C_16)
      | ~ r2_hidden(A_80,k3_zfmisc_1(A_14,B_15,C_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_129])).

tff(c_4137,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_4124,c_131])).

tff(c_4150,plain,(
    ~ r1_tarski('#skF_8',k2_mcart_1(k1_mcart_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_4137,c_16])).

tff(c_4161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3383,c_4150])).

tff(c_4163,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3279])).

tff(c_1845,plain,(
    ! [B_301,D_304,E_303,C_300,A_302] :
      ( k9_mcart_1(A_302,B_301,C_300,D_304,E_303) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_303)))
      | ~ m1_subset_1(E_303,k4_zfmisc_1(A_302,B_301,C_300,D_304))
      | k1_xboole_0 = D_304
      | k1_xboole_0 = C_300
      | k1_xboole_0 = B_301
      | k1_xboole_0 = A_302 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1855,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_1845])).

tff(c_1861,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1631,c_1855])).

tff(c_4164,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_3013,c_4163,c_1861])).

tff(c_4165,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_4164])).

tff(c_230,plain,(
    ! [C_110,A_109,A_111,D_113,B_112] :
      ( r2_hidden(k2_mcart_1(A_109),D_113)
      | ~ r2_hidden(A_109,k4_zfmisc_1(A_111,B_112,C_110,D_113)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_22])).

tff(c_237,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_230])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_261,plain,(
    ! [B_119] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_119)
      | ~ r1_tarski('#skF_9',B_119) ) ),
    inference(resolution,[status(thm)],[c_237,c_2])).

tff(c_1703,plain,(
    ! [B_290,B_291] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_290)
      | ~ r1_tarski(B_291,B_290)
      | ~ r1_tarski('#skF_9',B_291) ) ),
    inference(resolution,[status(thm)],[c_261,c_2])).

tff(c_1715,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_71,c_1703])).

tff(c_1725,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_1715])).

tff(c_1774,plain,(
    ! [B_298] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_298)
      | ~ r1_tarski('#skF_5',B_298) ) ),
    inference(resolution,[status(thm)],[c_1725,c_2])).

tff(c_136,plain,(
    ! [A_83,C_84,B_85] :
      ( m1_subset_1(A_83,C_84)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(C_84))
      | ~ r2_hidden(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_151,plain,(
    ! [A_83,A_6] :
      ( m1_subset_1(A_83,A_6)
      | ~ r2_hidden(A_83,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_136])).

tff(c_1816,plain,(
    ! [A_6] :
      ( m1_subset_1(k2_mcart_1('#skF_10'),A_6)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1774,c_151])).

tff(c_1826,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1816])).

tff(c_4172,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4165,c_1826])).

tff(c_4183,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_4172])).

tff(c_4185,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_4164])).

tff(c_4162,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_3279])).

tff(c_4191,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_4185,c_4162])).

tff(c_4527,plain,(
    ! [A_615,C_614,B_616,D_617,A_613] :
      ( r2_hidden(k1_mcart_1(A_613),k3_zfmisc_1(A_615,B_616,C_614))
      | ~ r2_hidden(A_613,k4_zfmisc_1(A_615,B_616,C_614,D_617)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_188,c_24])).

tff(c_4554,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_4527])).

tff(c_4613,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_4554,c_120])).

tff(c_4624,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_4613,c_24])).

tff(c_4634,plain,(
    r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4191,c_4624])).

tff(c_4636,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_4634])).

tff(c_4638,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1816])).

tff(c_312,plain,(
    ! [B_2,B_119] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2)
      | ~ r1_tarski(B_119,B_2)
      | ~ r1_tarski('#skF_9',B_119) ) ),
    inference(resolution,[status(thm)],[c_261,c_2])).

tff(c_4640,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),k1_xboole_0)
    | ~ r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_4638,c_312])).

tff(c_4645,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_4640])).

tff(c_4685,plain,(
    ~ r1_tarski(k1_xboole_0,k2_mcart_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_4645,c_16])).

tff(c_4697,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_4685])).

tff(c_4699,plain,(
    r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4741,plain,(
    ! [C_637,B_638,A_639] :
      ( r2_hidden(C_637,B_638)
      | ~ r2_hidden(C_637,A_639)
      | ~ r1_tarski(A_639,B_638) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_5115,plain,(
    ! [B_702] :
      ( r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),B_702)
      | ~ r1_tarski('#skF_6',B_702) ) ),
    inference(resolution,[status(thm)],[c_4699,c_4741])).

tff(c_5527,plain,(
    ! [B_738] :
      ( ~ r1_tarski(B_738,k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
      | ~ r1_tarski('#skF_6',B_738) ) ),
    inference(resolution,[status(thm)],[c_5115,c_16])).

tff(c_5543,plain,(
    ~ r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_5025,c_5527])).

tff(c_5554,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_5543])).

tff(c_5556,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4828])).

tff(c_4939,plain,(
    ! [A_681,B_680,D_683,E_682,C_679] :
      ( k2_mcart_1(k1_mcart_1(E_682)) = k10_mcart_1(A_681,B_680,C_679,D_683,E_682)
      | ~ m1_subset_1(E_682,k4_zfmisc_1(A_681,B_680,C_679,D_683))
      | k1_xboole_0 = D_683
      | k1_xboole_0 = C_679
      | k1_xboole_0 = B_680
      | k1_xboole_0 = A_681 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4947,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_4939])).

tff(c_5569,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_5556,c_4947])).

tff(c_5570,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_5569])).

tff(c_5576,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5570,c_70])).

tff(c_4861,plain,(
    ! [A_671,B_672,B_673] :
      ( r2_hidden('#skF_1'(A_671,B_672),B_673)
      | ~ r1_tarski(A_671,B_673)
      | r1_tarski(A_671,B_672) ) ),
    inference(resolution,[status(thm)],[c_6,c_4741])).

tff(c_6005,plain,(
    ! [B_787,A_788,B_789] :
      ( ~ r1_tarski(B_787,'#skF_1'(A_788,B_789))
      | ~ r1_tarski(A_788,B_787)
      | r1_tarski(A_788,B_789) ) ),
    inference(resolution,[status(thm)],[c_4861,c_16])).

tff(c_6027,plain,(
    ! [A_790,B_791] :
      ( ~ r1_tarski(A_790,'#skF_3')
      | r1_tarski(A_790,B_791) ) ),
    inference(resolution,[status(thm)],[c_5576,c_6005])).

tff(c_6048,plain,(
    ! [B_791] : r1_tarski('#skF_7',B_791) ),
    inference(resolution,[status(thm)],[c_72,c_6027])).

tff(c_6557,plain,(
    ! [D_847,A_846,B_845,C_843,A_844] :
      ( r2_hidden(k1_mcart_1(A_844),k3_zfmisc_1(A_846,B_845,C_843))
      | ~ r2_hidden(A_844,k4_zfmisc_1(A_846,B_845,C_843,D_847)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4776,c_24])).

tff(c_6588,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_6557])).

tff(c_4722,plain,(
    ! [A_634,B_635,C_636] : k2_zfmisc_1(k2_zfmisc_1(A_634,B_635),C_636) = k3_zfmisc_1(A_634,B_635,C_636) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4732,plain,(
    ! [A_21,A_634,B_635,C_636] :
      ( r2_hidden(k1_mcart_1(A_21),k2_zfmisc_1(A_634,B_635))
      | ~ r2_hidden(A_21,k3_zfmisc_1(A_634,B_635,C_636)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4722,c_24])).

tff(c_6600,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_6588,c_4732])).

tff(c_6632,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_6600,c_22])).

tff(c_6644,plain,(
    ~ r1_tarski('#skF_7',k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))) ),
    inference(resolution,[status(thm)],[c_6632,c_16])).

tff(c_6655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6048,c_6644])).

tff(c_6657,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_5569])).

tff(c_5557,plain,(
    ! [C_739,A_741,B_740,D_743,E_742] :
      ( k9_mcart_1(A_741,B_740,C_739,D_743,E_742) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_742)))
      | ~ m1_subset_1(E_742,k4_zfmisc_1(A_741,B_740,C_739,D_743))
      | k1_xboole_0 = D_743
      | k1_xboole_0 = C_739
      | k1_xboole_0 = B_740
      | k1_xboole_0 = A_741 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_5567,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_5557])).

tff(c_6674,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5556,c_6657,c_5567])).

tff(c_6675,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6674])).

tff(c_6683,plain,(
    ! [A_6] : r1_tarski('#skF_4',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6675,c_70])).

tff(c_7124,plain,(
    ! [B_901,A_902,B_903] :
      ( ~ r1_tarski(B_901,'#skF_1'(A_902,B_903))
      | ~ r1_tarski(A_902,B_901)
      | r1_tarski(A_902,B_903) ) ),
    inference(resolution,[status(thm)],[c_4861,c_16])).

tff(c_7145,plain,(
    ! [A_904,B_905] :
      ( ~ r1_tarski(A_904,'#skF_4')
      | r1_tarski(A_904,B_905) ) ),
    inference(resolution,[status(thm)],[c_6683,c_7124])).

tff(c_7166,plain,(
    ! [B_905] : r1_tarski('#skF_8',B_905) ),
    inference(resolution,[status(thm)],[c_69,c_7145])).

tff(c_7639,plain,(
    ! [D_962,B_960,A_961,A_959,C_958] :
      ( r2_hidden(k1_mcart_1(A_959),k3_zfmisc_1(A_961,B_960,C_958))
      | ~ r2_hidden(A_959,k4_zfmisc_1(A_961,B_960,C_958,D_962)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4776,c_24])).

tff(c_7670,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_7639])).

tff(c_4730,plain,(
    ! [A_21,C_636,A_634,B_635] :
      ( r2_hidden(k2_mcart_1(A_21),C_636)
      | ~ r2_hidden(A_21,k3_zfmisc_1(A_634,B_635,C_636)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4722,c_22])).

tff(c_7683,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_7670,c_4730])).

tff(c_7696,plain,(
    ~ r1_tarski('#skF_8',k2_mcart_1(k1_mcart_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_7683,c_16])).

tff(c_7707,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_7166,c_7696])).

tff(c_7709,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6674])).

tff(c_6659,plain,(
    ! [A_850,E_851,B_849,D_852,C_848] :
      ( k8_mcart_1(A_850,B_849,C_848,D_852,E_851) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_851)))
      | ~ m1_subset_1(E_851,k4_zfmisc_1(A_850,B_849,C_848,D_852))
      | k1_xboole_0 = D_852
      | k1_xboole_0 = C_848
      | k1_xboole_0 = B_849
      | k1_xboole_0 = A_850 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_6666,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_6659])).

tff(c_6671,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5556,c_6657,c_6666])).

tff(c_8594,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_7709,c_6671])).

tff(c_8595,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_8594])).

tff(c_4968,plain,(
    ! [B_685] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_685)
      | ~ r1_tarski('#skF_9',B_685) ) ),
    inference(resolution,[status(thm)],[c_4924,c_2])).

tff(c_7785,plain,(
    ! [B_966,B_967] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_966)
      | ~ r1_tarski(B_967,B_966)
      | ~ r1_tarski('#skF_9',B_967) ) ),
    inference(resolution,[status(thm)],[c_4968,c_2])).

tff(c_7797,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_71,c_7785])).

tff(c_7807,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_7797])).

tff(c_7840,plain,(
    ! [B_972] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_972)
      | ~ r1_tarski('#skF_5',B_972) ) ),
    inference(resolution,[status(thm)],[c_7807,c_2])).

tff(c_4751,plain,(
    ! [A_640,C_641,B_642] :
      ( m1_subset_1(A_640,C_641)
      | ~ m1_subset_1(B_642,k1_zfmisc_1(C_641))
      | ~ r2_hidden(A_640,B_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_4766,plain,(
    ! [A_640,A_6] :
      ( m1_subset_1(A_640,A_6)
      | ~ r2_hidden(A_640,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_4751])).

tff(c_7886,plain,(
    ! [A_6] :
      ( m1_subset_1(k2_mcart_1('#skF_10'),A_6)
      | ~ r1_tarski('#skF_5',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_7840,c_4766])).

tff(c_7922,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_7886])).

tff(c_8602,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8595,c_7922])).

tff(c_8616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_8602])).

tff(c_8618,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_8594])).

tff(c_5555,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_4828])).

tff(c_8924,plain,(
    k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_8618,c_7709,c_6657,c_5555])).

tff(c_4698,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_4721,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_4698])).

tff(c_8925,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8924,c_4721])).

tff(c_8928,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4924,c_8925])).

tff(c_8930,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_7886])).

tff(c_5017,plain,(
    ! [B_2,B_685] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_2)
      | ~ r1_tarski(B_685,B_2)
      | ~ r1_tarski('#skF_9',B_685) ) ),
    inference(resolution,[status(thm)],[c_4968,c_2])).

tff(c_8932,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),k1_xboole_0)
    | ~ r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_8930,c_5017])).

tff(c_8935,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_8932])).

tff(c_8975,plain,(
    ~ r1_tarski(k1_xboole_0,k2_mcart_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_8935,c_16])).

tff(c_8987,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8975])).

tff(c_8988,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4698])).

tff(c_9102,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_8988])).

tff(c_9236,plain,(
    ! [D_1137,E_1136,B_1134,C_1133,A_1135] :
      ( k11_mcart_1(A_1135,B_1134,C_1133,D_1137,E_1136) = k2_mcart_1(E_1136)
      | ~ m1_subset_1(E_1136,k4_zfmisc_1(A_1135,B_1134,C_1133,D_1137))
      | k1_xboole_0 = D_1137
      | k1_xboole_0 = C_1133
      | k1_xboole_0 = B_1134
      | k1_xboole_0 = A_1135 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_9244,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_9236])).

tff(c_9275,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_9244])).

tff(c_9278,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9275,c_70])).

tff(c_8994,plain,(
    ! [C_1097,B_1098,A_1099] :
      ( r2_hidden(C_1097,B_1098)
      | ~ r2_hidden(C_1097,A_1099)
      | ~ r1_tarski(A_1099,B_1098) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_9135,plain,(
    ! [B_1129] :
      ( r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),B_1129)
      | ~ r1_tarski('#skF_6',B_1129) ) ),
    inference(resolution,[status(thm)],[c_4699,c_8994])).

tff(c_10435,plain,(
    ! [B_1257] :
      ( ~ r1_tarski(B_1257,k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
      | ~ r1_tarski('#skF_6',B_1257) ) ),
    inference(resolution,[status(thm)],[c_9135,c_16])).

tff(c_10451,plain,(
    ~ r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_9278,c_10435])).

tff(c_10462,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_10451])).

tff(c_10464,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_9244])).

tff(c_10535,plain,(
    ! [A_1262,B_1261,E_1263,C_1260,D_1264] :
      ( k2_mcart_1(k1_mcart_1(E_1263)) = k10_mcart_1(A_1262,B_1261,C_1260,D_1264,E_1263)
      | ~ m1_subset_1(E_1263,k4_zfmisc_1(A_1262,B_1261,C_1260,D_1264))
      | k1_xboole_0 = D_1264
      | k1_xboole_0 = C_1260
      | k1_xboole_0 = B_1261
      | k1_xboole_0 = A_1262 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10545,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_10535])).

tff(c_10550,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_10464,c_10545])).

tff(c_11821,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_10550])).

tff(c_9184,plain,(
    ! [A_1130,B_1131,B_1132] :
      ( r2_hidden('#skF_1'(A_1130,B_1131),B_1132)
      | ~ r1_tarski(A_1130,B_1132)
      | r1_tarski(A_1130,B_1131) ) ),
    inference(resolution,[status(thm)],[c_6,c_8994])).

tff(c_11028,plain,(
    ! [B_1314,A_1315,B_1316] :
      ( ~ r1_tarski(B_1314,'#skF_1'(A_1315,B_1316))
      | ~ r1_tarski(A_1315,B_1314)
      | r1_tarski(A_1315,B_1316) ) ),
    inference(resolution,[status(thm)],[c_9184,c_16])).

tff(c_11048,plain,(
    ! [A_1315,B_1316] :
      ( ~ r1_tarski(A_1315,k1_xboole_0)
      | r1_tarski(A_1315,B_1316) ) ),
    inference(resolution,[status(thm)],[c_70,c_11028])).

tff(c_11934,plain,(
    ! [A_1391,B_1392] :
      ( ~ r1_tarski(A_1391,'#skF_3')
      | r1_tarski(A_1391,B_1392) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11821,c_11048])).

tff(c_11963,plain,(
    ! [B_1392] : r1_tarski('#skF_7',B_1392) ),
    inference(resolution,[status(thm)],[c_72,c_11934])).

tff(c_9051,plain,(
    ! [A_1107,B_1108,C_1109,D_1110] : k2_zfmisc_1(k3_zfmisc_1(A_1107,B_1108,C_1109),D_1110) = k4_zfmisc_1(A_1107,B_1108,C_1109,D_1110) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_11517,plain,(
    ! [B_1377,A_1376,D_1374,A_1378,C_1375] :
      ( r2_hidden(k1_mcart_1(A_1376),k3_zfmisc_1(A_1378,B_1377,C_1375))
      | ~ r2_hidden(A_1376,k4_zfmisc_1(A_1378,B_1377,C_1375,D_1374)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9051,c_24])).

tff(c_11548,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_11517])).

tff(c_9007,plain,(
    ! [A_1100,B_1101,C_1102] : k2_zfmisc_1(k2_zfmisc_1(A_1100,B_1101),C_1102) = k3_zfmisc_1(A_1100,B_1101,C_1102) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_9017,plain,(
    ! [A_21,A_1100,B_1101,C_1102] :
      ( r2_hidden(k1_mcart_1(A_21),k2_zfmisc_1(A_1100,B_1101))
      | ~ r2_hidden(A_21,k3_zfmisc_1(A_1100,B_1101,C_1102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9007,c_24])).

tff(c_11560,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_11548,c_9017])).

tff(c_11592,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_11560,c_22])).

tff(c_11608,plain,(
    ~ r1_tarski('#skF_7',k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))) ),
    inference(resolution,[status(thm)],[c_11592,c_16])).

tff(c_11968,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11963,c_11608])).

tff(c_11970,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_10550])).

tff(c_10628,plain,(
    ! [C_1273,D_1277,A_1275,E_1276,B_1274] :
      ( k9_mcart_1(A_1275,B_1274,C_1273,D_1277,E_1276) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_1276)))
      | ~ m1_subset_1(E_1276,k4_zfmisc_1(A_1275,B_1274,C_1273,D_1277))
      | k1_xboole_0 = D_1277
      | k1_xboole_0 = C_1273
      | k1_xboole_0 = B_1274
      | k1_xboole_0 = A_1275 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_10635,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_10628])).

tff(c_10640,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_10464,c_10635])).

tff(c_13131,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_11970,c_10640])).

tff(c_13132,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_13131])).

tff(c_9015,plain,(
    ! [A_21,C_1102,A_1100,B_1101] :
      ( r2_hidden(k2_mcart_1(A_21),C_1102)
      | ~ r2_hidden(A_21,k3_zfmisc_1(A_1100,B_1101,C_1102)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9007,c_22])).

tff(c_11561,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_11548,c_9015])).

tff(c_11723,plain,(
    ! [B_1385] :
      ( r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),B_1385)
      | ~ r1_tarski('#skF_8',B_1385) ) ),
    inference(resolution,[status(thm)],[c_11561,c_2])).

tff(c_12999,plain,(
    ! [B_1412] :
      ( ~ r1_tarski(B_1412,k2_mcart_1(k1_mcart_1('#skF_10')))
      | ~ r1_tarski('#skF_8',B_1412) ) ),
    inference(resolution,[status(thm)],[c_11723,c_16])).

tff(c_13034,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_12999])).

tff(c_13133,plain,(
    ~ r1_tarski('#skF_8','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13132,c_13034])).

tff(c_13156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_13133])).

tff(c_13157,plain,
    ( k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_13131])).

tff(c_13329,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_13157])).

tff(c_13419,plain,(
    r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13329,c_11592])).

tff(c_13421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9102,c_13419])).

tff(c_13422,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_13157])).

tff(c_9245,plain,(
    ! [A_1140,D_1138,C_1139,A_1142,B_1141] :
      ( r2_hidden(k2_mcart_1(A_1140),D_1138)
      | ~ r2_hidden(A_1140,k4_zfmisc_1(A_1142,B_1141,C_1139,D_1138)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9051,c_22])).

tff(c_9260,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_9245])).

tff(c_10465,plain,(
    ! [B_1258] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1258)
      | ~ r1_tarski('#skF_9',B_1258) ) ),
    inference(resolution,[status(thm)],[c_9260,c_2])).

tff(c_10604,plain,(
    ! [B_1271,B_1272] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1271)
      | ~ r1_tarski(B_1272,B_1271)
      | ~ r1_tarski('#skF_9',B_1272) ) ),
    inference(resolution,[status(thm)],[c_10465,c_2])).

tff(c_10616,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_71,c_10604])).

tff(c_10626,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_10616])).

tff(c_10676,plain,(
    ! [B_1281] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1281)
      | ~ r1_tarski('#skF_5',B_1281) ) ),
    inference(resolution,[status(thm)],[c_10626,c_2])).

tff(c_10747,plain,(
    ! [B_1287] :
      ( ~ r1_tarski(B_1287,k2_mcart_1('#skF_10'))
      | ~ r1_tarski('#skF_5',B_1287) ) ),
    inference(resolution,[status(thm)],[c_10676,c_16])).

tff(c_10762,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_10747])).

tff(c_13436,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13422,c_10762])).

tff(c_13448,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_13436])).

tff(c_13449,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_8988])).

tff(c_13497,plain,(
    ! [A_1432,B_1431,C_1430,D_1434,E_1433] :
      ( k11_mcart_1(A_1432,B_1431,C_1430,D_1434,E_1433) = k2_mcart_1(E_1433)
      | ~ m1_subset_1(E_1433,k4_zfmisc_1(A_1432,B_1431,C_1430,D_1434))
      | k1_xboole_0 = D_1434
      | k1_xboole_0 = C_1430
      | k1_xboole_0 = B_1431
      | k1_xboole_0 = A_1432 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_13505,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_13497])).

tff(c_13656,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_13505])).

tff(c_13659,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13656,c_70])).

tff(c_13604,plain,(
    ! [A_1437,B_1438,B_1439] :
      ( r2_hidden('#skF_1'(A_1437,B_1438),B_1439)
      | ~ r1_tarski(A_1437,B_1439)
      | r1_tarski(A_1437,B_1438) ) ),
    inference(resolution,[status(thm)],[c_6,c_8994])).

tff(c_14365,plain,(
    ! [B_1513,A_1514,B_1515] :
      ( ~ r1_tarski(B_1513,'#skF_1'(A_1514,B_1515))
      | ~ r1_tarski(A_1514,B_1513)
      | r1_tarski(A_1514,B_1515) ) ),
    inference(resolution,[status(thm)],[c_13604,c_16])).

tff(c_14391,plain,(
    ! [A_1516,B_1517] :
      ( ~ r1_tarski(A_1516,'#skF_2')
      | r1_tarski(A_1516,B_1517) ) ),
    inference(resolution,[status(thm)],[c_13659,c_14365])).

tff(c_14417,plain,(
    ! [B_1517] : r1_tarski('#skF_6',B_1517) ),
    inference(resolution,[status(thm)],[c_73,c_14391])).

tff(c_4703,plain,(
    ~ r1_tarski('#skF_6',k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')) ),
    inference(resolution,[status(thm)],[c_4699,c_16])).

tff(c_14424,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14417,c_4703])).

tff(c_14426,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_13505])).

tff(c_14476,plain,(
    ! [E_1527,D_1528,C_1524,A_1526,B_1525] :
      ( k2_mcart_1(k1_mcart_1(E_1527)) = k10_mcart_1(A_1526,B_1525,C_1524,D_1528,E_1527)
      | ~ m1_subset_1(E_1527,k4_zfmisc_1(A_1526,B_1525,C_1524,D_1528))
      | k1_xboole_0 = D_1528
      | k1_xboole_0 = C_1524
      | k1_xboole_0 = B_1525
      | k1_xboole_0 = A_1526 ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14486,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_14476])).

tff(c_14491,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_14426,c_14486])).

tff(c_15735,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_14491])).

tff(c_13450,plain,(
    r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_8988])).

tff(c_13555,plain,(
    ! [B_1436] :
      ( r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),B_1436)
      | ~ r1_tarski('#skF_7',B_1436) ) ),
    inference(resolution,[status(thm)],[c_13450,c_2])).

tff(c_9026,plain,(
    ! [A_1103,C_1104,B_1105] :
      ( m1_subset_1(A_1103,C_1104)
      | ~ m1_subset_1(B_1105,k1_zfmisc_1(C_1104))
      | ~ r2_hidden(A_1103,B_1105) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_9041,plain,(
    ! [A_1103,A_6] :
      ( m1_subset_1(A_1103,A_6)
      | ~ r2_hidden(A_1103,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_9026])).

tff(c_13598,plain,(
    ! [A_6] :
      ( m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),A_6)
      | ~ r1_tarski('#skF_7',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_13555,c_9041])).

tff(c_15046,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_13598])).

tff(c_15739,plain,(
    ~ r1_tarski('#skF_7','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_15735,c_15046])).

tff(c_15753,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_15739])).

tff(c_15754,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_14491])).

tff(c_17390,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_15754])).

tff(c_15625,plain,(
    ! [C_1635,D_1634,A_1636,B_1637,A_1638] :
      ( r2_hidden(k1_mcart_1(A_1636),k3_zfmisc_1(A_1638,B_1637,C_1635))
      | ~ r2_hidden(A_1636,k4_zfmisc_1(A_1638,B_1637,C_1635,D_1634)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9051,c_24])).

tff(c_15660,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_36,c_15625])).

tff(c_15673,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_15660,c_9015])).

tff(c_17435,plain,(
    r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17390,c_15673])).

tff(c_17437,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_13449,c_17435])).

tff(c_17438,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_15754])).

tff(c_17440,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_17438])).

tff(c_17461,plain,(
    ! [A_1691] : r1_tarski('#skF_4',A_1691) ),
    inference(demodulation,[status(thm),theory(equality)],[c_17440,c_70])).

tff(c_13655,plain,(
    ! [B_1439,A_1437,B_1438] :
      ( ~ r1_tarski(B_1439,'#skF_1'(A_1437,B_1438))
      | ~ r1_tarski(A_1437,B_1439)
      | r1_tarski(A_1437,B_1438) ) ),
    inference(resolution,[status(thm)],[c_13604,c_16])).

tff(c_17932,plain,(
    ! [A_1708,B_1709] :
      ( ~ r1_tarski(A_1708,'#skF_4')
      | r1_tarski(A_1708,B_1709) ) ),
    inference(resolution,[status(thm)],[c_17461,c_13655])).

tff(c_17970,plain,(
    ! [B_1709] : r1_tarski('#skF_8',B_1709) ),
    inference(resolution,[status(thm)],[c_69,c_17932])).

tff(c_15690,plain,(
    ~ r1_tarski('#skF_8',k2_mcart_1(k1_mcart_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_15673,c_16])).

tff(c_17980,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17970,c_15690])).

tff(c_17981,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_17438])).

tff(c_14427,plain,(
    ! [C_1519,B_1521,D_1518,A_1520,A_1522] :
      ( r2_hidden(k2_mcart_1(A_1520),D_1518)
      | ~ r2_hidden(A_1520,k4_zfmisc_1(A_1522,B_1521,C_1519,D_1518)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9051,c_22])).

tff(c_14446,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_36,c_14427])).

tff(c_14492,plain,(
    ! [B_1529] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1529)
      | ~ r1_tarski('#skF_9',B_1529) ) ),
    inference(resolution,[status(thm)],[c_14446,c_2])).

tff(c_14670,plain,(
    ! [B_1544,B_1545] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1544)
      | ~ r1_tarski(B_1545,B_1544)
      | ~ r1_tarski('#skF_9',B_1545) ) ),
    inference(resolution,[status(thm)],[c_14492,c_2])).

tff(c_14682,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_71,c_14670])).

tff(c_14692,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_14682])).

tff(c_14745,plain,(
    ! [B_1552] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_1552)
      | ~ r1_tarski('#skF_5',B_1552) ) ),
    inference(resolution,[status(thm)],[c_14692,c_2])).

tff(c_14799,plain,(
    ! [B_1553] :
      ( ~ r1_tarski(B_1553,k2_mcart_1('#skF_10'))
      | ~ r1_tarski('#skF_5',B_1553) ) ),
    inference(resolution,[status(thm)],[c_14745,c_16])).

tff(c_14814,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_14799])).

tff(c_17990,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_17981,c_14814])).

tff(c_18002,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_17990])).

tff(c_18004,plain,(
    r1_tarski('#skF_7',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_13598])).

tff(c_18143,plain,(
    ! [B_1715] :
      ( ~ r1_tarski(B_1715,k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
      | ~ r1_tarski('#skF_7',B_1715) ) ),
    inference(resolution,[status(thm)],[c_13555,c_16])).

tff(c_18163,plain,(
    ~ r1_tarski('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_70,c_18143])).

tff(c_18171,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18004,c_18163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n007.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:57:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.63/3.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.69  
% 9.76/3.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.70  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 9.76/3.70  
% 9.76/3.70  %Foreground sorts:
% 9.76/3.70  
% 9.76/3.70  
% 9.76/3.70  %Background operators:
% 9.76/3.70  
% 9.76/3.70  
% 9.76/3.70  %Foreground operators:
% 9.76/3.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.76/3.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.76/3.70  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 9.76/3.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.76/3.70  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 9.76/3.70  tff('#skF_7', type, '#skF_7': $i).
% 9.76/3.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.76/3.70  tff('#skF_10', type, '#skF_10': $i).
% 9.76/3.70  tff('#skF_5', type, '#skF_5': $i).
% 9.76/3.70  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 9.76/3.70  tff('#skF_6', type, '#skF_6': $i).
% 9.76/3.70  tff('#skF_2', type, '#skF_2': $i).
% 9.76/3.70  tff('#skF_3', type, '#skF_3': $i).
% 9.76/3.70  tff('#skF_9', type, '#skF_9': $i).
% 9.76/3.70  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 9.76/3.70  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.76/3.70  tff('#skF_8', type, '#skF_8': $i).
% 9.76/3.70  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 9.76/3.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.76/3.70  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 9.76/3.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.76/3.70  tff('#skF_4', type, '#skF_4': $i).
% 9.76/3.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.76/3.70  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 9.76/3.70  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 9.76/3.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.76/3.70  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.76/3.70  
% 9.76/3.74  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 9.76/3.74  tff(f_109, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_mcart_1)).
% 9.76/3.74  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 9.76/3.74  tff(f_34, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 9.76/3.74  tff(f_53, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 9.76/3.74  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 9.76/3.74  tff(f_84, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 9.76/3.74  tff(f_51, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 9.76/3.74  tff(f_49, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_ordinal1)).
% 9.76/3.74  tff(f_44, axiom, (![A, B, C]: ((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) => m1_subset_1(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset)).
% 9.76/3.74  tff(c_81, plain, (![A_66, B_67]: (r2_hidden('#skF_1'(A_66, B_67), A_66) | r1_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.76/3.74  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.76/3.74  tff(c_89, plain, (![A_66]: (r1_tarski(A_66, A_66))), inference(resolution, [status(thm)], [c_81, c_4])).
% 9.76/3.74  tff(c_42, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.76/3.74  tff(c_53, plain, (![A_59, B_60]: (r1_tarski(A_59, B_60) | ~m1_subset_1(A_59, k1_zfmisc_1(B_60)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 9.76/3.74  tff(c_69, plain, (r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_42, c_53])).
% 9.76/3.74  tff(c_8, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.76/3.74  tff(c_70, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(resolution, [status(thm)], [c_8, c_53])).
% 9.76/3.74  tff(c_40, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.76/3.74  tff(c_71, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_40, c_53])).
% 9.76/3.74  tff(c_36, plain, (r2_hidden('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.76/3.74  tff(c_4776, plain, (![A_644, B_645, C_646, D_647]: (k2_zfmisc_1(k3_zfmisc_1(A_644, B_645, C_646), D_647)=k4_zfmisc_1(A_644, B_645, C_646, D_647))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.76/3.74  tff(c_22, plain, (![A_21, C_23, B_22]: (r2_hidden(k2_mcart_1(A_21), C_23) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.76/3.74  tff(c_4913, plain, (![C_674, D_678, A_675, B_676, A_677]: (r2_hidden(k2_mcart_1(A_675), D_678) | ~r2_hidden(A_675, k4_zfmisc_1(A_677, B_676, C_674, D_678)))), inference(superposition, [status(thm), theory('equality')], [c_4776, c_22])).
% 9.76/3.74  tff(c_4924, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_36, c_4913])).
% 9.76/3.74  tff(c_46, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.76/3.74  tff(c_73, plain, (r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_46, c_53])).
% 9.76/3.74  tff(c_38, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.76/3.74  tff(c_4824, plain, (![B_658, A_659, C_657, D_661, E_660]: (k11_mcart_1(A_659, B_658, C_657, D_661, E_660)=k2_mcart_1(E_660) | ~m1_subset_1(E_660, k4_zfmisc_1(A_659, B_658, C_657, D_661)) | k1_xboole_0=D_661 | k1_xboole_0=C_657 | k1_xboole_0=B_658 | k1_xboole_0=A_659)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_4828, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_4824])).
% 9.76/3.74  tff(c_5021, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4828])).
% 9.76/3.74  tff(c_5025, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_5021, c_70])).
% 9.76/3.74  tff(c_34, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.76/3.74  tff(c_92, plain, (~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitLeft, [status(thm)], [c_34])).
% 9.76/3.74  tff(c_44, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_109])).
% 9.76/3.74  tff(c_72, plain, (r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_53])).
% 9.76/3.74  tff(c_18, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.74  tff(c_252, plain, (![B_115, C_114, A_116, E_117, D_118]: (k11_mcart_1(A_116, B_115, C_114, D_118, E_117)=k2_mcart_1(E_117) | ~m1_subset_1(E_117, k4_zfmisc_1(A_116, B_115, C_114, D_118)) | k1_xboole_0=D_118 | k1_xboole_0=C_114 | k1_xboole_0=B_115 | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_260, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_252])).
% 9.76/3.74  tff(c_329, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_260])).
% 9.76/3.74  tff(c_332, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_329, c_70])).
% 9.76/3.74  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.76/3.74  tff(c_100, plain, (![C_71, B_72, A_73]: (r2_hidden(C_71, B_72) | ~r2_hidden(C_71, A_73) | ~r1_tarski(A_73, B_72))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.76/3.74  tff(c_584, plain, (![A_150, B_151, B_152]: (r2_hidden('#skF_1'(A_150, B_151), B_152) | ~r1_tarski(A_150, B_152) | r1_tarski(A_150, B_151))), inference(resolution, [status(thm)], [c_6, c_100])).
% 9.76/3.74  tff(c_16, plain, (![B_13, A_12]: (~r1_tarski(B_13, A_12) | ~r2_hidden(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.76/3.74  tff(c_735, plain, (![B_167, A_168, B_169]: (~r1_tarski(B_167, '#skF_1'(A_168, B_169)) | ~r1_tarski(A_168, B_167) | r1_tarski(A_168, B_169))), inference(resolution, [status(thm)], [c_584, c_16])).
% 9.76/3.74  tff(c_756, plain, (![A_170, B_171]: (~r1_tarski(A_170, '#skF_2') | r1_tarski(A_170, B_171))), inference(resolution, [status(thm)], [c_332, c_735])).
% 9.76/3.74  tff(c_777, plain, (![B_171]: (r1_tarski('#skF_6', B_171))), inference(resolution, [status(thm)], [c_73, c_756])).
% 9.76/3.74  tff(c_107, plain, (![A_74, B_75, C_76]: (r2_hidden(k1_mcart_1(A_74), B_75) | ~r2_hidden(A_74, k2_zfmisc_1(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.76/3.74  tff(c_1039, plain, (![B_212, C_213, B_214]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_212, C_213), B_214)), B_212) | r1_tarski(k2_zfmisc_1(B_212, C_213), B_214))), inference(resolution, [status(thm)], [c_6, c_107])).
% 9.76/3.74  tff(c_1232, plain, (![B_235, C_236, B_237]: (~r1_tarski(B_235, k1_mcart_1('#skF_1'(k2_zfmisc_1(B_235, C_236), B_237))) | r1_tarski(k2_zfmisc_1(B_235, C_236), B_237))), inference(resolution, [status(thm)], [c_1039, c_16])).
% 9.76/3.74  tff(c_1327, plain, (![C_242, B_243]: (r1_tarski(k2_zfmisc_1('#skF_6', C_242), B_243))), inference(resolution, [status(thm)], [c_777, c_1232])).
% 9.76/3.74  tff(c_1111, plain, (![B_212, C_213, B_214]: (~r1_tarski(B_212, k1_mcart_1('#skF_1'(k2_zfmisc_1(B_212, C_213), B_214))) | r1_tarski(k2_zfmisc_1(B_212, C_213), B_214))), inference(resolution, [status(thm)], [c_1039, c_16])).
% 9.76/3.74  tff(c_1331, plain, (![C_242, C_213, B_214]: (r1_tarski(k2_zfmisc_1(k2_zfmisc_1('#skF_6', C_242), C_213), B_214))), inference(resolution, [status(thm)], [c_1327, c_1111])).
% 9.76/3.74  tff(c_1363, plain, (![C_242, C_213, B_214]: (r1_tarski(k3_zfmisc_1('#skF_6', C_242, C_213), B_214))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1331])).
% 9.76/3.74  tff(c_188, plain, (![A_95, B_96, C_97, D_98]: (k2_zfmisc_1(k3_zfmisc_1(A_95, B_96, C_97), D_98)=k4_zfmisc_1(A_95, B_96, C_97, D_98))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.76/3.74  tff(c_24, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.76/3.74  tff(c_1579, plain, (![C_277, B_279, A_278, D_280, A_276]: (r2_hidden(k1_mcart_1(A_276), k3_zfmisc_1(A_278, B_279, C_277)) | ~r2_hidden(A_276, k4_zfmisc_1(A_278, B_279, C_277, D_280)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_24])).
% 9.76/3.74  tff(c_1606, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_1579])).
% 9.76/3.74  tff(c_1617, plain, (~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_mcart_1('#skF_10'))), inference(resolution, [status(thm)], [c_1606, c_16])).
% 9.76/3.74  tff(c_1629, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1363, c_1617])).
% 9.76/3.74  tff(c_1631, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_260])).
% 9.76/3.74  tff(c_1636, plain, (![D_285, A_283, C_281, E_284, B_282]: (k2_mcart_1(k1_mcart_1(E_284))=k10_mcart_1(A_283, B_282, C_281, D_285, E_284) | ~m1_subset_1(E_284, k4_zfmisc_1(A_283, B_282, C_281, D_285)) | k1_xboole_0=D_285 | k1_xboole_0=C_281 | k1_xboole_0=B_282 | k1_xboole_0=A_283)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_1646, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_1636])).
% 9.76/3.74  tff(c_1651, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1631, c_1646])).
% 9.76/3.74  tff(c_1885, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1651])).
% 9.76/3.74  tff(c_1894, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_1885, c_70])).
% 9.76/3.74  tff(c_1957, plain, (![A_314, B_315, B_316]: (r2_hidden('#skF_1'(A_314, B_315), B_316) | ~r1_tarski(A_314, B_316) | r1_tarski(A_314, B_315))), inference(resolution, [status(thm)], [c_6, c_100])).
% 9.76/3.74  tff(c_2086, plain, (![B_330, A_331, B_332]: (~r1_tarski(B_330, '#skF_1'(A_331, B_332)) | ~r1_tarski(A_331, B_330) | r1_tarski(A_331, B_332))), inference(resolution, [status(thm)], [c_1957, c_16])).
% 9.76/3.74  tff(c_2107, plain, (![A_333, B_334]: (~r1_tarski(A_333, '#skF_3') | r1_tarski(A_333, B_334))), inference(resolution, [status(thm)], [c_1894, c_2086])).
% 9.76/3.74  tff(c_2128, plain, (![B_334]: (r1_tarski('#skF_7', B_334))), inference(resolution, [status(thm)], [c_72, c_2107])).
% 9.76/3.74  tff(c_2713, plain, (![D_416, B_415, C_413, A_414, A_412]: (r2_hidden(k1_mcart_1(A_412), k3_zfmisc_1(A_414, B_415, C_413)) | ~r2_hidden(A_412, k4_zfmisc_1(A_414, B_415, C_413, D_416)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_24])).
% 9.76/3.74  tff(c_2740, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_2713])).
% 9.76/3.74  tff(c_112, plain, (![A_77, B_78, C_79]: (k2_zfmisc_1(k2_zfmisc_1(A_77, B_78), C_79)=k3_zfmisc_1(A_77, B_78, C_79))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.74  tff(c_120, plain, (![A_21, A_77, B_78, C_79]: (r2_hidden(k1_mcart_1(A_21), k2_zfmisc_1(A_77, B_78)) | ~r2_hidden(A_21, k3_zfmisc_1(A_77, B_78, C_79)))), inference(superposition, [status(thm), theory('equality')], [c_112, c_24])).
% 9.76/3.74  tff(c_2853, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2740, c_120])).
% 9.76/3.74  tff(c_2920, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_7')), inference(resolution, [status(thm)], [c_2853, c_22])).
% 9.76/3.74  tff(c_3000, plain, (~r1_tarski('#skF_7', k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))))), inference(resolution, [status(thm)], [c_2920, c_16])).
% 9.76/3.74  tff(c_3011, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2128, c_3000])).
% 9.76/3.74  tff(c_3013, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1651])).
% 9.76/3.74  tff(c_1737, plain, (![D_296, B_293, A_294, C_292, E_295]: (k8_mcart_1(A_294, B_293, C_292, D_296, E_295)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_295))) | ~m1_subset_1(E_295, k4_zfmisc_1(A_294, B_293, C_292, D_296)) | k1_xboole_0=D_296 | k1_xboole_0=C_292 | k1_xboole_0=B_293 | k1_xboole_0=A_294)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_1744, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_1737])).
% 9.76/3.74  tff(c_1749, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1631, c_1744])).
% 9.76/3.74  tff(c_3279, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_3013, c_1749])).
% 9.76/3.74  tff(c_3280, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_3279])).
% 9.76/3.74  tff(c_3299, plain, (![A_483]: (r1_tarski('#skF_4', A_483))), inference(demodulation, [status(thm), theory('equality')], [c_3280, c_70])).
% 9.76/3.74  tff(c_3029, plain, (![A_443, B_444, B_445]: (r2_hidden('#skF_1'(A_443, B_444), B_445) | ~r1_tarski(A_443, B_445) | r1_tarski(A_443, B_444))), inference(resolution, [status(thm)], [c_6, c_100])).
% 9.76/3.74  tff(c_3084, plain, (![B_445, A_443, B_444]: (~r1_tarski(B_445, '#skF_1'(A_443, B_444)) | ~r1_tarski(A_443, B_445) | r1_tarski(A_443, B_444))), inference(resolution, [status(thm)], [c_3029, c_16])).
% 9.76/3.74  tff(c_3362, plain, (![A_487, B_488]: (~r1_tarski(A_487, '#skF_4') | r1_tarski(A_487, B_488))), inference(resolution, [status(thm)], [c_3299, c_3084])).
% 9.76/3.74  tff(c_3383, plain, (![B_488]: (r1_tarski('#skF_8', B_488))), inference(resolution, [status(thm)], [c_69, c_3362])).
% 9.76/3.74  tff(c_4097, plain, (![B_573, C_571, A_570, D_574, A_572]: (r2_hidden(k1_mcart_1(A_570), k3_zfmisc_1(A_572, B_573, C_571)) | ~r2_hidden(A_570, k4_zfmisc_1(A_572, B_573, C_571, D_574)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_24])).
% 9.76/3.74  tff(c_4124, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_4097])).
% 9.76/3.74  tff(c_129, plain, (![A_80, C_81, B_82]: (r2_hidden(k2_mcart_1(A_80), C_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_82, C_81)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 9.76/3.74  tff(c_131, plain, (![A_80, C_16, A_14, B_15]: (r2_hidden(k2_mcart_1(A_80), C_16) | ~r2_hidden(A_80, k3_zfmisc_1(A_14, B_15, C_16)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_129])).
% 9.76/3.74  tff(c_4137, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_4124, c_131])).
% 9.76/3.74  tff(c_4150, plain, (~r1_tarski('#skF_8', k2_mcart_1(k1_mcart_1('#skF_10')))), inference(resolution, [status(thm)], [c_4137, c_16])).
% 9.76/3.74  tff(c_4161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3383, c_4150])).
% 9.76/3.74  tff(c_4163, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_3279])).
% 9.76/3.74  tff(c_1845, plain, (![B_301, D_304, E_303, C_300, A_302]: (k9_mcart_1(A_302, B_301, C_300, D_304, E_303)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_303))) | ~m1_subset_1(E_303, k4_zfmisc_1(A_302, B_301, C_300, D_304)) | k1_xboole_0=D_304 | k1_xboole_0=C_300 | k1_xboole_0=B_301 | k1_xboole_0=A_302)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_1855, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_1845])).
% 9.76/3.74  tff(c_1861, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1631, c_1855])).
% 9.76/3.74  tff(c_4164, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_3013, c_4163, c_1861])).
% 9.76/3.74  tff(c_4165, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_4164])).
% 9.76/3.74  tff(c_230, plain, (![C_110, A_109, A_111, D_113, B_112]: (r2_hidden(k2_mcart_1(A_109), D_113) | ~r2_hidden(A_109, k4_zfmisc_1(A_111, B_112, C_110, D_113)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_22])).
% 9.76/3.74  tff(c_237, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_36, c_230])).
% 9.76/3.74  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.76/3.74  tff(c_261, plain, (![B_119]: (r2_hidden(k2_mcart_1('#skF_10'), B_119) | ~r1_tarski('#skF_9', B_119))), inference(resolution, [status(thm)], [c_237, c_2])).
% 9.76/3.74  tff(c_1703, plain, (![B_290, B_291]: (r2_hidden(k2_mcart_1('#skF_10'), B_290) | ~r1_tarski(B_291, B_290) | ~r1_tarski('#skF_9', B_291))), inference(resolution, [status(thm)], [c_261, c_2])).
% 9.76/3.74  tff(c_1715, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_71, c_1703])).
% 9.76/3.74  tff(c_1725, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_1715])).
% 9.76/3.74  tff(c_1774, plain, (![B_298]: (r2_hidden(k2_mcart_1('#skF_10'), B_298) | ~r1_tarski('#skF_5', B_298))), inference(resolution, [status(thm)], [c_1725, c_2])).
% 9.76/3.74  tff(c_136, plain, (![A_83, C_84, B_85]: (m1_subset_1(A_83, C_84) | ~m1_subset_1(B_85, k1_zfmisc_1(C_84)) | ~r2_hidden(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.76/3.74  tff(c_151, plain, (![A_83, A_6]: (m1_subset_1(A_83, A_6) | ~r2_hidden(A_83, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_136])).
% 9.76/3.74  tff(c_1816, plain, (![A_6]: (m1_subset_1(k2_mcart_1('#skF_10'), A_6) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_1774, c_151])).
% 9.76/3.74  tff(c_1826, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1816])).
% 9.76/3.74  tff(c_4172, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_4165, c_1826])).
% 9.76/3.74  tff(c_4183, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_4172])).
% 9.76/3.74  tff(c_4185, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_4164])).
% 9.76/3.74  tff(c_4162, plain, (k1_xboole_0='#skF_5' | k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_3279])).
% 9.76/3.74  tff(c_4191, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_4185, c_4162])).
% 9.76/3.74  tff(c_4527, plain, (![A_615, C_614, B_616, D_617, A_613]: (r2_hidden(k1_mcart_1(A_613), k3_zfmisc_1(A_615, B_616, C_614)) | ~r2_hidden(A_613, k4_zfmisc_1(A_615, B_616, C_614, D_617)))), inference(superposition, [status(thm), theory('equality')], [c_188, c_24])).
% 9.76/3.74  tff(c_4554, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_4527])).
% 9.76/3.74  tff(c_4613, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_4554, c_120])).
% 9.76/3.74  tff(c_4624, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_6')), inference(resolution, [status(thm)], [c_4613, c_24])).
% 9.76/3.74  tff(c_4634, plain, (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_4191, c_4624])).
% 9.76/3.74  tff(c_4636, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_4634])).
% 9.76/3.74  tff(c_4638, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1816])).
% 9.76/3.74  tff(c_312, plain, (![B_2, B_119]: (r2_hidden(k2_mcart_1('#skF_10'), B_2) | ~r1_tarski(B_119, B_2) | ~r1_tarski('#skF_9', B_119))), inference(resolution, [status(thm)], [c_261, c_2])).
% 9.76/3.74  tff(c_4640, plain, (r2_hidden(k2_mcart_1('#skF_10'), k1_xboole_0) | ~r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_4638, c_312])).
% 9.76/3.74  tff(c_4645, plain, (r2_hidden(k2_mcart_1('#skF_10'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_4640])).
% 9.76/3.74  tff(c_4685, plain, (~r1_tarski(k1_xboole_0, k2_mcart_1('#skF_10'))), inference(resolution, [status(thm)], [c_4645, c_16])).
% 9.76/3.74  tff(c_4697, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_4685])).
% 9.76/3.74  tff(c_4699, plain, (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 9.76/3.74  tff(c_4741, plain, (![C_637, B_638, A_639]: (r2_hidden(C_637, B_638) | ~r2_hidden(C_637, A_639) | ~r1_tarski(A_639, B_638))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.76/3.74  tff(c_5115, plain, (![B_702]: (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), B_702) | ~r1_tarski('#skF_6', B_702))), inference(resolution, [status(thm)], [c_4699, c_4741])).
% 9.76/3.74  tff(c_5527, plain, (![B_738]: (~r1_tarski(B_738, k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~r1_tarski('#skF_6', B_738))), inference(resolution, [status(thm)], [c_5115, c_16])).
% 9.76/3.74  tff(c_5543, plain, (~r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_5025, c_5527])).
% 9.76/3.74  tff(c_5554, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_5543])).
% 9.76/3.74  tff(c_5556, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4828])).
% 9.76/3.74  tff(c_4939, plain, (![A_681, B_680, D_683, E_682, C_679]: (k2_mcart_1(k1_mcart_1(E_682))=k10_mcart_1(A_681, B_680, C_679, D_683, E_682) | ~m1_subset_1(E_682, k4_zfmisc_1(A_681, B_680, C_679, D_683)) | k1_xboole_0=D_683 | k1_xboole_0=C_679 | k1_xboole_0=B_680 | k1_xboole_0=A_681)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_4947, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_4939])).
% 9.76/3.74  tff(c_5569, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_5556, c_4947])).
% 9.76/3.74  tff(c_5570, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_5569])).
% 9.76/3.74  tff(c_5576, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_5570, c_70])).
% 9.76/3.74  tff(c_4861, plain, (![A_671, B_672, B_673]: (r2_hidden('#skF_1'(A_671, B_672), B_673) | ~r1_tarski(A_671, B_673) | r1_tarski(A_671, B_672))), inference(resolution, [status(thm)], [c_6, c_4741])).
% 9.76/3.74  tff(c_6005, plain, (![B_787, A_788, B_789]: (~r1_tarski(B_787, '#skF_1'(A_788, B_789)) | ~r1_tarski(A_788, B_787) | r1_tarski(A_788, B_789))), inference(resolution, [status(thm)], [c_4861, c_16])).
% 9.76/3.74  tff(c_6027, plain, (![A_790, B_791]: (~r1_tarski(A_790, '#skF_3') | r1_tarski(A_790, B_791))), inference(resolution, [status(thm)], [c_5576, c_6005])).
% 9.76/3.74  tff(c_6048, plain, (![B_791]: (r1_tarski('#skF_7', B_791))), inference(resolution, [status(thm)], [c_72, c_6027])).
% 9.76/3.74  tff(c_6557, plain, (![D_847, A_846, B_845, C_843, A_844]: (r2_hidden(k1_mcart_1(A_844), k3_zfmisc_1(A_846, B_845, C_843)) | ~r2_hidden(A_844, k4_zfmisc_1(A_846, B_845, C_843, D_847)))), inference(superposition, [status(thm), theory('equality')], [c_4776, c_24])).
% 9.76/3.74  tff(c_6588, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_6557])).
% 9.76/3.74  tff(c_4722, plain, (![A_634, B_635, C_636]: (k2_zfmisc_1(k2_zfmisc_1(A_634, B_635), C_636)=k3_zfmisc_1(A_634, B_635, C_636))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.74  tff(c_4732, plain, (![A_21, A_634, B_635, C_636]: (r2_hidden(k1_mcart_1(A_21), k2_zfmisc_1(A_634, B_635)) | ~r2_hidden(A_21, k3_zfmisc_1(A_634, B_635, C_636)))), inference(superposition, [status(thm), theory('equality')], [c_4722, c_24])).
% 9.76/3.74  tff(c_6600, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_6588, c_4732])).
% 9.76/3.74  tff(c_6632, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_7')), inference(resolution, [status(thm)], [c_6600, c_22])).
% 9.76/3.74  tff(c_6644, plain, (~r1_tarski('#skF_7', k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))))), inference(resolution, [status(thm)], [c_6632, c_16])).
% 9.76/3.74  tff(c_6655, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6048, c_6644])).
% 9.76/3.74  tff(c_6657, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_5569])).
% 9.76/3.74  tff(c_5557, plain, (![C_739, A_741, B_740, D_743, E_742]: (k9_mcart_1(A_741, B_740, C_739, D_743, E_742)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_742))) | ~m1_subset_1(E_742, k4_zfmisc_1(A_741, B_740, C_739, D_743)) | k1_xboole_0=D_743 | k1_xboole_0=C_739 | k1_xboole_0=B_740 | k1_xboole_0=A_741)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_5567, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_5557])).
% 9.76/3.74  tff(c_6674, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5556, c_6657, c_5567])).
% 9.76/3.74  tff(c_6675, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_6674])).
% 9.76/3.74  tff(c_6683, plain, (![A_6]: (r1_tarski('#skF_4', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6675, c_70])).
% 9.76/3.74  tff(c_7124, plain, (![B_901, A_902, B_903]: (~r1_tarski(B_901, '#skF_1'(A_902, B_903)) | ~r1_tarski(A_902, B_901) | r1_tarski(A_902, B_903))), inference(resolution, [status(thm)], [c_4861, c_16])).
% 9.76/3.74  tff(c_7145, plain, (![A_904, B_905]: (~r1_tarski(A_904, '#skF_4') | r1_tarski(A_904, B_905))), inference(resolution, [status(thm)], [c_6683, c_7124])).
% 9.76/3.74  tff(c_7166, plain, (![B_905]: (r1_tarski('#skF_8', B_905))), inference(resolution, [status(thm)], [c_69, c_7145])).
% 9.76/3.74  tff(c_7639, plain, (![D_962, B_960, A_961, A_959, C_958]: (r2_hidden(k1_mcart_1(A_959), k3_zfmisc_1(A_961, B_960, C_958)) | ~r2_hidden(A_959, k4_zfmisc_1(A_961, B_960, C_958, D_962)))), inference(superposition, [status(thm), theory('equality')], [c_4776, c_24])).
% 9.76/3.74  tff(c_7670, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_7639])).
% 9.76/3.74  tff(c_4730, plain, (![A_21, C_636, A_634, B_635]: (r2_hidden(k2_mcart_1(A_21), C_636) | ~r2_hidden(A_21, k3_zfmisc_1(A_634, B_635, C_636)))), inference(superposition, [status(thm), theory('equality')], [c_4722, c_22])).
% 9.76/3.74  tff(c_7683, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_7670, c_4730])).
% 9.76/3.74  tff(c_7696, plain, (~r1_tarski('#skF_8', k2_mcart_1(k1_mcart_1('#skF_10')))), inference(resolution, [status(thm)], [c_7683, c_16])).
% 9.76/3.74  tff(c_7707, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_7166, c_7696])).
% 9.76/3.74  tff(c_7709, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_6674])).
% 9.76/3.74  tff(c_6659, plain, (![A_850, E_851, B_849, D_852, C_848]: (k8_mcart_1(A_850, B_849, C_848, D_852, E_851)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_851))) | ~m1_subset_1(E_851, k4_zfmisc_1(A_850, B_849, C_848, D_852)) | k1_xboole_0=D_852 | k1_xboole_0=C_848 | k1_xboole_0=B_849 | k1_xboole_0=A_850)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_6666, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_6659])).
% 9.76/3.74  tff(c_6671, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5556, c_6657, c_6666])).
% 9.76/3.74  tff(c_8594, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_7709, c_6671])).
% 9.76/3.74  tff(c_8595, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_8594])).
% 9.76/3.74  tff(c_4968, plain, (![B_685]: (r2_hidden(k2_mcart_1('#skF_10'), B_685) | ~r1_tarski('#skF_9', B_685))), inference(resolution, [status(thm)], [c_4924, c_2])).
% 9.76/3.74  tff(c_7785, plain, (![B_966, B_967]: (r2_hidden(k2_mcart_1('#skF_10'), B_966) | ~r1_tarski(B_967, B_966) | ~r1_tarski('#skF_9', B_967))), inference(resolution, [status(thm)], [c_4968, c_2])).
% 9.76/3.74  tff(c_7797, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_71, c_7785])).
% 9.76/3.74  tff(c_7807, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_7797])).
% 9.76/3.74  tff(c_7840, plain, (![B_972]: (r2_hidden(k2_mcart_1('#skF_10'), B_972) | ~r1_tarski('#skF_5', B_972))), inference(resolution, [status(thm)], [c_7807, c_2])).
% 9.76/3.74  tff(c_4751, plain, (![A_640, C_641, B_642]: (m1_subset_1(A_640, C_641) | ~m1_subset_1(B_642, k1_zfmisc_1(C_641)) | ~r2_hidden(A_640, B_642))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.76/3.74  tff(c_4766, plain, (![A_640, A_6]: (m1_subset_1(A_640, A_6) | ~r2_hidden(A_640, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_4751])).
% 9.76/3.74  tff(c_7886, plain, (![A_6]: (m1_subset_1(k2_mcart_1('#skF_10'), A_6) | ~r1_tarski('#skF_5', k1_xboole_0))), inference(resolution, [status(thm)], [c_7840, c_4766])).
% 9.76/3.74  tff(c_7922, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_7886])).
% 9.76/3.74  tff(c_8602, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8595, c_7922])).
% 9.76/3.74  tff(c_8616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_8602])).
% 9.76/3.74  tff(c_8618, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_8594])).
% 9.76/3.74  tff(c_5555, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_4828])).
% 9.76/3.74  tff(c_8924, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_8618, c_7709, c_6657, c_5555])).
% 9.76/3.74  tff(c_4698, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_34])).
% 9.76/3.74  tff(c_4721, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_4698])).
% 9.76/3.74  tff(c_8925, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_8924, c_4721])).
% 9.76/3.74  tff(c_8928, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4924, c_8925])).
% 9.76/3.74  tff(c_8930, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(splitRight, [status(thm)], [c_7886])).
% 9.76/3.74  tff(c_5017, plain, (![B_2, B_685]: (r2_hidden(k2_mcart_1('#skF_10'), B_2) | ~r1_tarski(B_685, B_2) | ~r1_tarski('#skF_9', B_685))), inference(resolution, [status(thm)], [c_4968, c_2])).
% 9.76/3.74  tff(c_8932, plain, (r2_hidden(k2_mcart_1('#skF_10'), k1_xboole_0) | ~r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_8930, c_5017])).
% 9.76/3.74  tff(c_8935, plain, (r2_hidden(k2_mcart_1('#skF_10'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_71, c_8932])).
% 9.76/3.74  tff(c_8975, plain, (~r1_tarski(k1_xboole_0, k2_mcart_1('#skF_10'))), inference(resolution, [status(thm)], [c_8935, c_16])).
% 9.76/3.74  tff(c_8987, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_8975])).
% 9.76/3.74  tff(c_8988, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_4698])).
% 9.76/3.74  tff(c_9102, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_8988])).
% 9.76/3.74  tff(c_9236, plain, (![D_1137, E_1136, B_1134, C_1133, A_1135]: (k11_mcart_1(A_1135, B_1134, C_1133, D_1137, E_1136)=k2_mcart_1(E_1136) | ~m1_subset_1(E_1136, k4_zfmisc_1(A_1135, B_1134, C_1133, D_1137)) | k1_xboole_0=D_1137 | k1_xboole_0=C_1133 | k1_xboole_0=B_1134 | k1_xboole_0=A_1135)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_9244, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_9236])).
% 9.76/3.74  tff(c_9275, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_9244])).
% 9.76/3.74  tff(c_9278, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_9275, c_70])).
% 9.76/3.74  tff(c_8994, plain, (![C_1097, B_1098, A_1099]: (r2_hidden(C_1097, B_1098) | ~r2_hidden(C_1097, A_1099) | ~r1_tarski(A_1099, B_1098))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.76/3.74  tff(c_9135, plain, (![B_1129]: (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), B_1129) | ~r1_tarski('#skF_6', B_1129))), inference(resolution, [status(thm)], [c_4699, c_8994])).
% 9.76/3.74  tff(c_10435, plain, (![B_1257]: (~r1_tarski(B_1257, k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~r1_tarski('#skF_6', B_1257))), inference(resolution, [status(thm)], [c_9135, c_16])).
% 9.76/3.74  tff(c_10451, plain, (~r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_9278, c_10435])).
% 9.76/3.74  tff(c_10462, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_73, c_10451])).
% 9.76/3.74  tff(c_10464, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_9244])).
% 9.76/3.74  tff(c_10535, plain, (![A_1262, B_1261, E_1263, C_1260, D_1264]: (k2_mcart_1(k1_mcart_1(E_1263))=k10_mcart_1(A_1262, B_1261, C_1260, D_1264, E_1263) | ~m1_subset_1(E_1263, k4_zfmisc_1(A_1262, B_1261, C_1260, D_1264)) | k1_xboole_0=D_1264 | k1_xboole_0=C_1260 | k1_xboole_0=B_1261 | k1_xboole_0=A_1262)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_10545, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_10535])).
% 9.76/3.74  tff(c_10550, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_10464, c_10545])).
% 9.76/3.74  tff(c_11821, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_10550])).
% 9.76/3.74  tff(c_9184, plain, (![A_1130, B_1131, B_1132]: (r2_hidden('#skF_1'(A_1130, B_1131), B_1132) | ~r1_tarski(A_1130, B_1132) | r1_tarski(A_1130, B_1131))), inference(resolution, [status(thm)], [c_6, c_8994])).
% 9.76/3.74  tff(c_11028, plain, (![B_1314, A_1315, B_1316]: (~r1_tarski(B_1314, '#skF_1'(A_1315, B_1316)) | ~r1_tarski(A_1315, B_1314) | r1_tarski(A_1315, B_1316))), inference(resolution, [status(thm)], [c_9184, c_16])).
% 9.76/3.74  tff(c_11048, plain, (![A_1315, B_1316]: (~r1_tarski(A_1315, k1_xboole_0) | r1_tarski(A_1315, B_1316))), inference(resolution, [status(thm)], [c_70, c_11028])).
% 9.76/3.74  tff(c_11934, plain, (![A_1391, B_1392]: (~r1_tarski(A_1391, '#skF_3') | r1_tarski(A_1391, B_1392))), inference(demodulation, [status(thm), theory('equality')], [c_11821, c_11048])).
% 9.76/3.74  tff(c_11963, plain, (![B_1392]: (r1_tarski('#skF_7', B_1392))), inference(resolution, [status(thm)], [c_72, c_11934])).
% 9.76/3.74  tff(c_9051, plain, (![A_1107, B_1108, C_1109, D_1110]: (k2_zfmisc_1(k3_zfmisc_1(A_1107, B_1108, C_1109), D_1110)=k4_zfmisc_1(A_1107, B_1108, C_1109, D_1110))), inference(cnfTransformation, [status(thm)], [f_53])).
% 9.76/3.74  tff(c_11517, plain, (![B_1377, A_1376, D_1374, A_1378, C_1375]: (r2_hidden(k1_mcart_1(A_1376), k3_zfmisc_1(A_1378, B_1377, C_1375)) | ~r2_hidden(A_1376, k4_zfmisc_1(A_1378, B_1377, C_1375, D_1374)))), inference(superposition, [status(thm), theory('equality')], [c_9051, c_24])).
% 9.76/3.74  tff(c_11548, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_11517])).
% 9.76/3.74  tff(c_9007, plain, (![A_1100, B_1101, C_1102]: (k2_zfmisc_1(k2_zfmisc_1(A_1100, B_1101), C_1102)=k3_zfmisc_1(A_1100, B_1101, C_1102))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.76/3.74  tff(c_9017, plain, (![A_21, A_1100, B_1101, C_1102]: (r2_hidden(k1_mcart_1(A_21), k2_zfmisc_1(A_1100, B_1101)) | ~r2_hidden(A_21, k3_zfmisc_1(A_1100, B_1101, C_1102)))), inference(superposition, [status(thm), theory('equality')], [c_9007, c_24])).
% 9.76/3.74  tff(c_11560, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_11548, c_9017])).
% 9.76/3.74  tff(c_11592, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_7')), inference(resolution, [status(thm)], [c_11560, c_22])).
% 9.76/3.74  tff(c_11608, plain, (~r1_tarski('#skF_7', k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))))), inference(resolution, [status(thm)], [c_11592, c_16])).
% 9.76/3.74  tff(c_11968, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11963, c_11608])).
% 9.76/3.74  tff(c_11970, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_10550])).
% 9.76/3.74  tff(c_10628, plain, (![C_1273, D_1277, A_1275, E_1276, B_1274]: (k9_mcart_1(A_1275, B_1274, C_1273, D_1277, E_1276)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_1276))) | ~m1_subset_1(E_1276, k4_zfmisc_1(A_1275, B_1274, C_1273, D_1277)) | k1_xboole_0=D_1277 | k1_xboole_0=C_1273 | k1_xboole_0=B_1274 | k1_xboole_0=A_1275)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_10635, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_10628])).
% 9.76/3.74  tff(c_10640, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_10464, c_10635])).
% 9.76/3.74  tff(c_13131, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_11970, c_10640])).
% 9.76/3.74  tff(c_13132, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_13131])).
% 9.76/3.74  tff(c_9015, plain, (![A_21, C_1102, A_1100, B_1101]: (r2_hidden(k2_mcart_1(A_21), C_1102) | ~r2_hidden(A_21, k3_zfmisc_1(A_1100, B_1101, C_1102)))), inference(superposition, [status(thm), theory('equality')], [c_9007, c_22])).
% 9.76/3.74  tff(c_11561, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_11548, c_9015])).
% 9.76/3.74  tff(c_11723, plain, (![B_1385]: (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), B_1385) | ~r1_tarski('#skF_8', B_1385))), inference(resolution, [status(thm)], [c_11561, c_2])).
% 9.76/3.74  tff(c_12999, plain, (![B_1412]: (~r1_tarski(B_1412, k2_mcart_1(k1_mcart_1('#skF_10'))) | ~r1_tarski('#skF_8', B_1412))), inference(resolution, [status(thm)], [c_11723, c_16])).
% 9.76/3.74  tff(c_13034, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_12999])).
% 9.76/3.74  tff(c_13133, plain, (~r1_tarski('#skF_8', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13132, c_13034])).
% 9.76/3.74  tff(c_13156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_69, c_13133])).
% 9.76/3.74  tff(c_13157, plain, (k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_13131])).
% 9.76/3.74  tff(c_13329, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_13157])).
% 9.76/3.74  tff(c_13419, plain, (r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_13329, c_11592])).
% 9.76/3.74  tff(c_13421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9102, c_13419])).
% 9.76/3.74  tff(c_13422, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_13157])).
% 9.76/3.74  tff(c_9245, plain, (![A_1140, D_1138, C_1139, A_1142, B_1141]: (r2_hidden(k2_mcart_1(A_1140), D_1138) | ~r2_hidden(A_1140, k4_zfmisc_1(A_1142, B_1141, C_1139, D_1138)))), inference(superposition, [status(thm), theory('equality')], [c_9051, c_22])).
% 9.76/3.74  tff(c_9260, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_36, c_9245])).
% 9.76/3.74  tff(c_10465, plain, (![B_1258]: (r2_hidden(k2_mcart_1('#skF_10'), B_1258) | ~r1_tarski('#skF_9', B_1258))), inference(resolution, [status(thm)], [c_9260, c_2])).
% 9.76/3.74  tff(c_10604, plain, (![B_1271, B_1272]: (r2_hidden(k2_mcart_1('#skF_10'), B_1271) | ~r1_tarski(B_1272, B_1271) | ~r1_tarski('#skF_9', B_1272))), inference(resolution, [status(thm)], [c_10465, c_2])).
% 9.76/3.74  tff(c_10616, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_71, c_10604])).
% 9.76/3.74  tff(c_10626, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_10616])).
% 9.76/3.74  tff(c_10676, plain, (![B_1281]: (r2_hidden(k2_mcart_1('#skF_10'), B_1281) | ~r1_tarski('#skF_5', B_1281))), inference(resolution, [status(thm)], [c_10626, c_2])).
% 9.76/3.74  tff(c_10747, plain, (![B_1287]: (~r1_tarski(B_1287, k2_mcart_1('#skF_10')) | ~r1_tarski('#skF_5', B_1287))), inference(resolution, [status(thm)], [c_10676, c_16])).
% 9.76/3.74  tff(c_10762, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_10747])).
% 9.76/3.74  tff(c_13436, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_13422, c_10762])).
% 9.76/3.74  tff(c_13448, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_13436])).
% 9.76/3.74  tff(c_13449, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_8988])).
% 9.76/3.74  tff(c_13497, plain, (![A_1432, B_1431, C_1430, D_1434, E_1433]: (k11_mcart_1(A_1432, B_1431, C_1430, D_1434, E_1433)=k2_mcart_1(E_1433) | ~m1_subset_1(E_1433, k4_zfmisc_1(A_1432, B_1431, C_1430, D_1434)) | k1_xboole_0=D_1434 | k1_xboole_0=C_1430 | k1_xboole_0=B_1431 | k1_xboole_0=A_1432)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_13505, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_13497])).
% 9.76/3.74  tff(c_13656, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_13505])).
% 9.76/3.74  tff(c_13659, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_13656, c_70])).
% 9.76/3.74  tff(c_13604, plain, (![A_1437, B_1438, B_1439]: (r2_hidden('#skF_1'(A_1437, B_1438), B_1439) | ~r1_tarski(A_1437, B_1439) | r1_tarski(A_1437, B_1438))), inference(resolution, [status(thm)], [c_6, c_8994])).
% 9.76/3.74  tff(c_14365, plain, (![B_1513, A_1514, B_1515]: (~r1_tarski(B_1513, '#skF_1'(A_1514, B_1515)) | ~r1_tarski(A_1514, B_1513) | r1_tarski(A_1514, B_1515))), inference(resolution, [status(thm)], [c_13604, c_16])).
% 9.76/3.74  tff(c_14391, plain, (![A_1516, B_1517]: (~r1_tarski(A_1516, '#skF_2') | r1_tarski(A_1516, B_1517))), inference(resolution, [status(thm)], [c_13659, c_14365])).
% 9.76/3.74  tff(c_14417, plain, (![B_1517]: (r1_tarski('#skF_6', B_1517))), inference(resolution, [status(thm)], [c_73, c_14391])).
% 9.76/3.74  tff(c_4703, plain, (~r1_tarski('#skF_6', k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'))), inference(resolution, [status(thm)], [c_4699, c_16])).
% 9.76/3.74  tff(c_14424, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14417, c_4703])).
% 9.76/3.74  tff(c_14426, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_13505])).
% 9.76/3.74  tff(c_14476, plain, (![E_1527, D_1528, C_1524, A_1526, B_1525]: (k2_mcart_1(k1_mcart_1(E_1527))=k10_mcart_1(A_1526, B_1525, C_1524, D_1528, E_1527) | ~m1_subset_1(E_1527, k4_zfmisc_1(A_1526, B_1525, C_1524, D_1528)) | k1_xboole_0=D_1528 | k1_xboole_0=C_1524 | k1_xboole_0=B_1525 | k1_xboole_0=A_1526)), inference(cnfTransformation, [status(thm)], [f_84])).
% 9.76/3.74  tff(c_14486, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_14476])).
% 9.76/3.74  tff(c_14491, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_14426, c_14486])).
% 9.76/3.74  tff(c_15735, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_14491])).
% 9.76/3.74  tff(c_13450, plain, (r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_8988])).
% 9.76/3.74  tff(c_13555, plain, (![B_1436]: (r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), B_1436) | ~r1_tarski('#skF_7', B_1436))), inference(resolution, [status(thm)], [c_13450, c_2])).
% 9.76/3.74  tff(c_9026, plain, (![A_1103, C_1104, B_1105]: (m1_subset_1(A_1103, C_1104) | ~m1_subset_1(B_1105, k1_zfmisc_1(C_1104)) | ~r2_hidden(A_1103, B_1105))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.76/3.74  tff(c_9041, plain, (![A_1103, A_6]: (m1_subset_1(A_1103, A_6) | ~r2_hidden(A_1103, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_9026])).
% 9.76/3.74  tff(c_13598, plain, (![A_6]: (m1_subset_1(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), A_6) | ~r1_tarski('#skF_7', k1_xboole_0))), inference(resolution, [status(thm)], [c_13555, c_9041])).
% 9.76/3.74  tff(c_15046, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_13598])).
% 9.76/3.74  tff(c_15739, plain, (~r1_tarski('#skF_7', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_15735, c_15046])).
% 9.76/3.74  tff(c_15753, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_15739])).
% 9.76/3.74  tff(c_15754, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_14491])).
% 9.76/3.74  tff(c_17390, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitLeft, [status(thm)], [c_15754])).
% 9.76/3.74  tff(c_15625, plain, (![C_1635, D_1634, A_1636, B_1637, A_1638]: (r2_hidden(k1_mcart_1(A_1636), k3_zfmisc_1(A_1638, B_1637, C_1635)) | ~r2_hidden(A_1636, k4_zfmisc_1(A_1638, B_1637, C_1635, D_1634)))), inference(superposition, [status(thm), theory('equality')], [c_9051, c_24])).
% 9.76/3.74  tff(c_15660, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_36, c_15625])).
% 9.76/3.74  tff(c_15673, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_15660, c_9015])).
% 9.76/3.74  tff(c_17435, plain, (r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_17390, c_15673])).
% 9.76/3.74  tff(c_17437, plain, $false, inference(negUnitSimplification, [status(thm)], [c_13449, c_17435])).
% 9.76/3.74  tff(c_17438, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_15754])).
% 9.76/3.74  tff(c_17440, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_17438])).
% 9.76/3.74  tff(c_17461, plain, (![A_1691]: (r1_tarski('#skF_4', A_1691))), inference(demodulation, [status(thm), theory('equality')], [c_17440, c_70])).
% 9.76/3.74  tff(c_13655, plain, (![B_1439, A_1437, B_1438]: (~r1_tarski(B_1439, '#skF_1'(A_1437, B_1438)) | ~r1_tarski(A_1437, B_1439) | r1_tarski(A_1437, B_1438))), inference(resolution, [status(thm)], [c_13604, c_16])).
% 9.76/3.74  tff(c_17932, plain, (![A_1708, B_1709]: (~r1_tarski(A_1708, '#skF_4') | r1_tarski(A_1708, B_1709))), inference(resolution, [status(thm)], [c_17461, c_13655])).
% 9.76/3.74  tff(c_17970, plain, (![B_1709]: (r1_tarski('#skF_8', B_1709))), inference(resolution, [status(thm)], [c_69, c_17932])).
% 9.76/3.74  tff(c_15690, plain, (~r1_tarski('#skF_8', k2_mcart_1(k1_mcart_1('#skF_10')))), inference(resolution, [status(thm)], [c_15673, c_16])).
% 9.76/3.74  tff(c_17980, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17970, c_15690])).
% 9.76/3.74  tff(c_17981, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_17438])).
% 9.76/3.74  tff(c_14427, plain, (![C_1519, B_1521, D_1518, A_1520, A_1522]: (r2_hidden(k2_mcart_1(A_1520), D_1518) | ~r2_hidden(A_1520, k4_zfmisc_1(A_1522, B_1521, C_1519, D_1518)))), inference(superposition, [status(thm), theory('equality')], [c_9051, c_22])).
% 9.76/3.74  tff(c_14446, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_36, c_14427])).
% 9.76/3.74  tff(c_14492, plain, (![B_1529]: (r2_hidden(k2_mcart_1('#skF_10'), B_1529) | ~r1_tarski('#skF_9', B_1529))), inference(resolution, [status(thm)], [c_14446, c_2])).
% 9.76/3.74  tff(c_14670, plain, (![B_1544, B_1545]: (r2_hidden(k2_mcart_1('#skF_10'), B_1544) | ~r1_tarski(B_1545, B_1544) | ~r1_tarski('#skF_9', B_1545))), inference(resolution, [status(thm)], [c_14492, c_2])).
% 9.76/3.74  tff(c_14682, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_71, c_14670])).
% 9.76/3.74  tff(c_14692, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_89, c_14682])).
% 9.76/3.74  tff(c_14745, plain, (![B_1552]: (r2_hidden(k2_mcart_1('#skF_10'), B_1552) | ~r1_tarski('#skF_5', B_1552))), inference(resolution, [status(thm)], [c_14692, c_2])).
% 9.76/3.74  tff(c_14799, plain, (![B_1553]: (~r1_tarski(B_1553, k2_mcart_1('#skF_10')) | ~r1_tarski('#skF_5', B_1553))), inference(resolution, [status(thm)], [c_14745, c_16])).
% 9.76/3.74  tff(c_14814, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_14799])).
% 9.76/3.74  tff(c_17990, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_17981, c_14814])).
% 9.76/3.74  tff(c_18002, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_17990])).
% 9.76/3.74  tff(c_18004, plain, (r1_tarski('#skF_7', k1_xboole_0)), inference(splitRight, [status(thm)], [c_13598])).
% 9.76/3.74  tff(c_18143, plain, (![B_1715]: (~r1_tarski(B_1715, k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~r1_tarski('#skF_7', B_1715))), inference(resolution, [status(thm)], [c_13555, c_16])).
% 9.76/3.74  tff(c_18163, plain, (~r1_tarski('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_70, c_18143])).
% 9.76/3.74  tff(c_18171, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18004, c_18163])).
% 9.76/3.74  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.76/3.74  
% 9.76/3.74  Inference rules
% 9.76/3.74  ----------------------
% 9.76/3.74  #Ref     : 0
% 9.76/3.74  #Sup     : 4055
% 9.76/3.74  #Fact    : 0
% 9.76/3.74  #Define  : 0
% 9.76/3.74  #Split   : 188
% 9.76/3.74  #Chain   : 0
% 9.76/3.74  #Close   : 0
% 9.76/3.74  
% 9.76/3.74  Ordering : KBO
% 9.76/3.74  
% 9.76/3.74  Simplification rules
% 9.76/3.74  ----------------------
% 9.76/3.74  #Subsume      : 917
% 9.76/3.74  #Demod        : 1547
% 9.76/3.74  #Tautology    : 513
% 9.76/3.74  #SimpNegUnit  : 34
% 9.76/3.74  #BackRed      : 473
% 9.76/3.74  
% 9.76/3.74  #Partial instantiations: 0
% 9.76/3.74  #Strategies tried      : 1
% 9.76/3.74  
% 9.76/3.74  Timing (in seconds)
% 9.76/3.74  ----------------------
% 9.76/3.74  Preprocessing        : 0.34
% 9.76/3.74  Parsing              : 0.18
% 9.76/3.74  CNF conversion       : 0.03
% 9.76/3.74  Main loop            : 2.57
% 9.76/3.74  Inferencing          : 0.77
% 9.76/3.74  Reduction            : 0.90
% 9.76/3.74  Demodulation         : 0.58
% 9.76/3.74  BG Simplification    : 0.08
% 9.76/3.74  Subsumption          : 0.58
% 9.76/3.74  Abstraction          : 0.10
% 9.76/3.74  MUC search           : 0.00
% 9.76/3.74  Cooper               : 0.00
% 9.76/3.74  Total                : 3.01
% 9.76/3.74  Index Insertion      : 0.00
% 9.76/3.74  Index Deletion       : 0.00
% 9.76/3.74  Index Matching       : 0.00
% 9.76/3.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
