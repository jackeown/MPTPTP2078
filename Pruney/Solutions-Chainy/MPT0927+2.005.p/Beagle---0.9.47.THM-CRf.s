%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:24 EST 2020

% Result     : Theorem 6.87s
% Output     : CNFRefutation 7.21s
% Verified   : 
% Statistics : Number of formulae       :  334 (1229 expanded)
%              Number of leaves         :   36 ( 403 expanded)
%              Depth                    :   12
%              Number of atoms          :  609 (4315 expanded)
%              Number of equality atoms :  234 (1780 expanded)
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

tff(f_45,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_103,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_47,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_78,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] : k2_zfmisc_1(k2_zfmisc_1(A_11,B_12),C_13) = k3_zfmisc_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2534,plain,(
    ! [A_434,B_435] :
      ( r1_tarski(A_434,B_435)
      | ~ m1_subset_1(A_434,k1_zfmisc_1(B_435)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2551,plain,(
    r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_2534])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2564,plain,(
    ! [A_438,B_439] :
      ( ~ r2_hidden('#skF_1'(A_438,B_439),B_439)
      | r1_tarski(A_438,B_439) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2569,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_2564])).

tff(c_42,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2553,plain,(
    r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_2534])).

tff(c_34,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2630,plain,(
    ! [A_460,B_461,C_462,D_463] : k2_zfmisc_1(k3_zfmisc_1(A_460,B_461,C_462),D_463) = k4_zfmisc_1(A_460,B_461,C_462,D_463) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_20,plain,(
    ! [A_18,C_20,B_19] :
      ( r2_hidden(k2_mcart_1(A_18),C_20)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2666,plain,(
    ! [C_467,A_466,B_469,D_465,A_468] :
      ( r2_hidden(k2_mcart_1(A_466),D_465)
      | ~ r2_hidden(A_466,k4_zfmisc_1(A_468,B_469,C_467,D_465)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2630,c_20])).

tff(c_2677,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_2666])).

tff(c_44,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2554,plain,(
    r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_2534])).

tff(c_36,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_2720,plain,(
    ! [A_472,E_474,D_473,C_475,B_476] :
      ( k11_mcart_1(A_472,B_476,C_475,D_473,E_474) = k2_mcart_1(E_474)
      | ~ m1_subset_1(E_474,k4_zfmisc_1(A_472,B_476,C_475,D_473))
      | k1_xboole_0 = D_473
      | k1_xboole_0 = C_475
      | k1_xboole_0 = B_476
      | k1_xboole_0 = A_472 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2724,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_2720])).

tff(c_2735,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2724])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2738,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2735,c_8])).

tff(c_32,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_79,plain,(
    ! [A_62,B_63] :
      ( ~ r2_hidden('#skF_1'(A_62,B_63),B_63)
      | r1_tarski(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_84,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(resolution,[status(thm)],[c_6,c_79])).

tff(c_53,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_72,plain,(
    r1_tarski('#skF_7','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_53])).

tff(c_73,plain,(
    r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_53])).

tff(c_182,plain,(
    ! [D_92,B_95,C_94,A_91,E_93] :
      ( k11_mcart_1(A_91,B_95,C_94,D_92,E_93) = k2_mcart_1(E_93)
      | ~ m1_subset_1(E_93,k4_zfmisc_1(A_91,B_95,C_94,D_92))
      | k1_xboole_0 = D_92
      | k1_xboole_0 = C_94
      | k1_xboole_0 = B_95
      | k1_xboole_0 = A_91 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_186,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_182])).

tff(c_274,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_186])).

tff(c_278,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_274,c_8])).

tff(c_93,plain,(
    ! [C_67,B_68,A_69] :
      ( r2_hidden(C_67,B_68)
      | ~ r2_hidden(C_67,A_69)
      | ~ r1_tarski(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_157,plain,(
    ! [A_88,B_89,B_90] :
      ( r2_hidden('#skF_1'(A_88,B_89),B_90)
      | ~ r1_tarski(A_88,B_90)
      | r1_tarski(A_88,B_89) ) ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( ~ r1_tarski(B_10,A_9)
      | ~ r2_hidden(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_410,plain,(
    ! [B_140,A_141,B_142] :
      ( ~ r1_tarski(B_140,'#skF_1'(A_141,B_142))
      | ~ r1_tarski(A_141,B_140)
      | r1_tarski(A_141,B_142) ) ),
    inference(resolution,[status(thm)],[c_157,c_14])).

tff(c_421,plain,(
    ! [A_143,B_144] :
      ( ~ r1_tarski(A_143,'#skF_2')
      | r1_tarski(A_143,B_144) ) ),
    inference(resolution,[status(thm)],[c_278,c_410])).

tff(c_434,plain,(
    ! [B_144] : r1_tarski('#skF_6',B_144) ),
    inference(resolution,[status(thm)],[c_73,c_421])).

tff(c_122,plain,(
    ! [A_76,B_77,C_78] :
      ( r2_hidden(k1_mcart_1(A_76),B_77)
      | ~ r2_hidden(A_76,k2_zfmisc_1(B_77,C_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_517,plain,(
    ! [B_163,C_164,B_165] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_163,C_164),B_165)),B_163)
      | r1_tarski(k2_zfmisc_1(B_163,C_164),B_165) ) ),
    inference(resolution,[status(thm)],[c_6,c_122])).

tff(c_593,plain,(
    ! [B_169,C_170,B_171] :
      ( ~ r1_tarski(B_169,k1_mcart_1('#skF_1'(k2_zfmisc_1(B_169,C_170),B_171)))
      | r1_tarski(k2_zfmisc_1(B_169,C_170),B_171) ) ),
    inference(resolution,[status(thm)],[c_517,c_14])).

tff(c_612,plain,(
    ! [C_172,B_173] : r1_tarski(k2_zfmisc_1('#skF_6',C_172),B_173) ),
    inference(resolution,[status(thm)],[c_434,c_593])).

tff(c_554,plain,(
    ! [B_163,C_164,B_165] :
      ( ~ r1_tarski(B_163,k1_mcart_1('#skF_1'(k2_zfmisc_1(B_163,C_164),B_165)))
      | r1_tarski(k2_zfmisc_1(B_163,C_164),B_165) ) ),
    inference(resolution,[status(thm)],[c_517,c_14])).

tff(c_616,plain,(
    ! [C_172,C_164,B_165] : r1_tarski(k2_zfmisc_1(k2_zfmisc_1('#skF_6',C_172),C_164),B_165) ),
    inference(resolution,[status(thm)],[c_612,c_554])).

tff(c_644,plain,(
    ! [C_172,C_164,B_165] : r1_tarski(k3_zfmisc_1('#skF_6',C_172,C_164),B_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_616])).

tff(c_129,plain,(
    ! [A_79,B_80,C_81,D_82] : k2_zfmisc_1(k3_zfmisc_1(A_79,B_80,C_81),D_82) = k4_zfmisc_1(A_79,B_80,C_81,D_82) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_22,plain,(
    ! [A_18,B_19,C_20] :
      ( r2_hidden(k1_mcart_1(A_18),B_19)
      | ~ r2_hidden(A_18,k2_zfmisc_1(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_704,plain,(
    ! [A_181,A_182,C_183,B_184,D_180] :
      ( r2_hidden(k1_mcart_1(A_181),k3_zfmisc_1(A_182,B_184,C_183))
      | ~ r2_hidden(A_181,k4_zfmisc_1(A_182,B_184,C_183,D_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_22])).

tff(c_731,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_704])).

tff(c_829,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_mcart_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_731,c_14])).

tff(c_838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_644,c_829])).

tff(c_840,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_186])).

tff(c_241,plain,(
    ! [D_104,B_107,E_105,C_106,A_103] :
      ( k2_mcart_1(k1_mcart_1(E_105)) = k10_mcart_1(A_103,B_107,C_106,D_104,E_105)
      | ~ m1_subset_1(E_105,k4_zfmisc_1(A_103,B_107,C_106,D_104))
      | k1_xboole_0 = D_104
      | k1_xboole_0 = C_106
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_103 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_245,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_241])).

tff(c_850,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_245])).

tff(c_851,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_850])).

tff(c_857,plain,(
    ! [A_6] : r1_tarski('#skF_3',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_851,c_8])).

tff(c_985,plain,(
    ! [B_220,A_221,B_222] :
      ( ~ r1_tarski(B_220,'#skF_1'(A_221,B_222))
      | ~ r1_tarski(A_221,B_220)
      | r1_tarski(A_221,B_222) ) ),
    inference(resolution,[status(thm)],[c_157,c_14])).

tff(c_996,plain,(
    ! [A_223,B_224] :
      ( ~ r1_tarski(A_223,'#skF_3')
      | r1_tarski(A_223,B_224) ) ),
    inference(resolution,[status(thm)],[c_857,c_985])).

tff(c_1009,plain,(
    ! [B_224] : r1_tarski('#skF_7',B_224) ),
    inference(resolution,[status(thm)],[c_72,c_996])).

tff(c_115,plain,(
    ! [A_73,C_74,B_75] :
      ( r2_hidden(k2_mcart_1(A_73),C_74)
      | ~ r2_hidden(A_73,k2_zfmisc_1(B_75,C_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1089,plain,(
    ! [B_242,C_243,B_244] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_242,C_243),B_244)),C_243)
      | r1_tarski(k2_zfmisc_1(B_242,C_243),B_244) ) ),
    inference(resolution,[status(thm)],[c_6,c_115])).

tff(c_1170,plain,(
    ! [C_255,B_256,B_257] :
      ( ~ r1_tarski(C_255,k2_mcart_1('#skF_1'(k2_zfmisc_1(B_256,C_255),B_257)))
      | r1_tarski(k2_zfmisc_1(B_256,C_255),B_257) ) ),
    inference(resolution,[status(thm)],[c_1089,c_14])).

tff(c_1185,plain,(
    ! [B_256,B_257] : r1_tarski(k2_zfmisc_1(B_256,'#skF_7'),B_257) ),
    inference(resolution,[status(thm)],[c_1009,c_1170])).

tff(c_1476,plain,(
    ! [C_282,B_283,A_280,A_281,D_279] :
      ( r2_hidden(k1_mcart_1(A_280),k3_zfmisc_1(A_281,B_283,C_282))
      | ~ r2_hidden(A_280,k4_zfmisc_1(A_281,B_283,C_282,D_279)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_22])).

tff(c_1503,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_1476])).

tff(c_124,plain,(
    ! [A_76,A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_76),k2_zfmisc_1(A_11,B_12))
      | ~ r2_hidden(A_76,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_122])).

tff(c_1531,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_1503,c_124])).

tff(c_1567,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_6','#skF_7'),k1_mcart_1(k1_mcart_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_1531,c_14])).

tff(c_1576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1185,c_1567])).

tff(c_1578,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_850])).

tff(c_70,plain,(
    r1_tarski('#skF_8','#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_53])).

tff(c_1630,plain,(
    ! [E_303,B_305,D_302,A_301,C_304] :
      ( k9_mcart_1(A_301,B_305,C_304,D_302,E_303) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_303)))
      | ~ m1_subset_1(E_303,k4_zfmisc_1(A_301,B_305,C_304,D_302))
      | k1_xboole_0 = D_302
      | k1_xboole_0 = C_304
      | k1_xboole_0 = B_305
      | k1_xboole_0 = A_301 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1632,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_1630])).

tff(c_1635,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_1578,c_1632])).

tff(c_1715,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1635])).

tff(c_1690,plain,(
    ! [B_316,A_317,B_318] :
      ( ~ r1_tarski(B_316,'#skF_1'(A_317,B_318))
      | ~ r1_tarski(A_317,B_316)
      | r1_tarski(A_317,B_318) ) ),
    inference(resolution,[status(thm)],[c_157,c_14])).

tff(c_1700,plain,(
    ! [A_317,B_318] :
      ( ~ r1_tarski(A_317,k1_xboole_0)
      | r1_tarski(A_317,B_318) ) ),
    inference(resolution,[status(thm)],[c_8,c_1690])).

tff(c_1780,plain,(
    ! [A_329,B_330] :
      ( ~ r1_tarski(A_329,'#skF_4')
      | r1_tarski(A_329,B_330) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1715,c_1700])).

tff(c_1793,plain,(
    ! [B_330] : r1_tarski('#skF_8',B_330) ),
    inference(resolution,[status(thm)],[c_70,c_1780])).

tff(c_2040,plain,(
    ! [A_364,B_367,D_363,A_365,C_366] :
      ( r2_hidden(k1_mcart_1(A_364),k3_zfmisc_1(A_365,B_367,C_366))
      | ~ r2_hidden(A_364,k4_zfmisc_1(A_365,B_367,C_366,D_363)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_22])).

tff(c_2067,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_2040])).

tff(c_117,plain,(
    ! [A_73,C_13,A_11,B_12] :
      ( r2_hidden(k2_mcart_1(A_73),C_13)
      | ~ r2_hidden(A_73,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_115])).

tff(c_2124,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_2067,c_117])).

tff(c_2131,plain,(
    ~ r1_tarski('#skF_8',k2_mcart_1(k1_mcart_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_2124,c_14])).

tff(c_2138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1793,c_2131])).

tff(c_2140,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1635])).

tff(c_843,plain,(
    ! [C_196,A_193,D_194,E_195,B_197] :
      ( k8_mcart_1(A_193,B_197,C_196,D_194,E_195) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_195)))
      | ~ m1_subset_1(E_195,k4_zfmisc_1(A_193,B_197,C_196,D_194))
      | k1_xboole_0 = D_194
      | k1_xboole_0 = C_196
      | k1_xboole_0 = B_197
      | k1_xboole_0 = A_193 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_845,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_843])).

tff(c_848,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_840,c_845])).

tff(c_2170,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_1578,c_2140,c_848])).

tff(c_2171,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2170])).

tff(c_38,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_71,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_53])).

tff(c_187,plain,(
    ! [C_99,A_98,D_96,B_100,A_97] :
      ( r2_hidden(k2_mcart_1(A_97),D_96)
      | ~ r2_hidden(A_97,k4_zfmisc_1(A_98,B_100,C_99,D_96)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_20])).

tff(c_198,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_187])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_206,plain,(
    ! [B_101] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_101)
      | ~ r1_tarski('#skF_9',B_101) ) ),
    inference(resolution,[status(thm)],[c_198,c_2])).

tff(c_246,plain,(
    ! [B_108,B_109] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_108)
      | ~ r1_tarski(B_109,B_108)
      | ~ r1_tarski('#skF_9',B_109) ) ),
    inference(resolution,[status(thm)],[c_206,c_2])).

tff(c_250,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_71,c_246])).

tff(c_262,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_250])).

tff(c_1579,plain,(
    ! [B_295] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_295)
      | ~ r1_tarski('#skF_5',B_295) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_1605,plain,(
    ! [B_296] :
      ( ~ r1_tarski(B_296,k2_mcart_1('#skF_10'))
      | ~ r1_tarski('#skF_5',B_296) ) ),
    inference(resolution,[status(thm)],[c_1579,c_14])).

tff(c_1615,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_1605])).

tff(c_2175,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2171,c_1615])).

tff(c_2185,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_2175])).

tff(c_2186,plain,(
    k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_2170])).

tff(c_2477,plain,(
    ! [C_432,A_430,D_429,B_433,A_431] :
      ( r2_hidden(k1_mcart_1(A_430),k3_zfmisc_1(A_431,B_433,C_432))
      | ~ r2_hidden(A_430,k4_zfmisc_1(A_431,B_433,C_432,D_429)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_22])).

tff(c_2504,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_2477])).

tff(c_2514,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_2504,c_124])).

tff(c_2520,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_6') ),
    inference(resolution,[status(thm)],[c_2514,c_22])).

tff(c_2529,plain,(
    r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2186,c_2520])).

tff(c_2531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_2529])).

tff(c_2533,plain,(
    r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2601,plain,(
    ! [C_449,B_450,A_451] :
      ( r2_hidden(C_449,B_450)
      | ~ r2_hidden(C_449,A_451)
      | ~ r1_tarski(A_451,B_450) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_2646,plain,(
    ! [B_464] :
      ( r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),B_464)
      | ~ r1_tarski('#skF_6',B_464) ) ),
    inference(resolution,[status(thm)],[c_2533,c_2601])).

tff(c_2839,plain,(
    ! [B_498] :
      ( ~ r1_tarski(B_498,k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
      | ~ r1_tarski('#skF_6',B_498) ) ),
    inference(resolution,[status(thm)],[c_2646,c_14])).

tff(c_2843,plain,(
    ~ r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_2738,c_2839])).

tff(c_2851,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2554,c_2843])).

tff(c_2852,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitRight,[status(thm)],[c_2724])).

tff(c_3023,plain,(
    k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(splitLeft,[status(thm)],[c_2852])).

tff(c_2532,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2571,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2532])).

tff(c_3035,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3023,c_2571])).

tff(c_3038,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2677,c_3035])).

tff(c_3039,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2852])).

tff(c_3041,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3039])).

tff(c_2966,plain,(
    ! [A_519,B_520,B_521] :
      ( r2_hidden('#skF_1'(A_519,B_520),B_521)
      | ~ r1_tarski(A_519,B_521)
      | r1_tarski(A_519,B_520) ) ),
    inference(resolution,[status(thm)],[c_6,c_2601])).

tff(c_3012,plain,(
    ! [B_528,A_529,B_530] :
      ( ~ r1_tarski(B_528,'#skF_1'(A_529,B_530))
      | ~ r1_tarski(A_529,B_528)
      | r1_tarski(A_529,B_530) ) ),
    inference(resolution,[status(thm)],[c_2966,c_14])).

tff(c_3022,plain,(
    ! [A_529,B_530] :
      ( ~ r1_tarski(A_529,k1_xboole_0)
      | r1_tarski(A_529,B_530) ) ),
    inference(resolution,[status(thm)],[c_8,c_3012])).

tff(c_3090,plain,(
    ! [A_534,B_535] :
      ( ~ r1_tarski(A_534,'#skF_3')
      | r1_tarski(A_534,B_535) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3041,c_3022])).

tff(c_3103,plain,(
    ! [B_535] : r1_tarski('#skF_7',B_535) ),
    inference(resolution,[status(thm)],[c_2553,c_3090])).

tff(c_3556,plain,(
    ! [B_606,C_604,A_605,A_603,D_602] :
      ( r2_hidden(k1_mcart_1(A_603),k3_zfmisc_1(A_605,B_606,C_604))
      | ~ r2_hidden(A_603,k4_zfmisc_1(A_605,B_606,C_604,D_602)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2630,c_22])).

tff(c_3587,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_3556])).

tff(c_2594,plain,(
    ! [A_446,B_447,C_448] :
      ( r2_hidden(k1_mcart_1(A_446),B_447)
      | ~ r2_hidden(A_446,k2_zfmisc_1(B_447,C_448)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2596,plain,(
    ! [A_446,A_11,B_12,C_13] :
      ( r2_hidden(k1_mcart_1(A_446),k2_zfmisc_1(A_11,B_12))
      | ~ r2_hidden(A_446,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_2594])).

tff(c_3599,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_3587,c_2596])).

tff(c_3619,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3599,c_20])).

tff(c_3627,plain,(
    ~ r1_tarski('#skF_7',k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))) ),
    inference(resolution,[status(thm)],[c_3619,c_14])).

tff(c_3634,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3103,c_3627])).

tff(c_3635,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3039])).

tff(c_3637,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3635])).

tff(c_2552,plain,(
    r1_tarski('#skF_9','#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_2534])).

tff(c_2685,plain,(
    ! [B_470] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_470)
      | ~ r1_tarski('#skF_9',B_470) ) ),
    inference(resolution,[status(thm)],[c_2677,c_2])).

tff(c_2854,plain,(
    ! [B_499,B_500] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_499)
      | ~ r1_tarski(B_500,B_499)
      | ~ r1_tarski('#skF_9',B_500) ) ),
    inference(resolution,[status(thm)],[c_2685,c_2])).

tff(c_2858,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_2552,c_2854])).

tff(c_2870,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_2858])).

tff(c_2892,plain,(
    ! [B_506] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_506)
      | ~ r1_tarski('#skF_5',B_506) ) ),
    inference(resolution,[status(thm)],[c_2870,c_2])).

tff(c_2916,plain,(
    ! [B_507] :
      ( ~ r1_tarski(B_507,k2_mcart_1('#skF_10'))
      | ~ r1_tarski('#skF_5',B_507) ) ),
    inference(resolution,[status(thm)],[c_2892,c_14])).

tff(c_2926,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_2916])).

tff(c_3642,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3637,c_2926])).

tff(c_3650,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_3642])).

tff(c_3651,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3635])).

tff(c_3705,plain,(
    ! [A_612,B_613] :
      ( ~ r1_tarski(A_612,'#skF_4')
      | r1_tarski(A_612,B_613) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3651,c_3022])).

tff(c_3718,plain,(
    ! [B_613] : r1_tarski('#skF_8',B_613) ),
    inference(resolution,[status(thm)],[c_2551,c_3705])).

tff(c_2611,plain,(
    ! [A_452,C_453,B_454] :
      ( r2_hidden(k2_mcart_1(A_452),C_453)
      | ~ r2_hidden(A_452,k2_zfmisc_1(B_454,C_453)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_3834,plain,(
    ! [B_642,C_643,B_644] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_642,C_643),B_644)),C_643)
      | r1_tarski(k2_zfmisc_1(B_642,C_643),B_644) ) ),
    inference(resolution,[status(thm)],[c_6,c_2611])).

tff(c_3910,plain,(
    ! [C_648,B_649,B_650] :
      ( ~ r1_tarski(C_648,k2_mcart_1('#skF_1'(k2_zfmisc_1(B_649,C_648),B_650)))
      | r1_tarski(k2_zfmisc_1(B_649,C_648),B_650) ) ),
    inference(resolution,[status(thm)],[c_3834,c_14])).

tff(c_3994,plain,(
    ! [B_654,B_655] : r1_tarski(k2_zfmisc_1(B_654,'#skF_8'),B_655) ),
    inference(resolution,[status(thm)],[c_3718,c_3910])).

tff(c_4036,plain,(
    ! [A_11,B_12,B_655] : r1_tarski(k3_zfmisc_1(A_11,B_12,'#skF_8'),B_655) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_3994])).

tff(c_4286,plain,(
    ! [B_686,A_685,C_684,A_683,D_682] :
      ( r2_hidden(k1_mcart_1(A_683),k3_zfmisc_1(A_685,B_686,C_684))
      | ~ r2_hidden(A_683,k4_zfmisc_1(A_685,B_686,C_684,D_682)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2630,c_22])).

tff(c_4317,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_4286])).

tff(c_4335,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_mcart_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_4317,c_14])).

tff(c_4344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4036,c_4335])).

tff(c_4345,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2532])).

tff(c_4491,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_4345])).

tff(c_4565,plain,(
    ! [A_727,C_730,E_729,D_728,B_731] :
      ( k11_mcart_1(A_727,B_731,C_730,D_728,E_729) = k2_mcart_1(E_729)
      | ~ m1_subset_1(E_729,k4_zfmisc_1(A_727,B_731,C_730,D_728))
      | k1_xboole_0 = D_728
      | k1_xboole_0 = C_730
      | k1_xboole_0 = B_731
      | k1_xboole_0 = A_727 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4569,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4565])).

tff(c_4572,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4569])).

tff(c_4575,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4572,c_8])).

tff(c_4358,plain,(
    ! [C_691,B_692,A_693] :
      ( r2_hidden(C_691,B_692)
      | ~ r2_hidden(C_691,A_693)
      | ~ r1_tarski(A_693,B_692) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4412,plain,(
    ! [B_708] :
      ( r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),B_708)
      | ~ r1_tarski('#skF_6',B_708) ) ),
    inference(resolution,[status(thm)],[c_2533,c_4358])).

tff(c_4603,plain,(
    ! [B_738] :
      ( ~ r1_tarski(B_738,k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
      | ~ r1_tarski('#skF_6',B_738) ) ),
    inference(resolution,[status(thm)],[c_4412,c_14])).

tff(c_4607,plain,(
    ~ r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_4575,c_4603])).

tff(c_4615,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2554,c_4607])).

tff(c_4617,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4569])).

tff(c_4643,plain,(
    ! [D_741,A_740,C_743,E_742,B_744] :
      ( k2_mcart_1(k1_mcart_1(E_742)) = k10_mcart_1(A_740,B_744,C_743,D_741,E_742)
      | ~ m1_subset_1(E_742,k4_zfmisc_1(A_740,B_744,C_743,D_741))
      | k1_xboole_0 = D_741
      | k1_xboole_0 = C_743
      | k1_xboole_0 = B_744
      | k1_xboole_0 = A_740 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4646,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4643])).

tff(c_4649,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4617,c_4646])).

tff(c_4779,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4649])).

tff(c_4794,plain,(
    ! [A_774] : r1_tarski('#skF_3',A_774) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4779,c_8])).

tff(c_4700,plain,(
    ! [A_757,B_758,B_759] :
      ( r2_hidden('#skF_1'(A_757,B_758),B_759)
      | ~ r1_tarski(A_757,B_759)
      | r1_tarski(A_757,B_758) ) ),
    inference(resolution,[status(thm)],[c_6,c_4358])).

tff(c_4728,plain,(
    ! [B_759,A_757,B_758] :
      ( ~ r1_tarski(B_759,'#skF_1'(A_757,B_758))
      | ~ r1_tarski(A_757,B_759)
      | r1_tarski(A_757,B_758) ) ),
    inference(resolution,[status(thm)],[c_4700,c_14])).

tff(c_4851,plain,(
    ! [A_779,B_780] :
      ( ~ r1_tarski(A_779,'#skF_3')
      | r1_tarski(A_779,B_780) ) ),
    inference(resolution,[status(thm)],[c_4794,c_4728])).

tff(c_4864,plain,(
    ! [B_780] : r1_tarski('#skF_7',B_780) ),
    inference(resolution,[status(thm)],[c_2553,c_4851])).

tff(c_4432,plain,(
    ! [A_709,B_710,C_711,D_712] : k2_zfmisc_1(k3_zfmisc_1(A_709,B_710,C_711),D_712) = k4_zfmisc_1(A_709,B_710,C_711,D_712) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5100,plain,(
    ! [B_815,A_816,D_818,C_817,A_814] :
      ( r2_hidden(k1_mcart_1(A_816),k3_zfmisc_1(A_814,B_815,C_817))
      | ~ r2_hidden(A_816,k4_zfmisc_1(A_814,B_815,C_817,D_818)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_22])).

tff(c_5131,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_5100])).

tff(c_4376,plain,(
    ! [A_697,B_698,C_699] : k2_zfmisc_1(k2_zfmisc_1(A_697,B_698),C_699) = k3_zfmisc_1(A_697,B_698,C_699) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4384,plain,(
    ! [A_18,A_697,B_698,C_699] :
      ( r2_hidden(k1_mcart_1(A_18),k2_zfmisc_1(A_697,B_698))
      | ~ r2_hidden(A_18,k3_zfmisc_1(A_697,B_698,C_699)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4376,c_22])).

tff(c_5192,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_5131,c_4384])).

tff(c_5302,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_5192,c_20])).

tff(c_5310,plain,(
    ~ r1_tarski('#skF_7',k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))) ),
    inference(resolution,[status(thm)],[c_5302,c_14])).

tff(c_5317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4864,c_5310])).

tff(c_5319,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4649])).

tff(c_4771,plain,(
    ! [E_768,D_767,B_770,A_766,C_769] :
      ( k8_mcart_1(A_766,B_770,C_769,D_767,E_768) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_768)))
      | ~ m1_subset_1(E_768,k4_zfmisc_1(A_766,B_770,C_769,D_767))
      | k1_xboole_0 = D_767
      | k1_xboole_0 = C_769
      | k1_xboole_0 = B_770
      | k1_xboole_0 = A_766 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4773,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4771])).

tff(c_4776,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4617,c_4773])).

tff(c_5372,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_5319,c_4776])).

tff(c_5373,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_5372])).

tff(c_4749,plain,(
    ! [B_761,A_762,B_763] :
      ( ~ r1_tarski(B_761,'#skF_1'(A_762,B_763))
      | ~ r1_tarski(A_762,B_761)
      | r1_tarski(A_762,B_763) ) ),
    inference(resolution,[status(thm)],[c_4700,c_14])).

tff(c_4759,plain,(
    ! [A_762,B_763] :
      ( ~ r1_tarski(A_762,k1_xboole_0)
      | r1_tarski(A_762,B_763) ) ),
    inference(resolution,[status(thm)],[c_8,c_4749])).

tff(c_5425,plain,(
    ! [A_854,B_855] :
      ( ~ r1_tarski(A_854,'#skF_4')
      | r1_tarski(A_854,B_855) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5373,c_4759])).

tff(c_5438,plain,(
    ! [B_855] : r1_tarski('#skF_8',B_855) ),
    inference(resolution,[status(thm)],[c_2551,c_5425])).

tff(c_4393,plain,(
    ! [A_700,C_701,B_702] :
      ( r2_hidden(k2_mcart_1(A_700),C_701)
      | ~ r2_hidden(A_700,k2_zfmisc_1(B_702,C_701)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5478,plain,(
    ! [B_857,C_858,B_859] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_857,C_858),B_859)),C_858)
      | r1_tarski(k2_zfmisc_1(B_857,C_858),B_859) ) ),
    inference(resolution,[status(thm)],[c_6,c_4393])).

tff(c_5575,plain,(
    ! [C_872,B_873,B_874] :
      ( ~ r1_tarski(C_872,k2_mcart_1('#skF_1'(k2_zfmisc_1(B_873,C_872),B_874)))
      | r1_tarski(k2_zfmisc_1(B_873,C_872),B_874) ) ),
    inference(resolution,[status(thm)],[c_5478,c_14])).

tff(c_5659,plain,(
    ! [B_878,B_879] : r1_tarski(k2_zfmisc_1(B_878,'#skF_8'),B_879) ),
    inference(resolution,[status(thm)],[c_5438,c_5575])).

tff(c_5701,plain,(
    ! [A_11,B_12,B_879] : r1_tarski(k3_zfmisc_1(A_11,B_12,'#skF_8'),B_879) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_5659])).

tff(c_5979,plain,(
    ! [C_909,B_907,A_906,D_910,A_908] :
      ( r2_hidden(k1_mcart_1(A_908),k3_zfmisc_1(A_906,B_907,C_909))
      | ~ r2_hidden(A_908,k4_zfmisc_1(A_906,B_907,C_909,D_910)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_22])).

tff(c_6010,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_5979])).

tff(c_6028,plain,(
    ~ r1_tarski(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'),k1_mcart_1('#skF_10')) ),
    inference(resolution,[status(thm)],[c_6010,c_14])).

tff(c_6037,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5701,c_6028])).

tff(c_6039,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5372])).

tff(c_4684,plain,(
    ! [E_750,A_748,C_751,D_749,B_752] :
      ( k9_mcart_1(A_748,B_752,C_751,D_749,E_750) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_750)))
      | ~ m1_subset_1(E_750,k4_zfmisc_1(A_748,B_752,C_751,D_749))
      | k1_xboole_0 = D_749
      | k1_xboole_0 = C_751
      | k1_xboole_0 = B_752
      | k1_xboole_0 = A_748 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_4686,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_4684])).

tff(c_4689,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4617,c_4686])).

tff(c_6052,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_5319,c_6039,c_4689])).

tff(c_6053,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_6052])).

tff(c_4468,plain,(
    ! [A_716,C_717,D_718,B_715,A_714] :
      ( r2_hidden(k2_mcart_1(A_716),D_718)
      | ~ r2_hidden(A_716,k4_zfmisc_1(A_714,B_715,C_717,D_718)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_20])).

tff(c_4483,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_34,c_4468])).

tff(c_4492,plain,(
    ! [B_719] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_719)
      | ~ r1_tarski('#skF_9',B_719) ) ),
    inference(resolution,[status(thm)],[c_4483,c_2])).

tff(c_4537,plain,(
    ! [B_725,B_726] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_725)
      | ~ r1_tarski(B_726,B_725)
      | ~ r1_tarski('#skF_9',B_726) ) ),
    inference(resolution,[status(thm)],[c_4492,c_2])).

tff(c_4541,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_2552,c_4537])).

tff(c_4553,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_4541])).

tff(c_4619,plain,(
    ! [B_739] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_739)
      | ~ r1_tarski('#skF_5',B_739) ) ),
    inference(resolution,[status(thm)],[c_4553,c_2])).

tff(c_4650,plain,(
    ! [B_745] :
      ( ~ r1_tarski(B_745,k2_mcart_1('#skF_10'))
      | ~ r1_tarski('#skF_5',B_745) ) ),
    inference(resolution,[status(thm)],[c_4619,c_14])).

tff(c_4660,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_4650])).

tff(c_6060,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6053,c_4660])).

tff(c_6068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_6060])).

tff(c_6069,plain,(
    k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_6052])).

tff(c_6151,plain,(
    ! [A_925,C_926,B_924,D_927,A_923] :
      ( r2_hidden(k1_mcart_1(A_925),k3_zfmisc_1(A_923,B_924,C_926))
      | ~ r2_hidden(A_925,k4_zfmisc_1(A_923,B_924,C_926,D_927)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_22])).

tff(c_6182,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_6151])).

tff(c_6192,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_6182,c_4384])).

tff(c_6198,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))),'#skF_7') ),
    inference(resolution,[status(thm)],[c_6192,c_20])).

tff(c_6207,plain,(
    r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6069,c_6198])).

tff(c_6209,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4491,c_6207])).

tff(c_6210,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_4345])).

tff(c_6259,plain,(
    ! [E_934,A_932,C_935,B_936,D_933] :
      ( k11_mcart_1(A_932,B_936,C_935,D_933,E_934) = k2_mcart_1(E_934)
      | ~ m1_subset_1(E_934,k4_zfmisc_1(A_932,B_936,C_935,D_933))
      | k1_xboole_0 = D_933
      | k1_xboole_0 = C_935
      | k1_xboole_0 = B_936
      | k1_xboole_0 = A_932 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6263,plain,
    ( k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_6259])).

tff(c_6292,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_6263])).

tff(c_6295,plain,(
    ! [A_6] : r1_tarski('#skF_2',A_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6292,c_8])).

tff(c_6463,plain,(
    ! [B_969] :
      ( ~ r1_tarski(B_969,k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'))
      | ~ r1_tarski('#skF_6',B_969) ) ),
    inference(resolution,[status(thm)],[c_4412,c_14])).

tff(c_6467,plain,(
    ~ r1_tarski('#skF_6','#skF_2') ),
    inference(resolution,[status(thm)],[c_6295,c_6463])).

tff(c_6475,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2554,c_6467])).

tff(c_6477,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_6263])).

tff(c_6480,plain,(
    ! [E_972,B_974,D_971,A_970,C_973] :
      ( k2_mcart_1(k1_mcart_1(E_972)) = k10_mcart_1(A_970,B_974,C_973,D_971,E_972)
      | ~ m1_subset_1(E_972,k4_zfmisc_1(A_970,B_974,C_973,D_971))
      | k1_xboole_0 = D_971
      | k1_xboole_0 = C_973
      | k1_xboole_0 = B_974
      | k1_xboole_0 = A_970 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6483,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_6480])).

tff(c_6486,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6477,c_6483])).

tff(c_6657,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_6486])).

tff(c_6576,plain,(
    ! [A_990,B_991,B_992] :
      ( r2_hidden('#skF_1'(A_990,B_991),B_992)
      | ~ r1_tarski(A_990,B_992)
      | r1_tarski(A_990,B_991) ) ),
    inference(resolution,[status(thm)],[c_6,c_4358])).

tff(c_6635,plain,(
    ! [B_999,A_1000,B_1001] :
      ( ~ r1_tarski(B_999,'#skF_1'(A_1000,B_1001))
      | ~ r1_tarski(A_1000,B_999)
      | r1_tarski(A_1000,B_1001) ) ),
    inference(resolution,[status(thm)],[c_6576,c_14])).

tff(c_6645,plain,(
    ! [A_1000,B_1001] :
      ( ~ r1_tarski(A_1000,k1_xboole_0)
      | r1_tarski(A_1000,B_1001) ) ),
    inference(resolution,[status(thm)],[c_8,c_6635])).

tff(c_6724,plain,(
    ! [A_1009,B_1010] :
      ( ~ r1_tarski(A_1009,'#skF_3')
      | r1_tarski(A_1009,B_1010) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6657,c_6645])).

tff(c_6737,plain,(
    ! [B_1010] : r1_tarski('#skF_7',B_1010) ),
    inference(resolution,[status(thm)],[c_2553,c_6724])).

tff(c_6211,plain,(
    r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_4345])).

tff(c_6253,plain,(
    ~ r1_tarski('#skF_7',k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')) ),
    inference(resolution,[status(thm)],[c_6211,c_14])).

tff(c_6743,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6737,c_6253])).

tff(c_6745,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_6486])).

tff(c_6605,plain,(
    ! [B_997,D_994,C_996,E_995,A_993] :
      ( k9_mcart_1(A_993,B_997,C_996,D_994,E_995) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E_995)))
      | ~ m1_subset_1(E_995,k4_zfmisc_1(A_993,B_997,C_996,D_994))
      | k1_xboole_0 = D_994
      | k1_xboole_0 = C_996
      | k1_xboole_0 = B_997
      | k1_xboole_0 = A_993 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6607,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_6605])).

tff(c_6610,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6477,c_6607])).

tff(c_6795,plain,
    ( k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_6745,c_6610])).

tff(c_6796,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_6795])).

tff(c_6813,plain,(
    ! [A_1020] : r1_tarski('#skF_4',A_1020) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6796,c_8])).

tff(c_6604,plain,(
    ! [B_992,A_990,B_991] :
      ( ~ r1_tarski(B_992,'#skF_1'(A_990,B_991))
      | ~ r1_tarski(A_990,B_992)
      | r1_tarski(A_990,B_991) ) ),
    inference(resolution,[status(thm)],[c_6576,c_14])).

tff(c_6879,plain,(
    ! [A_1025,B_1026] :
      ( ~ r1_tarski(A_1025,'#skF_4')
      | r1_tarski(A_1025,B_1026) ) ),
    inference(resolution,[status(thm)],[c_6813,c_6604])).

tff(c_6892,plain,(
    ! [B_1026] : r1_tarski('#skF_8',B_1026) ),
    inference(resolution,[status(thm)],[c_2551,c_6879])).

tff(c_7040,plain,(
    ! [A_1052,C_1053,B_1051,A_1050,D_1054] :
      ( r2_hidden(k1_mcart_1(A_1052),k3_zfmisc_1(A_1050,B_1051,C_1053))
      | ~ r2_hidden(A_1052,k4_zfmisc_1(A_1050,B_1051,C_1053,D_1054)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_22])).

tff(c_7075,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_7040])).

tff(c_4395,plain,(
    ! [A_700,C_13,A_11,B_12] :
      ( r2_hidden(k2_mcart_1(A_700),C_13)
      | ~ r2_hidden(A_700,k3_zfmisc_1(A_11,B_12,C_13)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_4393])).

tff(c_7086,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_7075,c_4395])).

tff(c_7093,plain,(
    ~ r1_tarski('#skF_8',k2_mcart_1(k1_mcart_1('#skF_10'))) ),
    inference(resolution,[status(thm)],[c_7086,c_14])).

tff(c_7100,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6892,c_7093])).

tff(c_7102,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_6795])).

tff(c_6542,plain,(
    ! [E_983,B_985,D_982,A_981,C_984] :
      ( k8_mcart_1(A_981,B_985,C_984,D_982,E_983) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E_983)))
      | ~ m1_subset_1(E_983,k4_zfmisc_1(A_981,B_985,C_984,D_982))
      | k1_xboole_0 = D_982
      | k1_xboole_0 = C_984
      | k1_xboole_0 = B_985
      | k1_xboole_0 = A_981 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6544,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_36,c_6542])).

tff(c_6547,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_6477,c_6544])).

tff(c_7103,plain,
    ( k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))) = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_6745,c_7102,c_6547])).

tff(c_7104,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_7103])).

tff(c_6212,plain,(
    ! [B_928] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_928)
      | ~ r1_tarski('#skF_9',B_928) ) ),
    inference(resolution,[status(thm)],[c_4483,c_2])).

tff(c_6264,plain,(
    ! [B_937,B_938] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_937)
      | ~ r1_tarski(B_938,B_937)
      | ~ r1_tarski('#skF_9',B_938) ) ),
    inference(resolution,[status(thm)],[c_6212,c_2])).

tff(c_6268,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_5')
    | ~ r1_tarski('#skF_9','#skF_9') ),
    inference(resolution,[status(thm)],[c_2552,c_6264])).

tff(c_6280,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_6268])).

tff(c_6488,plain,(
    ! [B_975] :
      ( r2_hidden(k2_mcart_1('#skF_10'),B_975)
      | ~ r1_tarski('#skF_5',B_975) ) ),
    inference(resolution,[status(thm)],[c_6280,c_2])).

tff(c_6513,plain,(
    ! [B_976] :
      ( ~ r1_tarski(B_976,k2_mcart_1('#skF_10'))
      | ~ r1_tarski('#skF_5',B_976) ) ),
    inference(resolution,[status(thm)],[c_6488,c_14])).

tff(c_6523,plain,(
    ~ r1_tarski('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_6513])).

tff(c_7112,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7104,c_6523])).

tff(c_7120,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2569,c_7112])).

tff(c_7122,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_7103])).

tff(c_6744,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_5'
    | k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_6486])).

tff(c_7163,plain,(
    k2_mcart_1(k1_mcart_1('#skF_10')) = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_7122,c_7102,c_6744])).

tff(c_7365,plain,(
    ! [A_1091,C_1094,A_1093,D_1095,B_1092] :
      ( r2_hidden(k1_mcart_1(A_1093),k3_zfmisc_1(A_1091,B_1092,C_1094))
      | ~ r2_hidden(A_1093,k4_zfmisc_1(A_1091,B_1092,C_1094,D_1095)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4432,c_22])).

tff(c_7400,plain,(
    r2_hidden(k1_mcart_1('#skF_10'),k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_34,c_7365])).

tff(c_7407,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')),'#skF_8') ),
    inference(resolution,[status(thm)],[c_7400,c_4395])).

tff(c_7415,plain,(
    r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7163,c_7407])).

tff(c_7417,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6210,c_7415])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:53:47 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.87/2.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.48  
% 6.87/2.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.87/2.48  %$ r2_hidden > r1_tarski > m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4 > #skF_1
% 6.87/2.48  
% 6.87/2.48  %Foreground sorts:
% 6.87/2.48  
% 6.87/2.48  
% 6.87/2.48  %Background operators:
% 6.87/2.48  
% 6.87/2.48  
% 6.87/2.48  %Foreground operators:
% 6.87/2.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.87/2.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.87/2.48  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.87/2.48  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 6.87/2.48  tff('#skF_7', type, '#skF_7': $i).
% 6.87/2.48  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.87/2.48  tff('#skF_10', type, '#skF_10': $i).
% 6.87/2.48  tff('#skF_5', type, '#skF_5': $i).
% 6.87/2.48  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.48  tff('#skF_6', type, '#skF_6': $i).
% 6.87/2.48  tff('#skF_2', type, '#skF_2': $i).
% 6.87/2.48  tff('#skF_3', type, '#skF_3': $i).
% 6.87/2.48  tff('#skF_9', type, '#skF_9': $i).
% 6.87/2.48  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.87/2.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.87/2.48  tff('#skF_8', type, '#skF_8': $i).
% 6.87/2.48  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.87/2.48  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.87/2.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.87/2.48  tff('#skF_4', type, '#skF_4': $i).
% 6.87/2.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.87/2.48  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.87/2.48  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 6.87/2.48  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.87/2.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.87/2.48  
% 7.21/2.52  tff(f_45, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.21/2.52  tff(f_103, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k1_zfmisc_1(A)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(B)) => (![G]: (m1_subset_1(G, k1_zfmisc_1(C)) => (![H]: (m1_subset_1(H, k1_zfmisc_1(D)) => (![I]: (m1_subset_1(I, k4_zfmisc_1(A, B, C, D)) => (r2_hidden(I, k4_zfmisc_1(E, F, G, H)) => (((r2_hidden(k8_mcart_1(A, B, C, D, I), E) & r2_hidden(k9_mcart_1(A, B, C, D, I), F)) & r2_hidden(k10_mcart_1(A, B, C, D, I), G)) & r2_hidden(k11_mcart_1(A, B, C, D, I), H))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_mcart_1)).
% 7.21/2.52  tff(f_38, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 7.21/2.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.21/2.52  tff(f_47, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 7.21/2.52  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.21/2.52  tff(f_78, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_mcart_1)).
% 7.21/2.52  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.21/2.52  tff(f_43, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 7.21/2.52  tff(c_16, plain, (![A_11, B_12, C_13]: (k2_zfmisc_1(k2_zfmisc_1(A_11, B_12), C_13)=k3_zfmisc_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.21/2.52  tff(c_40, plain, (m1_subset_1('#skF_8', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.21/2.52  tff(c_2534, plain, (![A_434, B_435]: (r1_tarski(A_434, B_435) | ~m1_subset_1(A_434, k1_zfmisc_1(B_435)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.21/2.52  tff(c_2551, plain, (r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_2534])).
% 7.21/2.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.52  tff(c_2564, plain, (![A_438, B_439]: (~r2_hidden('#skF_1'(A_438, B_439), B_439) | r1_tarski(A_438, B_439))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.52  tff(c_2569, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_2564])).
% 7.21/2.52  tff(c_42, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.21/2.52  tff(c_2553, plain, (r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_2534])).
% 7.21/2.52  tff(c_34, plain, (r2_hidden('#skF_10', k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.21/2.52  tff(c_2630, plain, (![A_460, B_461, C_462, D_463]: (k2_zfmisc_1(k3_zfmisc_1(A_460, B_461, C_462), D_463)=k4_zfmisc_1(A_460, B_461, C_462, D_463))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.21/2.52  tff(c_20, plain, (![A_18, C_20, B_19]: (r2_hidden(k2_mcart_1(A_18), C_20) | ~r2_hidden(A_18, k2_zfmisc_1(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.52  tff(c_2666, plain, (![C_467, A_466, B_469, D_465, A_468]: (r2_hidden(k2_mcart_1(A_466), D_465) | ~r2_hidden(A_466, k4_zfmisc_1(A_468, B_469, C_467, D_465)))), inference(superposition, [status(thm), theory('equality')], [c_2630, c_20])).
% 7.21/2.52  tff(c_2677, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_34, c_2666])).
% 7.21/2.52  tff(c_44, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.21/2.52  tff(c_2554, plain, (r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_2534])).
% 7.21/2.52  tff(c_36, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.21/2.52  tff(c_2720, plain, (![A_472, E_474, D_473, C_475, B_476]: (k11_mcart_1(A_472, B_476, C_475, D_473, E_474)=k2_mcart_1(E_474) | ~m1_subset_1(E_474, k4_zfmisc_1(A_472, B_476, C_475, D_473)) | k1_xboole_0=D_473 | k1_xboole_0=C_475 | k1_xboole_0=B_476 | k1_xboole_0=A_472)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_2724, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_2720])).
% 7.21/2.52  tff(c_2735, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_2724])).
% 7.21/2.52  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.21/2.52  tff(c_2738, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_2735, c_8])).
% 7.21/2.52  tff(c_32, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.21/2.52  tff(c_52, plain, (~r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitLeft, [status(thm)], [c_32])).
% 7.21/2.52  tff(c_79, plain, (![A_62, B_63]: (~r2_hidden('#skF_1'(A_62, B_63), B_63) | r1_tarski(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.52  tff(c_84, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(resolution, [status(thm)], [c_6, c_79])).
% 7.21/2.52  tff(c_53, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.21/2.52  tff(c_72, plain, (r1_tarski('#skF_7', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_53])).
% 7.21/2.52  tff(c_73, plain, (r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_53])).
% 7.21/2.52  tff(c_182, plain, (![D_92, B_95, C_94, A_91, E_93]: (k11_mcart_1(A_91, B_95, C_94, D_92, E_93)=k2_mcart_1(E_93) | ~m1_subset_1(E_93, k4_zfmisc_1(A_91, B_95, C_94, D_92)) | k1_xboole_0=D_92 | k1_xboole_0=C_94 | k1_xboole_0=B_95 | k1_xboole_0=A_91)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_186, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_182])).
% 7.21/2.52  tff(c_274, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_186])).
% 7.21/2.52  tff(c_278, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_274, c_8])).
% 7.21/2.52  tff(c_93, plain, (![C_67, B_68, A_69]: (r2_hidden(C_67, B_68) | ~r2_hidden(C_67, A_69) | ~r1_tarski(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.52  tff(c_157, plain, (![A_88, B_89, B_90]: (r2_hidden('#skF_1'(A_88, B_89), B_90) | ~r1_tarski(A_88, B_90) | r1_tarski(A_88, B_89))), inference(resolution, [status(thm)], [c_6, c_93])).
% 7.21/2.52  tff(c_14, plain, (![B_10, A_9]: (~r1_tarski(B_10, A_9) | ~r2_hidden(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.21/2.52  tff(c_410, plain, (![B_140, A_141, B_142]: (~r1_tarski(B_140, '#skF_1'(A_141, B_142)) | ~r1_tarski(A_141, B_140) | r1_tarski(A_141, B_142))), inference(resolution, [status(thm)], [c_157, c_14])).
% 7.21/2.52  tff(c_421, plain, (![A_143, B_144]: (~r1_tarski(A_143, '#skF_2') | r1_tarski(A_143, B_144))), inference(resolution, [status(thm)], [c_278, c_410])).
% 7.21/2.52  tff(c_434, plain, (![B_144]: (r1_tarski('#skF_6', B_144))), inference(resolution, [status(thm)], [c_73, c_421])).
% 7.21/2.52  tff(c_122, plain, (![A_76, B_77, C_78]: (r2_hidden(k1_mcart_1(A_76), B_77) | ~r2_hidden(A_76, k2_zfmisc_1(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.52  tff(c_517, plain, (![B_163, C_164, B_165]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_163, C_164), B_165)), B_163) | r1_tarski(k2_zfmisc_1(B_163, C_164), B_165))), inference(resolution, [status(thm)], [c_6, c_122])).
% 7.21/2.52  tff(c_593, plain, (![B_169, C_170, B_171]: (~r1_tarski(B_169, k1_mcart_1('#skF_1'(k2_zfmisc_1(B_169, C_170), B_171))) | r1_tarski(k2_zfmisc_1(B_169, C_170), B_171))), inference(resolution, [status(thm)], [c_517, c_14])).
% 7.21/2.52  tff(c_612, plain, (![C_172, B_173]: (r1_tarski(k2_zfmisc_1('#skF_6', C_172), B_173))), inference(resolution, [status(thm)], [c_434, c_593])).
% 7.21/2.52  tff(c_554, plain, (![B_163, C_164, B_165]: (~r1_tarski(B_163, k1_mcart_1('#skF_1'(k2_zfmisc_1(B_163, C_164), B_165))) | r1_tarski(k2_zfmisc_1(B_163, C_164), B_165))), inference(resolution, [status(thm)], [c_517, c_14])).
% 7.21/2.52  tff(c_616, plain, (![C_172, C_164, B_165]: (r1_tarski(k2_zfmisc_1(k2_zfmisc_1('#skF_6', C_172), C_164), B_165))), inference(resolution, [status(thm)], [c_612, c_554])).
% 7.21/2.52  tff(c_644, plain, (![C_172, C_164, B_165]: (r1_tarski(k3_zfmisc_1('#skF_6', C_172, C_164), B_165))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_616])).
% 7.21/2.52  tff(c_129, plain, (![A_79, B_80, C_81, D_82]: (k2_zfmisc_1(k3_zfmisc_1(A_79, B_80, C_81), D_82)=k4_zfmisc_1(A_79, B_80, C_81, D_82))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.21/2.52  tff(c_22, plain, (![A_18, B_19, C_20]: (r2_hidden(k1_mcart_1(A_18), B_19) | ~r2_hidden(A_18, k2_zfmisc_1(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.52  tff(c_704, plain, (![A_181, A_182, C_183, B_184, D_180]: (r2_hidden(k1_mcart_1(A_181), k3_zfmisc_1(A_182, B_184, C_183)) | ~r2_hidden(A_181, k4_zfmisc_1(A_182, B_184, C_183, D_180)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_22])).
% 7.21/2.52  tff(c_731, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_704])).
% 7.21/2.52  tff(c_829, plain, (~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_mcart_1('#skF_10'))), inference(resolution, [status(thm)], [c_731, c_14])).
% 7.21/2.52  tff(c_838, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_644, c_829])).
% 7.21/2.52  tff(c_840, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_186])).
% 7.21/2.52  tff(c_241, plain, (![D_104, B_107, E_105, C_106, A_103]: (k2_mcart_1(k1_mcart_1(E_105))=k10_mcart_1(A_103, B_107, C_106, D_104, E_105) | ~m1_subset_1(E_105, k4_zfmisc_1(A_103, B_107, C_106, D_104)) | k1_xboole_0=D_104 | k1_xboole_0=C_106 | k1_xboole_0=B_107 | k1_xboole_0=A_103)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_245, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_241])).
% 7.21/2.52  tff(c_850, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_840, c_245])).
% 7.21/2.52  tff(c_851, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_850])).
% 7.21/2.52  tff(c_857, plain, (![A_6]: (r1_tarski('#skF_3', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_851, c_8])).
% 7.21/2.52  tff(c_985, plain, (![B_220, A_221, B_222]: (~r1_tarski(B_220, '#skF_1'(A_221, B_222)) | ~r1_tarski(A_221, B_220) | r1_tarski(A_221, B_222))), inference(resolution, [status(thm)], [c_157, c_14])).
% 7.21/2.52  tff(c_996, plain, (![A_223, B_224]: (~r1_tarski(A_223, '#skF_3') | r1_tarski(A_223, B_224))), inference(resolution, [status(thm)], [c_857, c_985])).
% 7.21/2.52  tff(c_1009, plain, (![B_224]: (r1_tarski('#skF_7', B_224))), inference(resolution, [status(thm)], [c_72, c_996])).
% 7.21/2.52  tff(c_115, plain, (![A_73, C_74, B_75]: (r2_hidden(k2_mcart_1(A_73), C_74) | ~r2_hidden(A_73, k2_zfmisc_1(B_75, C_74)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.52  tff(c_1089, plain, (![B_242, C_243, B_244]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_242, C_243), B_244)), C_243) | r1_tarski(k2_zfmisc_1(B_242, C_243), B_244))), inference(resolution, [status(thm)], [c_6, c_115])).
% 7.21/2.52  tff(c_1170, plain, (![C_255, B_256, B_257]: (~r1_tarski(C_255, k2_mcart_1('#skF_1'(k2_zfmisc_1(B_256, C_255), B_257))) | r1_tarski(k2_zfmisc_1(B_256, C_255), B_257))), inference(resolution, [status(thm)], [c_1089, c_14])).
% 7.21/2.52  tff(c_1185, plain, (![B_256, B_257]: (r1_tarski(k2_zfmisc_1(B_256, '#skF_7'), B_257))), inference(resolution, [status(thm)], [c_1009, c_1170])).
% 7.21/2.52  tff(c_1476, plain, (![C_282, B_283, A_280, A_281, D_279]: (r2_hidden(k1_mcart_1(A_280), k3_zfmisc_1(A_281, B_283, C_282)) | ~r2_hidden(A_280, k4_zfmisc_1(A_281, B_283, C_282, D_279)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_22])).
% 7.21/2.52  tff(c_1503, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_1476])).
% 7.21/2.52  tff(c_124, plain, (![A_76, A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_76), k2_zfmisc_1(A_11, B_12)) | ~r2_hidden(A_76, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_122])).
% 7.21/2.52  tff(c_1531, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_1503, c_124])).
% 7.21/2.52  tff(c_1567, plain, (~r1_tarski(k2_zfmisc_1('#skF_6', '#skF_7'), k1_mcart_1(k1_mcart_1('#skF_10')))), inference(resolution, [status(thm)], [c_1531, c_14])).
% 7.21/2.52  tff(c_1576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1185, c_1567])).
% 7.21/2.52  tff(c_1578, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_850])).
% 7.21/2.52  tff(c_70, plain, (r1_tarski('#skF_8', '#skF_4')), inference(resolution, [status(thm)], [c_40, c_53])).
% 7.21/2.52  tff(c_1630, plain, (![E_303, B_305, D_302, A_301, C_304]: (k9_mcart_1(A_301, B_305, C_304, D_302, E_303)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_303))) | ~m1_subset_1(E_303, k4_zfmisc_1(A_301, B_305, C_304, D_302)) | k1_xboole_0=D_302 | k1_xboole_0=C_304 | k1_xboole_0=B_305 | k1_xboole_0=A_301)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_1632, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_1630])).
% 7.21/2.52  tff(c_1635, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_840, c_1578, c_1632])).
% 7.21/2.52  tff(c_1715, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1635])).
% 7.21/2.52  tff(c_1690, plain, (![B_316, A_317, B_318]: (~r1_tarski(B_316, '#skF_1'(A_317, B_318)) | ~r1_tarski(A_317, B_316) | r1_tarski(A_317, B_318))), inference(resolution, [status(thm)], [c_157, c_14])).
% 7.21/2.52  tff(c_1700, plain, (![A_317, B_318]: (~r1_tarski(A_317, k1_xboole_0) | r1_tarski(A_317, B_318))), inference(resolution, [status(thm)], [c_8, c_1690])).
% 7.21/2.52  tff(c_1780, plain, (![A_329, B_330]: (~r1_tarski(A_329, '#skF_4') | r1_tarski(A_329, B_330))), inference(demodulation, [status(thm), theory('equality')], [c_1715, c_1700])).
% 7.21/2.52  tff(c_1793, plain, (![B_330]: (r1_tarski('#skF_8', B_330))), inference(resolution, [status(thm)], [c_70, c_1780])).
% 7.21/2.52  tff(c_2040, plain, (![A_364, B_367, D_363, A_365, C_366]: (r2_hidden(k1_mcart_1(A_364), k3_zfmisc_1(A_365, B_367, C_366)) | ~r2_hidden(A_364, k4_zfmisc_1(A_365, B_367, C_366, D_363)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_22])).
% 7.21/2.52  tff(c_2067, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_2040])).
% 7.21/2.52  tff(c_117, plain, (![A_73, C_13, A_11, B_12]: (r2_hidden(k2_mcart_1(A_73), C_13) | ~r2_hidden(A_73, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_115])).
% 7.21/2.52  tff(c_2124, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_2067, c_117])).
% 7.21/2.52  tff(c_2131, plain, (~r1_tarski('#skF_8', k2_mcart_1(k1_mcart_1('#skF_10')))), inference(resolution, [status(thm)], [c_2124, c_14])).
% 7.21/2.52  tff(c_2138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1793, c_2131])).
% 7.21/2.52  tff(c_2140, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1635])).
% 7.21/2.52  tff(c_843, plain, (![C_196, A_193, D_194, E_195, B_197]: (k8_mcart_1(A_193, B_197, C_196, D_194, E_195)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_195))) | ~m1_subset_1(E_195, k4_zfmisc_1(A_193, B_197, C_196, D_194)) | k1_xboole_0=D_194 | k1_xboole_0=C_196 | k1_xboole_0=B_197 | k1_xboole_0=A_193)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_845, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_843])).
% 7.21/2.52  tff(c_848, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_840, c_845])).
% 7.21/2.52  tff(c_2170, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_1578, c_2140, c_848])).
% 7.21/2.52  tff(c_2171, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_2170])).
% 7.21/2.52  tff(c_38, plain, (m1_subset_1('#skF_9', k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 7.21/2.52  tff(c_71, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_53])).
% 7.21/2.52  tff(c_187, plain, (![C_99, A_98, D_96, B_100, A_97]: (r2_hidden(k2_mcart_1(A_97), D_96) | ~r2_hidden(A_97, k4_zfmisc_1(A_98, B_100, C_99, D_96)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_20])).
% 7.21/2.52  tff(c_198, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_34, c_187])).
% 7.21/2.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.52  tff(c_206, plain, (![B_101]: (r2_hidden(k2_mcart_1('#skF_10'), B_101) | ~r1_tarski('#skF_9', B_101))), inference(resolution, [status(thm)], [c_198, c_2])).
% 7.21/2.52  tff(c_246, plain, (![B_108, B_109]: (r2_hidden(k2_mcart_1('#skF_10'), B_108) | ~r1_tarski(B_109, B_108) | ~r1_tarski('#skF_9', B_109))), inference(resolution, [status(thm)], [c_206, c_2])).
% 7.21/2.52  tff(c_250, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_71, c_246])).
% 7.21/2.52  tff(c_262, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_250])).
% 7.21/2.52  tff(c_1579, plain, (![B_295]: (r2_hidden(k2_mcart_1('#skF_10'), B_295) | ~r1_tarski('#skF_5', B_295))), inference(resolution, [status(thm)], [c_262, c_2])).
% 7.21/2.52  tff(c_1605, plain, (![B_296]: (~r1_tarski(B_296, k2_mcart_1('#skF_10')) | ~r1_tarski('#skF_5', B_296))), inference(resolution, [status(thm)], [c_1579, c_14])).
% 7.21/2.52  tff(c_1615, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_1605])).
% 7.21/2.52  tff(c_2175, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2171, c_1615])).
% 7.21/2.52  tff(c_2185, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_2175])).
% 7.21/2.52  tff(c_2186, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_2170])).
% 7.21/2.52  tff(c_2477, plain, (![C_432, A_430, D_429, B_433, A_431]: (r2_hidden(k1_mcart_1(A_430), k3_zfmisc_1(A_431, B_433, C_432)) | ~r2_hidden(A_430, k4_zfmisc_1(A_431, B_433, C_432, D_429)))), inference(superposition, [status(thm), theory('equality')], [c_129, c_22])).
% 7.21/2.52  tff(c_2504, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_2477])).
% 7.21/2.52  tff(c_2514, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_2504, c_124])).
% 7.21/2.52  tff(c_2520, plain, (r2_hidden(k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_6')), inference(resolution, [status(thm)], [c_2514, c_22])).
% 7.21/2.52  tff(c_2529, plain, (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2186, c_2520])).
% 7.21/2.52  tff(c_2531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_2529])).
% 7.21/2.52  tff(c_2533, plain, (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_6')), inference(splitRight, [status(thm)], [c_32])).
% 7.21/2.52  tff(c_2601, plain, (![C_449, B_450, A_451]: (r2_hidden(C_449, B_450) | ~r2_hidden(C_449, A_451) | ~r1_tarski(A_451, B_450))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.52  tff(c_2646, plain, (![B_464]: (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), B_464) | ~r1_tarski('#skF_6', B_464))), inference(resolution, [status(thm)], [c_2533, c_2601])).
% 7.21/2.52  tff(c_2839, plain, (![B_498]: (~r1_tarski(B_498, k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~r1_tarski('#skF_6', B_498))), inference(resolution, [status(thm)], [c_2646, c_14])).
% 7.21/2.52  tff(c_2843, plain, (~r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_2738, c_2839])).
% 7.21/2.52  tff(c_2851, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2554, c_2843])).
% 7.21/2.52  tff(c_2852, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitRight, [status(thm)], [c_2724])).
% 7.21/2.52  tff(c_3023, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10')), inference(splitLeft, [status(thm)], [c_2852])).
% 7.21/2.52  tff(c_2532, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7') | ~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitRight, [status(thm)], [c_32])).
% 7.21/2.52  tff(c_2571, plain, (~r2_hidden(k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_9')), inference(splitLeft, [status(thm)], [c_2532])).
% 7.21/2.52  tff(c_3035, plain, (~r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(demodulation, [status(thm), theory('equality')], [c_3023, c_2571])).
% 7.21/2.52  tff(c_3038, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2677, c_3035])).
% 7.21/2.52  tff(c_3039, plain, (k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_2852])).
% 7.21/2.52  tff(c_3041, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_3039])).
% 7.21/2.52  tff(c_2966, plain, (![A_519, B_520, B_521]: (r2_hidden('#skF_1'(A_519, B_520), B_521) | ~r1_tarski(A_519, B_521) | r1_tarski(A_519, B_520))), inference(resolution, [status(thm)], [c_6, c_2601])).
% 7.21/2.52  tff(c_3012, plain, (![B_528, A_529, B_530]: (~r1_tarski(B_528, '#skF_1'(A_529, B_530)) | ~r1_tarski(A_529, B_528) | r1_tarski(A_529, B_530))), inference(resolution, [status(thm)], [c_2966, c_14])).
% 7.21/2.52  tff(c_3022, plain, (![A_529, B_530]: (~r1_tarski(A_529, k1_xboole_0) | r1_tarski(A_529, B_530))), inference(resolution, [status(thm)], [c_8, c_3012])).
% 7.21/2.52  tff(c_3090, plain, (![A_534, B_535]: (~r1_tarski(A_534, '#skF_3') | r1_tarski(A_534, B_535))), inference(demodulation, [status(thm), theory('equality')], [c_3041, c_3022])).
% 7.21/2.52  tff(c_3103, plain, (![B_535]: (r1_tarski('#skF_7', B_535))), inference(resolution, [status(thm)], [c_2553, c_3090])).
% 7.21/2.52  tff(c_3556, plain, (![B_606, C_604, A_605, A_603, D_602]: (r2_hidden(k1_mcart_1(A_603), k3_zfmisc_1(A_605, B_606, C_604)) | ~r2_hidden(A_603, k4_zfmisc_1(A_605, B_606, C_604, D_602)))), inference(superposition, [status(thm), theory('equality')], [c_2630, c_22])).
% 7.21/2.52  tff(c_3587, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_3556])).
% 7.21/2.52  tff(c_2594, plain, (![A_446, B_447, C_448]: (r2_hidden(k1_mcart_1(A_446), B_447) | ~r2_hidden(A_446, k2_zfmisc_1(B_447, C_448)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.52  tff(c_2596, plain, (![A_446, A_11, B_12, C_13]: (r2_hidden(k1_mcart_1(A_446), k2_zfmisc_1(A_11, B_12)) | ~r2_hidden(A_446, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_2594])).
% 7.21/2.52  tff(c_3599, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_3587, c_2596])).
% 7.21/2.52  tff(c_3619, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_7')), inference(resolution, [status(thm)], [c_3599, c_20])).
% 7.21/2.52  tff(c_3627, plain, (~r1_tarski('#skF_7', k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))))), inference(resolution, [status(thm)], [c_3619, c_14])).
% 7.21/2.52  tff(c_3634, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3103, c_3627])).
% 7.21/2.52  tff(c_3635, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_3039])).
% 7.21/2.52  tff(c_3637, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_3635])).
% 7.21/2.52  tff(c_2552, plain, (r1_tarski('#skF_9', '#skF_5')), inference(resolution, [status(thm)], [c_38, c_2534])).
% 7.21/2.52  tff(c_2685, plain, (![B_470]: (r2_hidden(k2_mcart_1('#skF_10'), B_470) | ~r1_tarski('#skF_9', B_470))), inference(resolution, [status(thm)], [c_2677, c_2])).
% 7.21/2.52  tff(c_2854, plain, (![B_499, B_500]: (r2_hidden(k2_mcart_1('#skF_10'), B_499) | ~r1_tarski(B_500, B_499) | ~r1_tarski('#skF_9', B_500))), inference(resolution, [status(thm)], [c_2685, c_2])).
% 7.21/2.52  tff(c_2858, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_2552, c_2854])).
% 7.21/2.52  tff(c_2870, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2569, c_2858])).
% 7.21/2.52  tff(c_2892, plain, (![B_506]: (r2_hidden(k2_mcart_1('#skF_10'), B_506) | ~r1_tarski('#skF_5', B_506))), inference(resolution, [status(thm)], [c_2870, c_2])).
% 7.21/2.52  tff(c_2916, plain, (![B_507]: (~r1_tarski(B_507, k2_mcart_1('#skF_10')) | ~r1_tarski('#skF_5', B_507))), inference(resolution, [status(thm)], [c_2892, c_14])).
% 7.21/2.52  tff(c_2926, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_2916])).
% 7.21/2.52  tff(c_3642, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_3637, c_2926])).
% 7.21/2.52  tff(c_3650, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2569, c_3642])).
% 7.21/2.52  tff(c_3651, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_3635])).
% 7.21/2.52  tff(c_3705, plain, (![A_612, B_613]: (~r1_tarski(A_612, '#skF_4') | r1_tarski(A_612, B_613))), inference(demodulation, [status(thm), theory('equality')], [c_3651, c_3022])).
% 7.21/2.52  tff(c_3718, plain, (![B_613]: (r1_tarski('#skF_8', B_613))), inference(resolution, [status(thm)], [c_2551, c_3705])).
% 7.21/2.52  tff(c_2611, plain, (![A_452, C_453, B_454]: (r2_hidden(k2_mcart_1(A_452), C_453) | ~r2_hidden(A_452, k2_zfmisc_1(B_454, C_453)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.52  tff(c_3834, plain, (![B_642, C_643, B_644]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_642, C_643), B_644)), C_643) | r1_tarski(k2_zfmisc_1(B_642, C_643), B_644))), inference(resolution, [status(thm)], [c_6, c_2611])).
% 7.21/2.52  tff(c_3910, plain, (![C_648, B_649, B_650]: (~r1_tarski(C_648, k2_mcart_1('#skF_1'(k2_zfmisc_1(B_649, C_648), B_650))) | r1_tarski(k2_zfmisc_1(B_649, C_648), B_650))), inference(resolution, [status(thm)], [c_3834, c_14])).
% 7.21/2.52  tff(c_3994, plain, (![B_654, B_655]: (r1_tarski(k2_zfmisc_1(B_654, '#skF_8'), B_655))), inference(resolution, [status(thm)], [c_3718, c_3910])).
% 7.21/2.52  tff(c_4036, plain, (![A_11, B_12, B_655]: (r1_tarski(k3_zfmisc_1(A_11, B_12, '#skF_8'), B_655))), inference(superposition, [status(thm), theory('equality')], [c_16, c_3994])).
% 7.21/2.52  tff(c_4286, plain, (![B_686, A_685, C_684, A_683, D_682]: (r2_hidden(k1_mcart_1(A_683), k3_zfmisc_1(A_685, B_686, C_684)) | ~r2_hidden(A_683, k4_zfmisc_1(A_685, B_686, C_684, D_682)))), inference(superposition, [status(thm), theory('equality')], [c_2630, c_22])).
% 7.21/2.52  tff(c_4317, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_4286])).
% 7.21/2.52  tff(c_4335, plain, (~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_mcart_1('#skF_10'))), inference(resolution, [status(thm)], [c_4317, c_14])).
% 7.21/2.52  tff(c_4344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4036, c_4335])).
% 7.21/2.52  tff(c_4345, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8') | ~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_2532])).
% 7.21/2.52  tff(c_4491, plain, (~r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitLeft, [status(thm)], [c_4345])).
% 7.21/2.52  tff(c_4565, plain, (![A_727, C_730, E_729, D_728, B_731]: (k11_mcart_1(A_727, B_731, C_730, D_728, E_729)=k2_mcart_1(E_729) | ~m1_subset_1(E_729, k4_zfmisc_1(A_727, B_731, C_730, D_728)) | k1_xboole_0=D_728 | k1_xboole_0=C_730 | k1_xboole_0=B_731 | k1_xboole_0=A_727)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_4569, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4565])).
% 7.21/2.52  tff(c_4572, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_4569])).
% 7.21/2.52  tff(c_4575, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_4572, c_8])).
% 7.21/2.52  tff(c_4358, plain, (![C_691, B_692, A_693]: (r2_hidden(C_691, B_692) | ~r2_hidden(C_691, A_693) | ~r1_tarski(A_693, B_692))), inference(cnfTransformation, [status(thm)], [f_32])).
% 7.21/2.52  tff(c_4412, plain, (![B_708]: (r2_hidden(k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), B_708) | ~r1_tarski('#skF_6', B_708))), inference(resolution, [status(thm)], [c_2533, c_4358])).
% 7.21/2.52  tff(c_4603, plain, (![B_738]: (~r1_tarski(B_738, k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~r1_tarski('#skF_6', B_738))), inference(resolution, [status(thm)], [c_4412, c_14])).
% 7.21/2.52  tff(c_4607, plain, (~r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_4575, c_4603])).
% 7.21/2.52  tff(c_4615, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2554, c_4607])).
% 7.21/2.52  tff(c_4617, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_4569])).
% 7.21/2.52  tff(c_4643, plain, (![D_741, A_740, C_743, E_742, B_744]: (k2_mcart_1(k1_mcart_1(E_742))=k10_mcart_1(A_740, B_744, C_743, D_741, E_742) | ~m1_subset_1(E_742, k4_zfmisc_1(A_740, B_744, C_743, D_741)) | k1_xboole_0=D_741 | k1_xboole_0=C_743 | k1_xboole_0=B_744 | k1_xboole_0=A_740)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_4646, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4643])).
% 7.21/2.52  tff(c_4649, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4617, c_4646])).
% 7.21/2.52  tff(c_4779, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_4649])).
% 7.21/2.52  tff(c_4794, plain, (![A_774]: (r1_tarski('#skF_3', A_774))), inference(demodulation, [status(thm), theory('equality')], [c_4779, c_8])).
% 7.21/2.52  tff(c_4700, plain, (![A_757, B_758, B_759]: (r2_hidden('#skF_1'(A_757, B_758), B_759) | ~r1_tarski(A_757, B_759) | r1_tarski(A_757, B_758))), inference(resolution, [status(thm)], [c_6, c_4358])).
% 7.21/2.52  tff(c_4728, plain, (![B_759, A_757, B_758]: (~r1_tarski(B_759, '#skF_1'(A_757, B_758)) | ~r1_tarski(A_757, B_759) | r1_tarski(A_757, B_758))), inference(resolution, [status(thm)], [c_4700, c_14])).
% 7.21/2.52  tff(c_4851, plain, (![A_779, B_780]: (~r1_tarski(A_779, '#skF_3') | r1_tarski(A_779, B_780))), inference(resolution, [status(thm)], [c_4794, c_4728])).
% 7.21/2.52  tff(c_4864, plain, (![B_780]: (r1_tarski('#skF_7', B_780))), inference(resolution, [status(thm)], [c_2553, c_4851])).
% 7.21/2.52  tff(c_4432, plain, (![A_709, B_710, C_711, D_712]: (k2_zfmisc_1(k3_zfmisc_1(A_709, B_710, C_711), D_712)=k4_zfmisc_1(A_709, B_710, C_711, D_712))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.21/2.52  tff(c_5100, plain, (![B_815, A_816, D_818, C_817, A_814]: (r2_hidden(k1_mcart_1(A_816), k3_zfmisc_1(A_814, B_815, C_817)) | ~r2_hidden(A_816, k4_zfmisc_1(A_814, B_815, C_817, D_818)))), inference(superposition, [status(thm), theory('equality')], [c_4432, c_22])).
% 7.21/2.52  tff(c_5131, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_5100])).
% 7.21/2.52  tff(c_4376, plain, (![A_697, B_698, C_699]: (k2_zfmisc_1(k2_zfmisc_1(A_697, B_698), C_699)=k3_zfmisc_1(A_697, B_698, C_699))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.21/2.52  tff(c_4384, plain, (![A_18, A_697, B_698, C_699]: (r2_hidden(k1_mcart_1(A_18), k2_zfmisc_1(A_697, B_698)) | ~r2_hidden(A_18, k3_zfmisc_1(A_697, B_698, C_699)))), inference(superposition, [status(thm), theory('equality')], [c_4376, c_22])).
% 7.21/2.52  tff(c_5192, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_5131, c_4384])).
% 7.21/2.52  tff(c_5302, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_7')), inference(resolution, [status(thm)], [c_5192, c_20])).
% 7.21/2.52  tff(c_5310, plain, (~r1_tarski('#skF_7', k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))))), inference(resolution, [status(thm)], [c_5302, c_14])).
% 7.21/2.52  tff(c_5317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4864, c_5310])).
% 7.21/2.52  tff(c_5319, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_4649])).
% 7.21/2.52  tff(c_4771, plain, (![E_768, D_767, B_770, A_766, C_769]: (k8_mcart_1(A_766, B_770, C_769, D_767, E_768)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_768))) | ~m1_subset_1(E_768, k4_zfmisc_1(A_766, B_770, C_769, D_767)) | k1_xboole_0=D_767 | k1_xboole_0=C_769 | k1_xboole_0=B_770 | k1_xboole_0=A_766)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_4773, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4771])).
% 7.21/2.52  tff(c_4776, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4617, c_4773])).
% 7.21/2.52  tff(c_5372, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_5319, c_4776])).
% 7.21/2.52  tff(c_5373, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_5372])).
% 7.21/2.52  tff(c_4749, plain, (![B_761, A_762, B_763]: (~r1_tarski(B_761, '#skF_1'(A_762, B_763)) | ~r1_tarski(A_762, B_761) | r1_tarski(A_762, B_763))), inference(resolution, [status(thm)], [c_4700, c_14])).
% 7.21/2.52  tff(c_4759, plain, (![A_762, B_763]: (~r1_tarski(A_762, k1_xboole_0) | r1_tarski(A_762, B_763))), inference(resolution, [status(thm)], [c_8, c_4749])).
% 7.21/2.52  tff(c_5425, plain, (![A_854, B_855]: (~r1_tarski(A_854, '#skF_4') | r1_tarski(A_854, B_855))), inference(demodulation, [status(thm), theory('equality')], [c_5373, c_4759])).
% 7.21/2.52  tff(c_5438, plain, (![B_855]: (r1_tarski('#skF_8', B_855))), inference(resolution, [status(thm)], [c_2551, c_5425])).
% 7.21/2.52  tff(c_4393, plain, (![A_700, C_701, B_702]: (r2_hidden(k2_mcart_1(A_700), C_701) | ~r2_hidden(A_700, k2_zfmisc_1(B_702, C_701)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.21/2.52  tff(c_5478, plain, (![B_857, C_858, B_859]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_857, C_858), B_859)), C_858) | r1_tarski(k2_zfmisc_1(B_857, C_858), B_859))), inference(resolution, [status(thm)], [c_6, c_4393])).
% 7.21/2.52  tff(c_5575, plain, (![C_872, B_873, B_874]: (~r1_tarski(C_872, k2_mcart_1('#skF_1'(k2_zfmisc_1(B_873, C_872), B_874))) | r1_tarski(k2_zfmisc_1(B_873, C_872), B_874))), inference(resolution, [status(thm)], [c_5478, c_14])).
% 7.21/2.52  tff(c_5659, plain, (![B_878, B_879]: (r1_tarski(k2_zfmisc_1(B_878, '#skF_8'), B_879))), inference(resolution, [status(thm)], [c_5438, c_5575])).
% 7.21/2.52  tff(c_5701, plain, (![A_11, B_12, B_879]: (r1_tarski(k3_zfmisc_1(A_11, B_12, '#skF_8'), B_879))), inference(superposition, [status(thm), theory('equality')], [c_16, c_5659])).
% 7.21/2.52  tff(c_5979, plain, (![C_909, B_907, A_906, D_910, A_908]: (r2_hidden(k1_mcart_1(A_908), k3_zfmisc_1(A_906, B_907, C_909)) | ~r2_hidden(A_908, k4_zfmisc_1(A_906, B_907, C_909, D_910)))), inference(superposition, [status(thm), theory('equality')], [c_4432, c_22])).
% 7.21/2.52  tff(c_6010, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_5979])).
% 7.21/2.52  tff(c_6028, plain, (~r1_tarski(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'), k1_mcart_1('#skF_10'))), inference(resolution, [status(thm)], [c_6010, c_14])).
% 7.21/2.52  tff(c_6037, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5701, c_6028])).
% 7.21/2.52  tff(c_6039, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_5372])).
% 7.21/2.52  tff(c_4684, plain, (![E_750, A_748, C_751, D_749, B_752]: (k9_mcart_1(A_748, B_752, C_751, D_749, E_750)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_750))) | ~m1_subset_1(E_750, k4_zfmisc_1(A_748, B_752, C_751, D_749)) | k1_xboole_0=D_749 | k1_xboole_0=C_751 | k1_xboole_0=B_752 | k1_xboole_0=A_748)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_4686, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_4684])).
% 7.21/2.52  tff(c_4689, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4617, c_4686])).
% 7.21/2.52  tff(c_6052, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_5319, c_6039, c_4689])).
% 7.21/2.52  tff(c_6053, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_6052])).
% 7.21/2.52  tff(c_4468, plain, (![A_716, C_717, D_718, B_715, A_714]: (r2_hidden(k2_mcart_1(A_716), D_718) | ~r2_hidden(A_716, k4_zfmisc_1(A_714, B_715, C_717, D_718)))), inference(superposition, [status(thm), theory('equality')], [c_4432, c_20])).
% 7.21/2.52  tff(c_4483, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_34, c_4468])).
% 7.21/2.52  tff(c_4492, plain, (![B_719]: (r2_hidden(k2_mcart_1('#skF_10'), B_719) | ~r1_tarski('#skF_9', B_719))), inference(resolution, [status(thm)], [c_4483, c_2])).
% 7.21/2.52  tff(c_4537, plain, (![B_725, B_726]: (r2_hidden(k2_mcart_1('#skF_10'), B_725) | ~r1_tarski(B_726, B_725) | ~r1_tarski('#skF_9', B_726))), inference(resolution, [status(thm)], [c_4492, c_2])).
% 7.21/2.52  tff(c_4541, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_2552, c_4537])).
% 7.21/2.52  tff(c_4553, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2569, c_4541])).
% 7.21/2.52  tff(c_4619, plain, (![B_739]: (r2_hidden(k2_mcart_1('#skF_10'), B_739) | ~r1_tarski('#skF_5', B_739))), inference(resolution, [status(thm)], [c_4553, c_2])).
% 7.21/2.52  tff(c_4650, plain, (![B_745]: (~r1_tarski(B_745, k2_mcart_1('#skF_10')) | ~r1_tarski('#skF_5', B_745))), inference(resolution, [status(thm)], [c_4619, c_14])).
% 7.21/2.52  tff(c_4660, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_4650])).
% 7.21/2.52  tff(c_6060, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_6053, c_4660])).
% 7.21/2.52  tff(c_6068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2569, c_6060])).
% 7.21/2.52  tff(c_6069, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_6052])).
% 7.21/2.52  tff(c_6151, plain, (![A_925, C_926, B_924, D_927, A_923]: (r2_hidden(k1_mcart_1(A_925), k3_zfmisc_1(A_923, B_924, C_926)) | ~r2_hidden(A_925, k4_zfmisc_1(A_923, B_924, C_926, D_927)))), inference(superposition, [status(thm), theory('equality')], [c_4432, c_22])).
% 7.21/2.52  tff(c_6182, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_6151])).
% 7.21/2.52  tff(c_6192, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_10')), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_6182, c_4384])).
% 7.21/2.52  tff(c_6198, plain, (r2_hidden(k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10'))), '#skF_7')), inference(resolution, [status(thm)], [c_6192, c_20])).
% 7.21/2.52  tff(c_6207, plain, (r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_6069, c_6198])).
% 7.21/2.52  tff(c_6209, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4491, c_6207])).
% 7.21/2.52  tff(c_6210, plain, (~r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(splitRight, [status(thm)], [c_4345])).
% 7.21/2.52  tff(c_6259, plain, (![E_934, A_932, C_935, B_936, D_933]: (k11_mcart_1(A_932, B_936, C_935, D_933, E_934)=k2_mcart_1(E_934) | ~m1_subset_1(E_934, k4_zfmisc_1(A_932, B_936, C_935, D_933)) | k1_xboole_0=D_933 | k1_xboole_0=C_935 | k1_xboole_0=B_936 | k1_xboole_0=A_932)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_6263, plain, (k11_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_6259])).
% 7.21/2.52  tff(c_6292, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_6263])).
% 7.21/2.52  tff(c_6295, plain, (![A_6]: (r1_tarski('#skF_2', A_6))), inference(demodulation, [status(thm), theory('equality')], [c_6292, c_8])).
% 7.21/2.52  tff(c_6463, plain, (![B_969]: (~r1_tarski(B_969, k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')) | ~r1_tarski('#skF_6', B_969))), inference(resolution, [status(thm)], [c_4412, c_14])).
% 7.21/2.52  tff(c_6467, plain, (~r1_tarski('#skF_6', '#skF_2')), inference(resolution, [status(thm)], [c_6295, c_6463])).
% 7.21/2.52  tff(c_6475, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2554, c_6467])).
% 7.21/2.52  tff(c_6477, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_6263])).
% 7.21/2.52  tff(c_6480, plain, (![E_972, B_974, D_971, A_970, C_973]: (k2_mcart_1(k1_mcart_1(E_972))=k10_mcart_1(A_970, B_974, C_973, D_971, E_972) | ~m1_subset_1(E_972, k4_zfmisc_1(A_970, B_974, C_973, D_971)) | k1_xboole_0=D_971 | k1_xboole_0=C_973 | k1_xboole_0=B_974 | k1_xboole_0=A_970)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_6483, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_6480])).
% 7.21/2.52  tff(c_6486, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6477, c_6483])).
% 7.21/2.52  tff(c_6657, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_6486])).
% 7.21/2.52  tff(c_6576, plain, (![A_990, B_991, B_992]: (r2_hidden('#skF_1'(A_990, B_991), B_992) | ~r1_tarski(A_990, B_992) | r1_tarski(A_990, B_991))), inference(resolution, [status(thm)], [c_6, c_4358])).
% 7.21/2.52  tff(c_6635, plain, (![B_999, A_1000, B_1001]: (~r1_tarski(B_999, '#skF_1'(A_1000, B_1001)) | ~r1_tarski(A_1000, B_999) | r1_tarski(A_1000, B_1001))), inference(resolution, [status(thm)], [c_6576, c_14])).
% 7.21/2.52  tff(c_6645, plain, (![A_1000, B_1001]: (~r1_tarski(A_1000, k1_xboole_0) | r1_tarski(A_1000, B_1001))), inference(resolution, [status(thm)], [c_8, c_6635])).
% 7.21/2.52  tff(c_6724, plain, (![A_1009, B_1010]: (~r1_tarski(A_1009, '#skF_3') | r1_tarski(A_1009, B_1010))), inference(demodulation, [status(thm), theory('equality')], [c_6657, c_6645])).
% 7.21/2.52  tff(c_6737, plain, (![B_1010]: (r1_tarski('#skF_7', B_1010))), inference(resolution, [status(thm)], [c_2553, c_6724])).
% 7.21/2.52  tff(c_6211, plain, (r2_hidden(k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_7')), inference(splitRight, [status(thm)], [c_4345])).
% 7.21/2.52  tff(c_6253, plain, (~r1_tarski('#skF_7', k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'))), inference(resolution, [status(thm)], [c_6211, c_14])).
% 7.21/2.52  tff(c_6743, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6737, c_6253])).
% 7.21/2.52  tff(c_6745, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_6486])).
% 7.21/2.52  tff(c_6605, plain, (![B_997, D_994, C_996, E_995, A_993]: (k9_mcart_1(A_993, B_997, C_996, D_994, E_995)=k2_mcart_1(k1_mcart_1(k1_mcart_1(E_995))) | ~m1_subset_1(E_995, k4_zfmisc_1(A_993, B_997, C_996, D_994)) | k1_xboole_0=D_994 | k1_xboole_0=C_996 | k1_xboole_0=B_997 | k1_xboole_0=A_993)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_6607, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_6605])).
% 7.21/2.52  tff(c_6610, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6477, c_6607])).
% 7.21/2.52  tff(c_6795, plain, (k2_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k9_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_6745, c_6610])).
% 7.21/2.52  tff(c_6796, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_6795])).
% 7.21/2.52  tff(c_6813, plain, (![A_1020]: (r1_tarski('#skF_4', A_1020))), inference(demodulation, [status(thm), theory('equality')], [c_6796, c_8])).
% 7.21/2.52  tff(c_6604, plain, (![B_992, A_990, B_991]: (~r1_tarski(B_992, '#skF_1'(A_990, B_991)) | ~r1_tarski(A_990, B_992) | r1_tarski(A_990, B_991))), inference(resolution, [status(thm)], [c_6576, c_14])).
% 7.21/2.52  tff(c_6879, plain, (![A_1025, B_1026]: (~r1_tarski(A_1025, '#skF_4') | r1_tarski(A_1025, B_1026))), inference(resolution, [status(thm)], [c_6813, c_6604])).
% 7.21/2.52  tff(c_6892, plain, (![B_1026]: (r1_tarski('#skF_8', B_1026))), inference(resolution, [status(thm)], [c_2551, c_6879])).
% 7.21/2.52  tff(c_7040, plain, (![A_1052, C_1053, B_1051, A_1050, D_1054]: (r2_hidden(k1_mcart_1(A_1052), k3_zfmisc_1(A_1050, B_1051, C_1053)) | ~r2_hidden(A_1052, k4_zfmisc_1(A_1050, B_1051, C_1053, D_1054)))), inference(superposition, [status(thm), theory('equality')], [c_4432, c_22])).
% 7.21/2.52  tff(c_7075, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_7040])).
% 7.21/2.52  tff(c_4395, plain, (![A_700, C_13, A_11, B_12]: (r2_hidden(k2_mcart_1(A_700), C_13) | ~r2_hidden(A_700, k3_zfmisc_1(A_11, B_12, C_13)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_4393])).
% 7.21/2.52  tff(c_7086, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_7075, c_4395])).
% 7.21/2.52  tff(c_7093, plain, (~r1_tarski('#skF_8', k2_mcart_1(k1_mcart_1('#skF_10')))), inference(resolution, [status(thm)], [c_7086, c_14])).
% 7.21/2.52  tff(c_7100, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6892, c_7093])).
% 7.21/2.52  tff(c_7102, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_6795])).
% 7.21/2.52  tff(c_6542, plain, (![E_983, B_985, D_982, A_981, C_984]: (k8_mcart_1(A_981, B_985, C_984, D_982, E_983)=k1_mcart_1(k1_mcart_1(k1_mcart_1(E_983))) | ~m1_subset_1(E_983, k4_zfmisc_1(A_981, B_985, C_984, D_982)) | k1_xboole_0=D_982 | k1_xboole_0=C_984 | k1_xboole_0=B_985 | k1_xboole_0=A_981)), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.21/2.52  tff(c_6544, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_36, c_6542])).
% 7.21/2.52  tff(c_6547, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_6477, c_6544])).
% 7.21/2.52  tff(c_7103, plain, (k1_mcart_1(k1_mcart_1(k1_mcart_1('#skF_10')))=k8_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10') | k1_xboole_0='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_6745, c_7102, c_6547])).
% 7.21/2.52  tff(c_7104, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_7103])).
% 7.21/2.52  tff(c_6212, plain, (![B_928]: (r2_hidden(k2_mcart_1('#skF_10'), B_928) | ~r1_tarski('#skF_9', B_928))), inference(resolution, [status(thm)], [c_4483, c_2])).
% 7.21/2.52  tff(c_6264, plain, (![B_937, B_938]: (r2_hidden(k2_mcart_1('#skF_10'), B_937) | ~r1_tarski(B_938, B_937) | ~r1_tarski('#skF_9', B_938))), inference(resolution, [status(thm)], [c_6212, c_2])).
% 7.21/2.52  tff(c_6268, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5') | ~r1_tarski('#skF_9', '#skF_9')), inference(resolution, [status(thm)], [c_2552, c_6264])).
% 7.21/2.52  tff(c_6280, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2569, c_6268])).
% 7.21/2.52  tff(c_6488, plain, (![B_975]: (r2_hidden(k2_mcart_1('#skF_10'), B_975) | ~r1_tarski('#skF_5', B_975))), inference(resolution, [status(thm)], [c_6280, c_2])).
% 7.21/2.52  tff(c_6513, plain, (![B_976]: (~r1_tarski(B_976, k2_mcart_1('#skF_10')) | ~r1_tarski('#skF_5', B_976))), inference(resolution, [status(thm)], [c_6488, c_14])).
% 7.21/2.52  tff(c_6523, plain, (~r1_tarski('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_6513])).
% 7.21/2.52  tff(c_7112, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_7104, c_6523])).
% 7.21/2.52  tff(c_7120, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2569, c_7112])).
% 7.21/2.52  tff(c_7122, plain, (k1_xboole_0!='#skF_5'), inference(splitRight, [status(thm)], [c_7103])).
% 7.21/2.52  tff(c_6744, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_5' | k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(splitRight, [status(thm)], [c_6486])).
% 7.21/2.52  tff(c_7163, plain, (k2_mcart_1(k1_mcart_1('#skF_10'))=k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10')), inference(negUnitSimplification, [status(thm)], [c_7122, c_7102, c_6744])).
% 7.21/2.52  tff(c_7365, plain, (![A_1091, C_1094, A_1093, D_1095, B_1092]: (r2_hidden(k1_mcart_1(A_1093), k3_zfmisc_1(A_1091, B_1092, C_1094)) | ~r2_hidden(A_1093, k4_zfmisc_1(A_1091, B_1092, C_1094, D_1095)))), inference(superposition, [status(thm), theory('equality')], [c_4432, c_22])).
% 7.21/2.52  tff(c_7400, plain, (r2_hidden(k1_mcart_1('#skF_10'), k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_34, c_7365])).
% 7.21/2.52  tff(c_7407, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_10')), '#skF_8')), inference(resolution, [status(thm)], [c_7400, c_4395])).
% 7.21/2.52  tff(c_7415, plain, (r2_hidden(k10_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_5', '#skF_10'), '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_7163, c_7407])).
% 7.21/2.52  tff(c_7417, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6210, c_7415])).
% 7.21/2.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.21/2.52  
% 7.21/2.52  Inference rules
% 7.21/2.52  ----------------------
% 7.21/2.52  #Ref     : 0
% 7.21/2.52  #Sup     : 1666
% 7.21/2.52  #Fact    : 0
% 7.21/2.52  #Define  : 0
% 7.21/2.52  #Split   : 68
% 7.21/2.52  #Chain   : 0
% 7.21/2.52  #Close   : 0
% 7.21/2.52  
% 7.21/2.52  Ordering : KBO
% 7.21/2.52  
% 7.21/2.52  Simplification rules
% 7.21/2.52  ----------------------
% 7.21/2.52  #Subsume      : 263
% 7.21/2.52  #Demod        : 873
% 7.21/2.52  #Tautology    : 335
% 7.21/2.52  #SimpNegUnit  : 32
% 7.21/2.52  #BackRed      : 146
% 7.21/2.52  
% 7.21/2.52  #Partial instantiations: 0
% 7.21/2.52  #Strategies tried      : 1
% 7.21/2.52  
% 7.21/2.52  Timing (in seconds)
% 7.21/2.52  ----------------------
% 7.21/2.53  Preprocessing        : 0.35
% 7.21/2.53  Parsing              : 0.19
% 7.21/2.53  CNF conversion       : 0.03
% 7.21/2.53  Main loop            : 1.35
% 7.21/2.53  Inferencing          : 0.46
% 7.21/2.53  Reduction            : 0.46
% 7.21/2.53  Demodulation         : 0.31
% 7.21/2.53  BG Simplification    : 0.05
% 7.21/2.53  Subsumption          : 0.26
% 7.21/2.53  Abstraction          : 0.06
% 7.21/2.53  MUC search           : 0.00
% 7.21/2.53  Cooper               : 0.00
% 7.21/2.53  Total                : 1.79
% 7.21/2.53  Index Insertion      : 0.00
% 7.21/2.53  Index Deletion       : 0.00
% 7.21/2.53  Index Matching       : 0.00
% 7.21/2.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
