%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:04 EST 2020

% Result     : Theorem 29.89s
% Output     : CNFRefutation 30.12s
% Verified   : 
% Statistics : Number of formulae       :  382 (3443 expanded)
%              Number of leaves         :   39 (1173 expanded)
%              Depth                    :   25
%              Number of atoms          :  702 (9599 expanded)
%              Number of equality atoms :  352 (5008 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_149,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_121,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ! [C] :
              ( m1_subset_1(C,k2_zfmisc_1(A,B))
             => C = k4_tarski(k1_mcart_1(C),k2_mcart_1(C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_mcart_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_125,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_56,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_54,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_60,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_119761,plain,(
    ! [A_42407,B_42408,C_42409,D_42410] :
      ( k7_mcart_1(A_42407,B_42408,C_42409,D_42410) = k2_mcart_1(D_42410)
      | ~ m1_subset_1(D_42410,k3_zfmisc_1(A_42407,B_42408,C_42409))
      | k1_xboole_0 = C_42409
      | k1_xboole_0 = B_42408
      | k1_xboole_0 = A_42407 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_119768,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_119761])).

tff(c_119772,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_119768])).

tff(c_50,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_119823,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119772,c_50])).

tff(c_40,plain,(
    ! [A_42,B_43,D_45] : k4_zfmisc_1(A_42,B_43,k1_xboole_0,D_45) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_44,plain,(
    ! [B_43,C_44,D_45] : k4_zfmisc_1(k1_xboole_0,B_43,C_44,D_45) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_18,plain,(
    ! [A_21,B_22,C_23,D_24] : k2_zfmisc_1(k3_zfmisc_1(A_21,B_22,C_23),D_24) = k4_zfmisc_1(A_21,B_22,C_23,D_24) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_191,plain,(
    ! [A_97,B_98,C_99] : k2_zfmisc_1(k2_zfmisc_1(A_97,B_98),C_99) = k3_zfmisc_1(A_97,B_98,C_99) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    ! [A_18,B_19,C_20] : k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20) = k3_zfmisc_1(A_18,B_19,C_20) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_194,plain,(
    ! [A_97,B_98,C_99,C_20] : k3_zfmisc_1(k2_zfmisc_1(A_97,B_98),C_99,C_20) = k2_zfmisc_1(k3_zfmisc_1(A_97,B_98,C_99),C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_16])).

tff(c_135582,plain,(
    ! [A_97,B_98,C_99,C_20] : k3_zfmisc_1(k2_zfmisc_1(A_97,B_98),C_99,C_20) = k4_zfmisc_1(A_97,B_98,C_99,C_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_194])).

tff(c_364,plain,(
    ! [C_139,A_140,B_141] :
      ( k4_tarski(k1_mcart_1(C_139),k2_mcart_1(C_139)) = C_139
      | ~ m1_subset_1(C_139,k2_zfmisc_1(A_140,B_141))
      | k1_xboole_0 = B_141
      | k1_xboole_0 = A_140 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_137134,plain,(
    ! [C_43275,A_43276,B_43277,C_43278] :
      ( k4_tarski(k1_mcart_1(C_43275),k2_mcart_1(C_43275)) = C_43275
      | ~ m1_subset_1(C_43275,k3_zfmisc_1(A_43276,B_43277,C_43278))
      | k1_xboole_0 = C_43278
      | k2_zfmisc_1(A_43276,B_43277) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_364])).

tff(c_137266,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_137134])).

tff(c_137315,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_137266])).

tff(c_137319,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_137315])).

tff(c_137625,plain,(
    ! [C_43287] : k3_zfmisc_1('#skF_4','#skF_5',C_43287) = k2_zfmisc_1(k1_xboole_0,C_43287) ),
    inference(superposition,[status(thm),theory(equality)],[c_137319,c_16])).

tff(c_247,plain,(
    ! [A_109,B_110,C_111,D_112] : k2_zfmisc_1(k3_zfmisc_1(A_109,B_110,C_111),D_112) = k4_zfmisc_1(A_109,B_110,C_111,D_112) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_255,plain,(
    ! [B_110,A_109,D_112,C_111,C_20] : k3_zfmisc_1(k3_zfmisc_1(A_109,B_110,C_111),D_112,C_20) = k2_zfmisc_1(k4_zfmisc_1(A_109,B_110,C_111,D_112),C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_16])).

tff(c_137633,plain,(
    ! [C_43287,D_112,C_20] : k3_zfmisc_1(k2_zfmisc_1(k1_xboole_0,C_43287),D_112,C_20) = k2_zfmisc_1(k4_zfmisc_1('#skF_4','#skF_5',C_43287,D_112),C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_137625,c_255])).

tff(c_140677,plain,(
    ! [C_43334,D_43335,C_43336] : k2_zfmisc_1(k4_zfmisc_1('#skF_4','#skF_5',C_43334,D_43335),C_43336) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_135582,c_137633])).

tff(c_140742,plain,(
    ! [C_43336] : k2_zfmisc_1(k1_xboole_0,C_43336) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_140677])).

tff(c_137358,plain,(
    ! [C_20] : k3_zfmisc_1('#skF_4','#skF_5',C_20) = k2_zfmisc_1(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_137319,c_16])).

tff(c_140933,plain,(
    ! [C_43341] : k3_zfmisc_1('#skF_4','#skF_5',C_43341) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140742,c_137358])).

tff(c_140980,plain,(
    ! [C_43341,D_24] : k4_zfmisc_1('#skF_4','#skF_5',C_43341,D_24) = k2_zfmisc_1(k1_xboole_0,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_140933,c_18])).

tff(c_141800,plain,(
    ! [C_43351,D_43352] : k4_zfmisc_1('#skF_4','#skF_5',C_43351,D_43352) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140742,c_140980])).

tff(c_36,plain,(
    ! [A_42,B_43,C_44,D_45] :
      ( k4_zfmisc_1(A_42,B_43,C_44,D_45) != k1_xboole_0
      | k1_xboole_0 = D_45
      | k1_xboole_0 = C_44
      | k1_xboole_0 = B_43
      | k1_xboole_0 = A_42 ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_141817,plain,(
    ! [D_43352,C_43351] :
      ( k1_xboole_0 = D_43352
      | k1_xboole_0 = C_43351
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_141800,c_36])).

tff(c_141839,plain,(
    ! [D_43352,C_43351] :
      ( k1_xboole_0 = D_43352
      | k1_xboole_0 = C_43351 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_141817])).

tff(c_141847,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_141839])).

tff(c_141845,plain,(
    ! [C_43351] : k1_xboole_0 = C_43351 ),
    inference(splitLeft,[status(thm)],[c_141839])).

tff(c_144332,plain,(
    ! [C_50428] : C_50428 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_141847,c_141845])).

tff(c_145833,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_144332,c_52])).

tff(c_145836,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_141839])).

tff(c_145834,plain,(
    ! [D_43352] : k1_xboole_0 = D_43352 ),
    inference(splitRight,[status(thm)],[c_141839])).

tff(c_148117,plain,(
    ! [D_64605] : D_64605 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_145836,c_145834])).

tff(c_149616,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_148117,c_52])).

tff(c_149617,plain,(
    k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_137315])).

tff(c_417,plain,(
    ! [A_152,B_153,C_154] :
      ( k4_tarski('#skF_2'(A_152,B_153,C_154),'#skF_3'(A_152,B_153,C_154)) = A_152
      | ~ r2_hidden(A_152,k2_zfmisc_1(B_153,C_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17] : k4_tarski(k4_tarski(A_15,B_16),C_17) = k3_mcart_1(A_15,B_16,C_17) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_136957,plain,(
    ! [A_43263,B_43264,C_43265,C_43266] :
      ( k3_mcart_1('#skF_2'(A_43263,B_43264,C_43265),'#skF_3'(A_43263,B_43264,C_43265),C_43266) = k4_tarski(A_43263,C_43266)
      | ~ r2_hidden(A_43263,k2_zfmisc_1(B_43264,C_43265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_14])).

tff(c_58,plain,(
    ! [H_61,F_55,G_59] :
      ( H_61 = '#skF_7'
      | k3_mcart_1(F_55,G_59,H_61) != '#skF_8'
      | ~ m1_subset_1(H_61,'#skF_6')
      | ~ m1_subset_1(G_59,'#skF_5')
      | ~ m1_subset_1(F_55,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_136980,plain,(
    ! [C_43266,A_43263,B_43264,C_43265] :
      ( C_43266 = '#skF_7'
      | k4_tarski(A_43263,C_43266) != '#skF_8'
      | ~ m1_subset_1(C_43266,'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_43263,B_43264,C_43265),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_43263,B_43264,C_43265),'#skF_4')
      | ~ r2_hidden(A_43263,k2_zfmisc_1(B_43264,C_43265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136957,c_58])).

tff(c_149621,plain,(
    ! [B_43264,C_43265] :
      ( k2_mcart_1('#skF_8') = '#skF_7'
      | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_43264,C_43265),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_43264,C_43265),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_43264,C_43265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_149617,c_136980])).

tff(c_149654,plain,(
    ! [B_43264,C_43265] :
      ( ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_43264,C_43265),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_43264,C_43265),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_43264,C_43265)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119823,c_149621])).

tff(c_149870,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_149654])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_208,plain,(
    ! [A_100,B_101,C_102] :
      ( r2_hidden(k1_mcart_1(A_100),B_101)
      | ~ r2_hidden(A_100,k2_zfmisc_1(B_101,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_312,plain,(
    ! [B_130,C_131] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_130,C_131))),B_130)
      | v1_xboole_0(k2_zfmisc_1(B_130,C_131)) ) ),
    inference(resolution,[status(thm)],[c_4,c_208])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_344,plain,(
    ! [B_132,C_133] :
      ( ~ v1_xboole_0(B_132)
      | v1_xboole_0(k2_zfmisc_1(B_132,C_133)) ) ),
    inference(resolution,[status(thm)],[c_312,c_2])).

tff(c_353,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_18,B_19))
      | v1_xboole_0(k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_344])).

tff(c_12,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | v1_xboole_0(B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_182,plain,(
    ! [A_94,C_95,B_96] :
      ( r2_hidden(k2_mcart_1(A_94),C_95)
      | ~ r2_hidden(A_94,k2_zfmisc_1(B_96,C_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_35205,plain,(
    ! [A_25977,C_25978,B_25979] :
      ( r2_hidden(k2_mcart_1(A_25977),C_25978)
      | v1_xboole_0(k2_zfmisc_1(B_25979,C_25978))
      | ~ m1_subset_1(A_25977,k2_zfmisc_1(B_25979,C_25978)) ) ),
    inference(resolution,[status(thm)],[c_12,c_182])).

tff(c_35223,plain,(
    ! [A_25977,C_20,A_18,B_19] :
      ( r2_hidden(k2_mcart_1(A_25977),C_20)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_18,B_19),C_20))
      | ~ m1_subset_1(A_25977,k3_zfmisc_1(A_18,B_19,C_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_35205])).

tff(c_72094,plain,(
    ! [A_38431,C_38432,A_38433,B_38434] :
      ( r2_hidden(k2_mcart_1(A_38431),C_38432)
      | v1_xboole_0(k3_zfmisc_1(A_38433,B_38434,C_38432))
      | ~ m1_subset_1(A_38431,k3_zfmisc_1(A_38433,B_38434,C_38432)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_35223])).

tff(c_72170,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_6')
    | v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_72094])).

tff(c_72171,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_72170])).

tff(c_36593,plain,(
    ! [A_26032,B_26033,C_26034,D_26035] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_26032,B_26033,C_26034))
      | v1_xboole_0(k4_zfmisc_1(A_26032,B_26033,C_26034,D_26035)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_344])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36660,plain,(
    ! [A_26032,B_26033,C_26034,D_26035] :
      ( k4_zfmisc_1(A_26032,B_26033,C_26034,D_26035) = k1_xboole_0
      | ~ v1_xboole_0(k3_zfmisc_1(A_26032,B_26033,C_26034)) ) ),
    inference(resolution,[status(thm)],[c_36593,c_6])).

tff(c_72379,plain,(
    ! [D_38435] : k4_zfmisc_1('#skF_4','#skF_5','#skF_6',D_38435) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_72171,c_36660])).

tff(c_72510,plain,(
    ! [D_38435] :
      ( k1_xboole_0 = D_38435
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72379,c_36])).

tff(c_72598,plain,(
    ! [D_38436] : k1_xboole_0 = D_38436 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_72510])).

tff(c_539,plain,(
    ! [A_164,B_165,C_166,D_167] :
      ( k7_mcart_1(A_164,B_165,C_166,D_167) = k2_mcart_1(D_167)
      | ~ m1_subset_1(D_167,k3_zfmisc_1(A_164,B_165,C_166))
      | k1_xboole_0 = C_166
      | k1_xboole_0 = B_165
      | k1_xboole_0 = A_164 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_546,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_539])).

tff(c_550,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_546])).

tff(c_551,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_550,c_50])).

tff(c_13443,plain,(
    ! [A_97,B_98,C_99,C_20] : k3_zfmisc_1(k2_zfmisc_1(A_97,B_98),C_99,C_20) = k4_zfmisc_1(A_97,B_98,C_99,C_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_194])).

tff(c_14962,plain,(
    ! [C_963,A_964,B_965,C_966] :
      ( k4_tarski(k1_mcart_1(C_963),k2_mcart_1(C_963)) = C_963
      | ~ m1_subset_1(C_963,k3_zfmisc_1(A_964,B_965,C_966))
      | k1_xboole_0 = C_966
      | k2_zfmisc_1(A_964,B_965) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_364])).

tff(c_15067,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_14962])).

tff(c_15107,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_15067])).

tff(c_15114,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_15107])).

tff(c_15184,plain,(
    ! [C_971] : k3_zfmisc_1('#skF_4','#skF_5',C_971) = k2_zfmisc_1(k1_xboole_0,C_971) ),
    inference(superposition,[status(thm),theory(equality)],[c_15114,c_16])).

tff(c_15192,plain,(
    ! [C_971,D_112,C_20] : k3_zfmisc_1(k2_zfmisc_1(k1_xboole_0,C_971),D_112,C_20) = k2_zfmisc_1(k4_zfmisc_1('#skF_4','#skF_5',C_971,D_112),C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_15184,c_255])).

tff(c_17188,plain,(
    ! [C_1017,D_1018,C_1019] : k2_zfmisc_1(k4_zfmisc_1('#skF_4','#skF_5',C_1017,D_1018),C_1019) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_13443,c_15192])).

tff(c_17235,plain,(
    ! [C_1019] : k2_zfmisc_1(k1_xboole_0,C_1019) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_17188])).

tff(c_15153,plain,(
    ! [C_20] : k3_zfmisc_1('#skF_4','#skF_5',C_20) = k2_zfmisc_1(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_15114,c_16])).

tff(c_17378,plain,(
    ! [C_1023] : k3_zfmisc_1('#skF_4','#skF_5',C_1023) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17235,c_15153])).

tff(c_17421,plain,(
    ! [C_1023,D_24] : k4_zfmisc_1('#skF_4','#skF_5',C_1023,D_24) = k2_zfmisc_1(k1_xboole_0,D_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_17378,c_18])).

tff(c_17763,plain,(
    ! [C_1031,D_1032] : k4_zfmisc_1('#skF_4','#skF_5',C_1031,D_1032) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_17235,c_17421])).

tff(c_17780,plain,(
    ! [D_1032,C_1031] :
      ( k1_xboole_0 = D_1032
      | k1_xboole_0 = C_1031
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_17763,c_36])).

tff(c_17802,plain,(
    ! [D_1032,C_1031] :
      ( k1_xboole_0 = D_1032
      | k1_xboole_0 = C_1031 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_17780])).

tff(c_17810,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_17802])).

tff(c_17808,plain,(
    ! [C_1031] : k1_xboole_0 = C_1031 ),
    inference(splitLeft,[status(thm)],[c_17802])).

tff(c_19258,plain,(
    ! [C_7103] : C_7103 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_17810,c_17808])).

tff(c_20335,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_19258,c_54])).

tff(c_20338,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_17802])).

tff(c_20336,plain,(
    ! [D_1032] : k1_xboole_0 = D_1032 ),
    inference(splitRight,[status(thm)],[c_17802])).

tff(c_21839,plain,(
    ! [D_19253] : D_19253 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_20338,c_20336])).

tff(c_22905,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_21839,c_52])).

tff(c_22906,plain,(
    k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_15107])).

tff(c_22951,plain,(
    ! [A_25379,B_25380,C_25381,C_25382] :
      ( k3_mcart_1('#skF_2'(A_25379,B_25380,C_25381),'#skF_3'(A_25379,B_25380,C_25381),C_25382) = k4_tarski(A_25379,C_25382)
      | ~ r2_hidden(A_25379,k2_zfmisc_1(B_25380,C_25381)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_14])).

tff(c_23025,plain,(
    ! [C_25384,A_25385,B_25386,C_25387] :
      ( C_25384 = '#skF_7'
      | k4_tarski(A_25385,C_25384) != '#skF_8'
      | ~ m1_subset_1(C_25384,'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_25385,B_25386,C_25387),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_25385,B_25386,C_25387),'#skF_4')
      | ~ r2_hidden(A_25385,k2_zfmisc_1(B_25386,C_25387)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22951,c_58])).

tff(c_23027,plain,(
    ! [B_25386,C_25387] :
      ( k2_mcart_1('#skF_8') = '#skF_7'
      | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_25386,C_25387),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_25386,C_25387),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_25386,C_25387)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22906,c_23025])).

tff(c_23034,plain,(
    ! [B_25386,C_25387] :
      ( ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_25386,C_25387),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_25386,C_25387),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_25386,C_25387)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_23027])).

tff(c_23266,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_23034])).

tff(c_341,plain,(
    ! [B_130,C_131] :
      ( ~ v1_xboole_0(B_130)
      | v1_xboole_0(k2_zfmisc_1(B_130,C_131)) ) ),
    inference(resolution,[status(thm)],[c_312,c_2])).

tff(c_355,plain,(
    ! [B_134,C_135] :
      ( k2_zfmisc_1(B_134,C_135) = k1_xboole_0
      | ~ v1_xboole_0(B_134) ) ),
    inference(resolution,[status(thm)],[c_344,c_6])).

tff(c_357,plain,(
    ! [B_130,C_131,C_135] :
      ( k2_zfmisc_1(k2_zfmisc_1(B_130,C_131),C_135) = k1_xboole_0
      | ~ v1_xboole_0(B_130) ) ),
    inference(resolution,[status(thm)],[c_341,c_355])).

tff(c_360,plain,(
    ! [B_136,C_137,C_138] :
      ( k3_zfmisc_1(B_136,C_137,C_138) = k1_xboole_0
      | ~ v1_xboole_0(B_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_357])).

tff(c_393,plain,(
    ! [B_148,C_149,C_150,C_151] :
      ( k3_zfmisc_1(k2_zfmisc_1(B_148,C_149),C_150,C_151) = k1_xboole_0
      | ~ v1_xboole_0(B_148) ) ),
    inference(resolution,[status(thm)],[c_341,c_360])).

tff(c_20,plain,(
    ! [A_25,C_27,B_26] :
      ( r2_hidden(k2_mcart_1(A_25),C_27)
      | ~ r2_hidden(A_25,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_199,plain,(
    ! [A_25,C_99,A_97,B_98] :
      ( r2_hidden(k2_mcart_1(A_25),C_99)
      | ~ r2_hidden(A_25,k3_zfmisc_1(A_97,B_98,C_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_20])).

tff(c_401,plain,(
    ! [A_25,C_151,B_148] :
      ( r2_hidden(k2_mcart_1(A_25),C_151)
      | ~ r2_hidden(A_25,k1_xboole_0)
      | ~ v1_xboole_0(B_148) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_199])).

tff(c_441,plain,(
    ! [B_148] : ~ v1_xboole_0(B_148) ),
    inference(splitLeft,[status(thm)],[c_401])).

tff(c_472,plain,(
    ! [A_158,B_159] :
      ( r2_hidden(A_158,B_159)
      | ~ m1_subset_1(A_158,B_159) ) ),
    inference(negUnitSimplification,[status(thm)],[c_441,c_12])).

tff(c_24376,plain,(
    ! [A_25474,C_25475,A_25476,B_25477] :
      ( r2_hidden(k2_mcart_1(A_25474),C_25475)
      | ~ m1_subset_1(A_25474,k3_zfmisc_1(A_25476,B_25477,C_25475)) ) ),
    inference(resolution,[status(thm)],[c_472,c_199])).

tff(c_24557,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_24376])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,B_12)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_24560,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_24557,c_10])).

tff(c_24564,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_23266,c_24560])).

tff(c_24566,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_23034])).

tff(c_650,plain,(
    ! [A_182,B_183,C_184,D_185] :
      ( k5_mcart_1(A_182,B_183,C_184,D_185) = k1_mcart_1(k1_mcart_1(D_185))
      | ~ m1_subset_1(D_185,k3_zfmisc_1(A_182,B_183,C_184))
      | k1_xboole_0 = C_184
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_182 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_669,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_650])).

tff(c_677,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_669])).

tff(c_22,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden(k1_mcart_1(A_25),B_26)
      | ~ r2_hidden(A_25,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_706,plain,(
    ! [A_189,B_190,C_191] :
      ( r2_hidden(k1_mcart_1(A_189),B_190)
      | ~ m1_subset_1(A_189,k2_zfmisc_1(B_190,C_191)) ) ),
    inference(resolution,[status(thm)],[c_472,c_22])).

tff(c_31457,plain,(
    ! [A_25796,A_25797,B_25798,C_25799] :
      ( r2_hidden(k1_mcart_1(A_25796),k2_zfmisc_1(A_25797,B_25798))
      | ~ m1_subset_1(A_25796,k3_zfmisc_1(A_25797,B_25798,C_25799)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_706])).

tff(c_31753,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_31457])).

tff(c_31770,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_31753,c_22])).

tff(c_31784,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_31770])).

tff(c_31952,plain,(
    m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_31784,c_10])).

tff(c_607,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( k6_mcart_1(A_175,B_176,C_177,D_178) = k2_mcart_1(k1_mcart_1(D_178))
      | ~ m1_subset_1(D_178,k3_zfmisc_1(A_175,B_176,C_177))
      | k1_xboole_0 = C_177
      | k1_xboole_0 = B_176
      | k1_xboole_0 = A_175 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_622,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_607])).

tff(c_629,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_622])).

tff(c_1848,plain,(
    ! [D_238,B_239,A_237,C_240,A_236] :
      ( r2_hidden(k2_mcart_1(A_236),D_238)
      | ~ r2_hidden(A_236,k4_zfmisc_1(A_237,B_239,C_240,D_238)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_247,c_20])).

tff(c_1949,plain,(
    ! [A_241,D_242] :
      ( r2_hidden(k2_mcart_1(A_241),D_242)
      | ~ r2_hidden(A_241,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1848])).

tff(c_1983,plain,(
    ! [D_242] :
      ( r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),D_242)
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_1949])).

tff(c_1999,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1983])).

tff(c_3889,plain,(
    ! [C_380,A_381,B_382,C_383] :
      ( k4_tarski(k1_mcart_1(C_380),k2_mcart_1(C_380)) = C_380
      | ~ m1_subset_1(C_380,k3_zfmisc_1(A_381,B_382,C_383))
      | k1_xboole_0 = C_383
      | k2_zfmisc_1(A_381,B_382) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_364])).

tff(c_3982,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_3889])).

tff(c_4018,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_3982])).

tff(c_4022,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_4018])).

tff(c_4061,plain,(
    ! [C_20] : k3_zfmisc_1('#skF_4','#skF_5',C_20) = k2_zfmisc_1(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_4022,c_16])).

tff(c_4089,plain,(
    m1_subset_1('#skF_8',k2_zfmisc_1(k1_xboole_0,'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4061,c_60])).

tff(c_486,plain,(
    ! [A_158,B_26,C_27] :
      ( r2_hidden(k1_mcart_1(A_158),B_26)
      | ~ m1_subset_1(A_158,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(resolution,[status(thm)],[c_472,c_22])).

tff(c_4184,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4089,c_486])).

tff(c_4192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1999,c_4184])).

tff(c_4193,plain,(
    k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4018])).

tff(c_4244,plain,(
    ! [A_390,B_391,C_392,C_393] :
      ( k3_mcart_1('#skF_2'(A_390,B_391,C_392),'#skF_3'(A_390,B_391,C_392),C_393) = k4_tarski(A_390,C_393)
      | ~ r2_hidden(A_390,k2_zfmisc_1(B_391,C_392)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_14])).

tff(c_4280,plain,(
    ! [C_394,A_395,B_396,C_397] :
      ( C_394 = '#skF_7'
      | k4_tarski(A_395,C_394) != '#skF_8'
      | ~ m1_subset_1(C_394,'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_395,B_396,C_397),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_395,B_396,C_397),'#skF_4')
      | ~ r2_hidden(A_395,k2_zfmisc_1(B_396,C_397)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4244,c_58])).

tff(c_4282,plain,(
    ! [B_396,C_397] :
      ( k2_mcart_1('#skF_8') = '#skF_7'
      | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_396,C_397),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_396,C_397),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_396,C_397)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4193,c_4280])).

tff(c_4289,plain,(
    ! [B_396,C_397] :
      ( ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_396,C_397),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_396,C_397),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_396,C_397)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_4282])).

tff(c_4604,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_4289])).

tff(c_5611,plain,(
    ! [A_530,C_531,A_532,B_533] :
      ( r2_hidden(k2_mcart_1(A_530),C_531)
      | ~ m1_subset_1(A_530,k3_zfmisc_1(A_532,B_533,C_531)) ) ),
    inference(resolution,[status(thm)],[c_472,c_199])).

tff(c_5764,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_5611])).

tff(c_5767,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_5764,c_10])).

tff(c_5771,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4604,c_5767])).

tff(c_5773,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_4289])).

tff(c_12070,plain,(
    ! [A_814,A_815,B_816,C_817] :
      ( r2_hidden(k1_mcart_1(A_814),k2_zfmisc_1(A_815,B_816))
      | ~ m1_subset_1(A_814,k3_zfmisc_1(A_815,B_816,C_817)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_706])).

tff(c_12365,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_12070])).

tff(c_12382,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12365,c_22])).

tff(c_12396,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_677,c_12382])).

tff(c_12498,plain,(
    m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_12396,c_10])).

tff(c_12384,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_12365,c_20])).

tff(c_12398,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_12384])).

tff(c_12494,plain,(
    m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_12398,c_10])).

tff(c_12399,plain,(
    m1_subset_1(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_12365,c_10])).

tff(c_28,plain,(
    ! [C_36,A_33,B_34] :
      ( k4_tarski(k1_mcart_1(C_36),k2_mcart_1(C_36)) = C_36
      | ~ m1_subset_1(C_36,k2_zfmisc_1(A_33,B_34))
      | k1_xboole_0 = B_34
      | k1_xboole_0 = A_33 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_12417,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')),k2_mcart_1(k1_mcart_1('#skF_8'))) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_12399,c_28])).

tff(c_12429,plain,
    ( k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_677,c_12417])).

tff(c_12430,plain,(
    k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_12429])).

tff(c_12863,plain,(
    ! [C_833] : k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),C_833) = k4_tarski(k1_mcart_1('#skF_8'),C_833) ),
    inference(superposition,[status(thm),theory(equality)],[c_12430,c_14])).

tff(c_12904,plain,(
    ! [C_833] :
      ( C_833 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_833) != '#skF_8'
      | ~ m1_subset_1(C_833,'#skF_6')
      | ~ m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
      | ~ m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12863,c_58])).

tff(c_13130,plain,(
    ! [C_837] :
      ( C_837 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_837) != '#skF_8'
      | ~ m1_subset_1(C_837,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12498,c_12494,c_12904])).

tff(c_13133,plain,
    ( k2_mcart_1('#skF_8') = '#skF_7'
    | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_4193,c_13130])).

tff(c_13136,plain,(
    k2_mcart_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5773,c_13133])).

tff(c_13138,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_13136])).

tff(c_13140,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1983])).

tff(c_13145,plain,(
    ! [A_838,D_839] :
      ( m1_subset_1(k2_mcart_1(A_838),D_839)
      | ~ r2_hidden(A_838,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1949,c_10])).

tff(c_13169,plain,(
    ! [D_839] :
      ( m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),D_839)
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_629,c_13145])).

tff(c_13183,plain,(
    ! [D_839] : m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),D_839) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13140,c_13169])).

tff(c_31787,plain,(
    m1_subset_1(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_31753,c_10])).

tff(c_31805,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')),k2_mcart_1(k1_mcart_1('#skF_8'))) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_31787,c_28])).

tff(c_31817,plain,
    ( k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_677,c_31805])).

tff(c_31818,plain,(
    k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_31817])).

tff(c_32176,plain,(
    ! [C_25806] : k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),C_25806) = k4_tarski(k1_mcart_1('#skF_8'),C_25806) ),
    inference(superposition,[status(thm),theory(equality)],[c_31818,c_14])).

tff(c_32224,plain,(
    ! [C_25806] :
      ( C_25806 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_25806) != '#skF_8'
      | ~ m1_subset_1(C_25806,'#skF_6')
      | ~ m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
      | ~ m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32176,c_58])).

tff(c_32619,plain,(
    ! [C_25816] :
      ( C_25816 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_25816) != '#skF_8'
      | ~ m1_subset_1(C_25816,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31952,c_13183,c_32224])).

tff(c_32622,plain,
    ( k2_mcart_1('#skF_8') = '#skF_7'
    | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_22906,c_32619])).

tff(c_32625,plain,(
    k2_mcart_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24566,c_32622])).

tff(c_32627,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_551,c_32625])).

tff(c_32629,plain,(
    ! [A_25817,C_25818] :
      ( r2_hidden(k2_mcart_1(A_25817),C_25818)
      | ~ r2_hidden(A_25817,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_32655,plain,(
    ! [C_25818,A_25817] :
      ( ~ v1_xboole_0(C_25818)
      | ~ r2_hidden(A_25817,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_32629,c_2])).

tff(c_32657,plain,(
    ! [A_25819] : ~ r2_hidden(A_25819,k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_32655])).

tff(c_32672,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4,c_32657])).

tff(c_37784,plain,(
    ! [C_26071,A_26072,B_26073,C_26074] :
      ( k4_tarski(k1_mcart_1(C_26071),k2_mcart_1(C_26071)) = C_26071
      | ~ m1_subset_1(C_26071,k3_zfmisc_1(A_26072,B_26073,C_26074))
      | k1_xboole_0 = C_26074
      | k2_zfmisc_1(A_26072,B_26073) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_364])).

tff(c_37821,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_37784])).

tff(c_37833,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_37821])).

tff(c_37834,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_37833])).

tff(c_373,plain,(
    ! [A_142,B_143,C_144] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_142,B_143))
      | v1_xboole_0(k3_zfmisc_1(A_142,B_143,C_144)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_344])).

tff(c_354,plain,(
    ! [B_132,C_133] :
      ( k2_zfmisc_1(B_132,C_133) = k1_xboole_0
      | ~ v1_xboole_0(B_132) ) ),
    inference(resolution,[status(thm)],[c_344,c_6])).

tff(c_377,plain,(
    ! [A_142,B_143,C_144,C_133] :
      ( k2_zfmisc_1(k3_zfmisc_1(A_142,B_143,C_144),C_133) = k1_xboole_0
      | ~ v1_xboole_0(k2_zfmisc_1(A_142,B_143)) ) ),
    inference(resolution,[status(thm)],[c_373,c_354])).

tff(c_383,plain,(
    ! [A_142,B_143,C_144,C_133] :
      ( k4_zfmisc_1(A_142,B_143,C_144,C_133) = k1_xboole_0
      | ~ v1_xboole_0(k2_zfmisc_1(A_142,B_143)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_377])).

tff(c_37906,plain,(
    ! [C_144,C_133] :
      ( k4_zfmisc_1('#skF_4','#skF_5',C_144,C_133) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_37834,c_383])).

tff(c_38087,plain,(
    ! [C_26076,C_26077] : k4_zfmisc_1('#skF_4','#skF_5',C_26076,C_26077) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32672,c_37906])).

tff(c_38126,plain,(
    ! [C_26077,C_26076] :
      ( k1_xboole_0 = C_26077
      | k1_xboole_0 = C_26076
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38087,c_36])).

tff(c_38169,plain,(
    ! [C_26077,C_26076] :
      ( k1_xboole_0 = C_26077
      | k1_xboole_0 = C_26076 ) ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_38126])).

tff(c_38181,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_38169])).

tff(c_38179,plain,(
    ! [C_26076] : k1_xboole_0 = C_26076 ),
    inference(splitLeft,[status(thm)],[c_38169])).

tff(c_38395,plain,(
    ! [C_28109] : C_28109 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_38181,c_38179])).

tff(c_38588,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_38395,c_54])).

tff(c_38637,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38169])).

tff(c_38589,plain,(
    ! [C_26077] : k1_xboole_0 = C_26077 ),
    inference(splitRight,[status(thm)],[c_38169])).

tff(c_38851,plain,(
    ! [C_32246] : C_32246 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_38637,c_38589])).

tff(c_39025,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_38851,c_56])).

tff(c_39027,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_37833])).

tff(c_72981,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_72598,c_39027])).

tff(c_72983,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_72170])).

tff(c_73008,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_353,c_72983])).

tff(c_33507,plain,(
    ! [A_25897,A_25898,B_25899,C_25900] :
      ( r2_hidden(k1_mcart_1(A_25897),k2_zfmisc_1(A_25898,B_25899))
      | ~ r2_hidden(A_25897,k3_zfmisc_1(A_25898,B_25899,C_25900)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_208])).

tff(c_119281,plain,(
    ! [A_42398,A_42399,B_42400,C_42401] :
      ( r2_hidden(k1_mcart_1(A_42398),k2_zfmisc_1(A_42399,B_42400))
      | v1_xboole_0(k3_zfmisc_1(A_42399,B_42400,C_42401))
      | ~ m1_subset_1(A_42398,k3_zfmisc_1(A_42399,B_42400,C_42401)) ) ),
    inference(resolution,[status(thm)],[c_12,c_33507])).

tff(c_119374,plain,
    ( r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5'))
    | v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_119281])).

tff(c_119388,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_72983,c_119374])).

tff(c_119425,plain,(
    m1_subset_1(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_119388,c_10])).

tff(c_32785,plain,(
    ! [A_25828,B_25829,C_25830,D_25831] :
      ( k5_mcart_1(A_25828,B_25829,C_25830,D_25831) = k1_mcart_1(k1_mcart_1(D_25831))
      | ~ m1_subset_1(D_25831,k3_zfmisc_1(A_25828,B_25829,C_25830))
      | k1_xboole_0 = C_25830
      | k1_xboole_0 = B_25829
      | k1_xboole_0 = A_25828 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32798,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_32785])).

tff(c_32803,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_32798])).

tff(c_119405,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_119388,c_22])).

tff(c_119422,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32803,c_119405])).

tff(c_119510,plain,(
    m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_119422,c_10])).

tff(c_32811,plain,(
    ! [A_25832,B_25833,C_25834,D_25835] :
      ( k6_mcart_1(A_25832,B_25833,C_25834,D_25835) = k2_mcart_1(k1_mcart_1(D_25835))
      | ~ m1_subset_1(D_25835,k3_zfmisc_1(A_25832,B_25833,C_25834))
      | k1_xboole_0 = C_25834
      | k1_xboole_0 = B_25833
      | k1_xboole_0 = A_25832 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32824,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_32811])).

tff(c_32829,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_32824])).

tff(c_119407,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_119388,c_20])).

tff(c_119424,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32829,c_119407])).

tff(c_119502,plain,(
    m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_119424,c_10])).

tff(c_48,plain,(
    ! [A_46,B_47] : k2_mcart_1(k4_tarski(A_46,B_47)) = B_47 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_429,plain,(
    ! [A_152,B_153,C_154] :
      ( k2_mcart_1(A_152) = '#skF_3'(A_152,B_153,C_154)
      | ~ r2_hidden(A_152,k2_zfmisc_1(B_153,C_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_48])).

tff(c_119394,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = '#skF_3'(k1_mcart_1('#skF_8'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_119388,c_429])).

tff(c_119416,plain,(
    '#skF_3'(k1_mcart_1('#skF_8'),'#skF_4','#skF_5') = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32829,c_119394])).

tff(c_46,plain,(
    ! [A_46,B_47] : k1_mcart_1(k4_tarski(A_46,B_47)) = A_46 ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_426,plain,(
    ! [A_152,B_153,C_154] :
      ( k1_mcart_1(A_152) = '#skF_2'(A_152,B_153,C_154)
      | ~ r2_hidden(A_152,k2_zfmisc_1(B_153,C_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_46])).

tff(c_119397,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = '#skF_2'(k1_mcart_1('#skF_8'),'#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_119388,c_426])).

tff(c_119418,plain,(
    '#skF_2'(k1_mcart_1('#skF_8'),'#skF_4','#skF_5') = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32803,c_119397])).

tff(c_32698,plain,(
    ! [A_25821,B_25822,C_25823,D_25824] :
      ( k7_mcart_1(A_25821,B_25822,C_25823,D_25824) = k2_mcart_1(D_25824)
      | ~ m1_subset_1(D_25824,k3_zfmisc_1(A_25821,B_25822,C_25823))
      | k1_xboole_0 = C_25823
      | k1_xboole_0 = B_25822
      | k1_xboole_0 = A_25821 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_32708,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_32698])).

tff(c_32712,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_32708])).

tff(c_32755,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32712,c_50])).

tff(c_39026,plain,(
    k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_37833])).

tff(c_36676,plain,(
    ! [A_26036,B_26037,C_26038,C_26039] :
      ( k3_mcart_1('#skF_2'(A_26036,B_26037,C_26038),'#skF_3'(A_26036,B_26037,C_26038),C_26039) = k4_tarski(A_26036,C_26039)
      | ~ r2_hidden(A_26036,k2_zfmisc_1(B_26037,C_26038)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_14])).

tff(c_36695,plain,(
    ! [C_26039,A_26036,B_26037,C_26038] :
      ( C_26039 = '#skF_7'
      | k4_tarski(A_26036,C_26039) != '#skF_8'
      | ~ m1_subset_1(C_26039,'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_26036,B_26037,C_26038),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_26036,B_26037,C_26038),'#skF_4')
      | ~ r2_hidden(A_26036,k2_zfmisc_1(B_26037,C_26038)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36676,c_58])).

tff(c_39030,plain,(
    ! [B_26037,C_26038] :
      ( k2_mcart_1('#skF_8') = '#skF_7'
      | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_26037,C_26038),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_26037,C_26038),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_26037,C_26038)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_39026,c_36695])).

tff(c_39053,plain,(
    ! [B_26037,C_26038] :
      ( ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_26037,C_26038),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_26037,C_26038),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_26037,C_26038)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32755,c_39030])).

tff(c_39622,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_39053])).

tff(c_303,plain,(
    ! [A_126,C_127,A_128,B_129] :
      ( r2_hidden(k2_mcart_1(A_126),C_127)
      | ~ r2_hidden(A_126,k3_zfmisc_1(A_128,B_129,C_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_20])).

tff(c_55506,plain,(
    ! [A_34758,C_34759,A_34760,B_34761] :
      ( r2_hidden(k2_mcart_1(A_34758),C_34759)
      | v1_xboole_0(k3_zfmisc_1(A_34760,B_34761,C_34759))
      | ~ m1_subset_1(A_34758,k3_zfmisc_1(A_34760,B_34761,C_34759)) ) ),
    inference(resolution,[status(thm)],[c_12,c_303])).

tff(c_55582,plain,
    ( r2_hidden(k2_mcart_1('#skF_8'),'#skF_6')
    | v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_60,c_55506])).

tff(c_55583,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_55582])).

tff(c_55795,plain,(
    ! [D_34762] : k4_zfmisc_1('#skF_4','#skF_5','#skF_6',D_34762) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_55583,c_36660])).

tff(c_55923,plain,(
    ! [D_34762] :
      ( k1_xboole_0 = D_34762
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_55795,c_36])).

tff(c_56010,plain,(
    ! [D_34763] : k1_xboole_0 = D_34763 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_55923])).

tff(c_56367,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_56010,c_39027])).

tff(c_56368,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_55582])).

tff(c_56372,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_56368,c_10])).

tff(c_56379,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_39622,c_56372])).

tff(c_58686,plain,(
    ! [B_38129,C_38130] :
      ( ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_38129,C_38130),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_38129,C_38130),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_38129,C_38130)) ) ),
    inference(splitRight,[status(thm)],[c_39053])).

tff(c_58729,plain,(
    ! [B_38129,C_38130] :
      ( ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_38129,C_38130),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_38129,C_38130),'#skF_4')
      | v1_xboole_0(k2_zfmisc_1(B_38129,C_38130))
      | ~ m1_subset_1(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_38129,C_38130)) ) ),
    inference(resolution,[status(thm)],[c_12,c_58686])).

tff(c_119635,plain,
    ( ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),'#skF_4','#skF_5'),'#skF_5')
    | ~ m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4')
    | v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5'))
    | ~ m1_subset_1(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_119418,c_58729])).

tff(c_119710,plain,(
    v1_xboole_0(k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_119425,c_119510,c_119502,c_119416,c_119635])).

tff(c_119712,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_73008,c_119710])).

tff(c_119713,plain,(
    ! [C_25818] : ~ v1_xboole_0(C_25818) ),
    inference(splitRight,[status(thm)],[c_32655])).

tff(c_119744,plain,(
    ! [A_42405,B_42406] :
      ( r2_hidden(A_42405,B_42406)
      | ~ m1_subset_1(A_42405,B_42406) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119713,c_12])).

tff(c_133124,plain,(
    ! [A_43080,C_43081,B_43082] :
      ( r2_hidden(k2_mcart_1(A_43080),C_43081)
      | ~ m1_subset_1(A_43080,k2_zfmisc_1(B_43082,C_43081)) ) ),
    inference(resolution,[status(thm)],[c_119744,c_20])).

tff(c_150294,plain,(
    ! [A_71741,C_71742,A_71743,B_71744] :
      ( r2_hidden(k2_mcart_1(A_71741),C_71742)
      | ~ m1_subset_1(A_71741,k3_zfmisc_1(A_71743,B_71744,C_71742)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_133124])).

tff(c_150502,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_150294])).

tff(c_150505,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_150502,c_10])).

tff(c_150509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_149870,c_150505])).

tff(c_150511,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_149654])).

tff(c_119828,plain,(
    ! [A_42415,B_42416,C_42417,D_42418] :
      ( k5_mcart_1(A_42415,B_42416,C_42417,D_42418) = k1_mcart_1(k1_mcart_1(D_42418))
      | ~ m1_subset_1(D_42418,k3_zfmisc_1(A_42415,B_42416,C_42417))
      | k1_xboole_0 = C_42417
      | k1_xboole_0 = B_42416
      | k1_xboole_0 = A_42415 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_119835,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_119828])).

tff(c_119839,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_119835])).

tff(c_119717,plain,(
    ! [A_13,B_14] :
      ( r2_hidden(A_13,B_14)
      | ~ m1_subset_1(A_13,B_14) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119713,c_12])).

tff(c_134933,plain,(
    ! [A_43166,A_43167,B_43168,C_43169] :
      ( r2_hidden(k1_mcart_1(A_43166),k2_zfmisc_1(A_43167,B_43168))
      | ~ r2_hidden(A_43166,k3_zfmisc_1(A_43167,B_43168,C_43169)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_208])).

tff(c_157186,plain,(
    ! [A_72025,A_72026,B_72027,C_72028] :
      ( r2_hidden(k1_mcart_1(A_72025),k2_zfmisc_1(A_72026,B_72027))
      | ~ m1_subset_1(A_72025,k3_zfmisc_1(A_72026,B_72027,C_72028)) ) ),
    inference(resolution,[status(thm)],[c_119717,c_134933])).

tff(c_157512,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_157186])).

tff(c_157529,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_157512,c_22])).

tff(c_157543,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119839,c_157529])).

tff(c_157703,plain,(
    m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_157543,c_10])).

tff(c_119967,plain,(
    ! [A_42433,B_42434,C_42435,D_42436] :
      ( k6_mcart_1(A_42433,B_42434,C_42435,D_42436) = k2_mcart_1(k1_mcart_1(D_42436))
      | ~ m1_subset_1(D_42436,k3_zfmisc_1(A_42433,B_42434,C_42435))
      | k1_xboole_0 = C_42435
      | k1_xboole_0 = B_42434
      | k1_xboole_0 = A_42433 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_119990,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_60,c_119967])).

tff(c_119999,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_52,c_119990])).

tff(c_32628,plain,(
    ! [A_25,C_151] :
      ( r2_hidden(k2_mcart_1(A_25),C_151)
      | ~ r2_hidden(A_25,k1_xboole_0) ) ),
    inference(splitRight,[status(thm)],[c_401])).

tff(c_120009,plain,(
    ! [C_151] :
      ( r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),C_151)
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_119999,c_32628])).

tff(c_120048,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_120009])).

tff(c_123606,plain,(
    ! [C_42614,A_42615,B_42616,C_42617] :
      ( k4_tarski(k1_mcart_1(C_42614),k2_mcart_1(C_42614)) = C_42614
      | ~ m1_subset_1(C_42614,k3_zfmisc_1(A_42615,B_42616,C_42617))
      | k1_xboole_0 = C_42617
      | k2_zfmisc_1(A_42615,B_42616) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_364])).

tff(c_123729,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_123606])).

tff(c_123775,plain,
    ( k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_123729])).

tff(c_123810,plain,(
    k2_zfmisc_1('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_123775])).

tff(c_123849,plain,(
    ! [C_20] : k3_zfmisc_1('#skF_4','#skF_5',C_20) = k2_zfmisc_1(k1_xboole_0,C_20) ),
    inference(superposition,[status(thm),theory(equality)],[c_123810,c_16])).

tff(c_123939,plain,(
    m1_subset_1('#skF_8',k2_zfmisc_1(k1_xboole_0,'#skF_6')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_123849,c_60])).

tff(c_119758,plain,(
    ! [A_42405,B_26,C_27] :
      ( r2_hidden(k1_mcart_1(A_42405),B_26)
      | ~ m1_subset_1(A_42405,k2_zfmisc_1(B_26,C_27)) ) ),
    inference(resolution,[status(thm)],[c_119744,c_22])).

tff(c_123998,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_123939,c_119758])).

tff(c_124006,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_120048,c_123998])).

tff(c_124007,plain,(
    k4_tarski(k1_mcart_1('#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_123775])).

tff(c_124046,plain,(
    ! [A_42627,B_42628,C_42629,C_42630] :
      ( k3_mcart_1('#skF_2'(A_42627,B_42628,C_42629),'#skF_3'(A_42627,B_42628,C_42629),C_42630) = k4_tarski(A_42627,C_42630)
      | ~ r2_hidden(A_42627,k2_zfmisc_1(B_42628,C_42629)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_14])).

tff(c_124116,plain,(
    ! [C_42632,A_42633,B_42634,C_42635] :
      ( C_42632 = '#skF_7'
      | k4_tarski(A_42633,C_42632) != '#skF_8'
      | ~ m1_subset_1(C_42632,'#skF_6')
      | ~ m1_subset_1('#skF_3'(A_42633,B_42634,C_42635),'#skF_5')
      | ~ m1_subset_1('#skF_2'(A_42633,B_42634,C_42635),'#skF_4')
      | ~ r2_hidden(A_42633,k2_zfmisc_1(B_42634,C_42635)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124046,c_58])).

tff(c_124118,plain,(
    ! [B_42634,C_42635] :
      ( k2_mcart_1('#skF_8') = '#skF_7'
      | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_42634,C_42635),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_42634,C_42635),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_42634,C_42635)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124007,c_124116])).

tff(c_124125,plain,(
    ! [B_42634,C_42635] :
      ( ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6')
      | ~ m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'),B_42634,C_42635),'#skF_5')
      | ~ m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'),B_42634,C_42635),'#skF_4')
      | ~ r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1(B_42634,C_42635)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_119823,c_124118])).

tff(c_124345,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_124125])).

tff(c_124361,plain,(
    ! [A_42649,C_42650,A_42651,B_42652] :
      ( r2_hidden(k2_mcart_1(A_42649),C_42650)
      | ~ m1_subset_1(A_42649,k3_zfmisc_1(A_42651,B_42652,C_42650)) ) ),
    inference(resolution,[status(thm)],[c_119744,c_199])).

tff(c_124550,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_60,c_124361])).

tff(c_124553,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_124550,c_10])).

tff(c_124557,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124345,c_124553])).

tff(c_124559,plain,(
    m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_124125])).

tff(c_120165,plain,(
    ! [A_42458,B_42459,C_42460] :
      ( r2_hidden(k1_mcart_1(A_42458),B_42459)
      | ~ m1_subset_1(A_42458,k2_zfmisc_1(B_42459,C_42460)) ) ),
    inference(resolution,[status(thm)],[c_119744,c_22])).

tff(c_131542,plain,(
    ! [A_43051,A_43052,B_43053,C_43054] :
      ( r2_hidden(k1_mcart_1(A_43051),k2_zfmisc_1(A_43052,B_43053))
      | ~ m1_subset_1(A_43051,k3_zfmisc_1(A_43052,B_43053,C_43054)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_120165])).

tff(c_131881,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_60,c_131542])).

tff(c_131898,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_131881,c_22])).

tff(c_131912,plain,(
    r2_hidden(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119839,c_131898])).

tff(c_132039,plain,(
    m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_131912,c_10])).

tff(c_131900,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_131881,c_20])).

tff(c_131914,plain,(
    r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_119999,c_131900])).

tff(c_132035,plain,(
    m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_131914,c_10])).

tff(c_131915,plain,(
    m1_subset_1(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_131881,c_10])).

tff(c_131933,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')),k2_mcart_1(k1_mcart_1('#skF_8'))) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_131915,c_28])).

tff(c_131945,plain,
    ( k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119839,c_119999,c_131933])).

tff(c_131946,plain,(
    k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_131945])).

tff(c_132640,plain,(
    ! [C_43064] : k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),C_43064) = k4_tarski(k1_mcart_1('#skF_8'),C_43064) ),
    inference(superposition,[status(thm),theory(equality)],[c_131946,c_14])).

tff(c_132695,plain,(
    ! [C_43064] :
      ( C_43064 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_43064) != '#skF_8'
      | ~ m1_subset_1(C_43064,'#skF_6')
      | ~ m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
      | ~ m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_132640,c_58])).

tff(c_133072,plain,(
    ! [C_43077] :
      ( C_43077 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_43077) != '#skF_8'
      | ~ m1_subset_1(C_43077,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132039,c_132035,c_132695])).

tff(c_133075,plain,
    ( k2_mcart_1('#skF_8') = '#skF_7'
    | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_124007,c_133072])).

tff(c_133078,plain,(
    k2_mcart_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_124559,c_133075])).

tff(c_133080,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119823,c_133078])).

tff(c_133087,plain,(
    ! [C_43078] : r2_hidden(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),C_43078) ),
    inference(splitRight,[status(thm)],[c_120009])).

tff(c_133103,plain,(
    ! [C_43078] : m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),C_43078) ),
    inference(resolution,[status(thm)],[c_133087,c_10])).

tff(c_157546,plain,(
    m1_subset_1(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_157512,c_10])).

tff(c_157564,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')),k2_mcart_1(k1_mcart_1('#skF_8'))) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157546,c_28])).

tff(c_157576,plain,
    ( k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119839,c_119999,c_157564])).

tff(c_157577,plain,(
    k4_tarski(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')) = k1_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_54,c_157576])).

tff(c_158136,plain,(
    ! [C_72044] : k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),C_72044) = k4_tarski(k1_mcart_1('#skF_8'),C_72044) ),
    inference(superposition,[status(thm),theory(equality)],[c_157577,c_14])).

tff(c_158184,plain,(
    ! [C_72044] :
      ( C_72044 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_72044) != '#skF_8'
      | ~ m1_subset_1(C_72044,'#skF_6')
      | ~ m1_subset_1(k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_5')
      | ~ m1_subset_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_158136,c_58])).

tff(c_158746,plain,(
    ! [C_72062] :
      ( C_72062 = '#skF_7'
      | k4_tarski(k1_mcart_1('#skF_8'),C_72062) != '#skF_8'
      | ~ m1_subset_1(C_72062,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_157703,c_133103,c_158184])).

tff(c_158749,plain,
    ( k2_mcart_1('#skF_8') = '#skF_7'
    | ~ m1_subset_1(k2_mcart_1('#skF_8'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_149617,c_158746])).

tff(c_158752,plain,(
    k2_mcart_1('#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150511,c_158749])).

tff(c_158754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_119823,c_158752])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:14:12 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 29.89/19.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.12/19.17  
% 30.12/19.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.12/19.17  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_4 > #skF_3
% 30.12/19.17  
% 30.12/19.17  %Foreground sorts:
% 30.12/19.17  
% 30.12/19.17  
% 30.12/19.17  %Background operators:
% 30.12/19.17  
% 30.12/19.17  
% 30.12/19.17  %Foreground operators:
% 30.12/19.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 30.12/19.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 30.12/19.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 30.12/19.17  tff('#skF_1', type, '#skF_1': $i > $i).
% 30.12/19.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 30.12/19.17  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 30.12/19.17  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 30.12/19.17  tff('#skF_7', type, '#skF_7': $i).
% 30.12/19.17  tff('#skF_5', type, '#skF_5': $i).
% 30.12/19.17  tff('#skF_6', type, '#skF_6': $i).
% 30.12/19.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 30.12/19.17  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 30.12/19.17  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 30.12/19.17  tff('#skF_8', type, '#skF_8': $i).
% 30.12/19.17  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 30.12/19.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 30.12/19.17  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 30.12/19.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 30.12/19.17  tff('#skF_4', type, '#skF_4': $i).
% 30.12/19.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 30.12/19.17  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 30.12/19.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 30.12/19.17  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 30.12/19.17  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 30.12/19.17  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 30.12/19.17  
% 30.12/19.22  tff(f_149, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 30.12/19.22  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 30.12/19.22  tff(f_121, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 30.12/19.22  tff(f_58, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 30.12/19.22  tff(f_56, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 30.12/19.22  tff(f_86, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(![C]: (m1_subset_1(C, k2_zfmisc_1(A, B)) => (C = k4_tarski(k1_mcart_1(C), k2_mcart_1(C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_mcart_1)).
% 30.12/19.22  tff(f_42, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 30.12/19.22  tff(f_54, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 30.12/19.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 30.12/19.22  tff(f_64, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 30.12/19.22  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 30.12/19.22  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 30.12/19.22  tff(f_46, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 30.12/19.22  tff(f_125, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 30.12/19.22  tff(c_56, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_149])).
% 30.12/19.22  tff(c_54, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_149])).
% 30.12/19.22  tff(c_52, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_149])).
% 30.12/19.22  tff(c_60, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 30.12/19.22  tff(c_119761, plain, (![A_42407, B_42408, C_42409, D_42410]: (k7_mcart_1(A_42407, B_42408, C_42409, D_42410)=k2_mcart_1(D_42410) | ~m1_subset_1(D_42410, k3_zfmisc_1(A_42407, B_42408, C_42409)) | k1_xboole_0=C_42409 | k1_xboole_0=B_42408 | k1_xboole_0=A_42407)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_119768, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_119761])).
% 30.12/19.22  tff(c_119772, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_119768])).
% 30.12/19.22  tff(c_50, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_149])).
% 30.12/19.22  tff(c_119823, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_119772, c_50])).
% 30.12/19.22  tff(c_40, plain, (![A_42, B_43, D_45]: (k4_zfmisc_1(A_42, B_43, k1_xboole_0, D_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_121])).
% 30.12/19.22  tff(c_44, plain, (![B_43, C_44, D_45]: (k4_zfmisc_1(k1_xboole_0, B_43, C_44, D_45)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_121])).
% 30.12/19.22  tff(c_18, plain, (![A_21, B_22, C_23, D_24]: (k2_zfmisc_1(k3_zfmisc_1(A_21, B_22, C_23), D_24)=k4_zfmisc_1(A_21, B_22, C_23, D_24))), inference(cnfTransformation, [status(thm)], [f_58])).
% 30.12/19.22  tff(c_191, plain, (![A_97, B_98, C_99]: (k2_zfmisc_1(k2_zfmisc_1(A_97, B_98), C_99)=k3_zfmisc_1(A_97, B_98, C_99))), inference(cnfTransformation, [status(thm)], [f_56])).
% 30.12/19.22  tff(c_16, plain, (![A_18, B_19, C_20]: (k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)=k3_zfmisc_1(A_18, B_19, C_20))), inference(cnfTransformation, [status(thm)], [f_56])).
% 30.12/19.22  tff(c_194, plain, (![A_97, B_98, C_99, C_20]: (k3_zfmisc_1(k2_zfmisc_1(A_97, B_98), C_99, C_20)=k2_zfmisc_1(k3_zfmisc_1(A_97, B_98, C_99), C_20))), inference(superposition, [status(thm), theory('equality')], [c_191, c_16])).
% 30.12/19.22  tff(c_135582, plain, (![A_97, B_98, C_99, C_20]: (k3_zfmisc_1(k2_zfmisc_1(A_97, B_98), C_99, C_20)=k4_zfmisc_1(A_97, B_98, C_99, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_194])).
% 30.12/19.22  tff(c_364, plain, (![C_139, A_140, B_141]: (k4_tarski(k1_mcart_1(C_139), k2_mcart_1(C_139))=C_139 | ~m1_subset_1(C_139, k2_zfmisc_1(A_140, B_141)) | k1_xboole_0=B_141 | k1_xboole_0=A_140)), inference(cnfTransformation, [status(thm)], [f_86])).
% 30.12/19.22  tff(c_137134, plain, (![C_43275, A_43276, B_43277, C_43278]: (k4_tarski(k1_mcart_1(C_43275), k2_mcart_1(C_43275))=C_43275 | ~m1_subset_1(C_43275, k3_zfmisc_1(A_43276, B_43277, C_43278)) | k1_xboole_0=C_43278 | k2_zfmisc_1(A_43276, B_43277)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_364])).
% 30.12/19.22  tff(c_137266, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_137134])).
% 30.12/19.22  tff(c_137315, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_137266])).
% 30.12/19.22  tff(c_137319, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_137315])).
% 30.12/19.22  tff(c_137625, plain, (![C_43287]: (k3_zfmisc_1('#skF_4', '#skF_5', C_43287)=k2_zfmisc_1(k1_xboole_0, C_43287))), inference(superposition, [status(thm), theory('equality')], [c_137319, c_16])).
% 30.12/19.22  tff(c_247, plain, (![A_109, B_110, C_111, D_112]: (k2_zfmisc_1(k3_zfmisc_1(A_109, B_110, C_111), D_112)=k4_zfmisc_1(A_109, B_110, C_111, D_112))), inference(cnfTransformation, [status(thm)], [f_58])).
% 30.12/19.22  tff(c_255, plain, (![B_110, A_109, D_112, C_111, C_20]: (k3_zfmisc_1(k3_zfmisc_1(A_109, B_110, C_111), D_112, C_20)=k2_zfmisc_1(k4_zfmisc_1(A_109, B_110, C_111, D_112), C_20))), inference(superposition, [status(thm), theory('equality')], [c_247, c_16])).
% 30.12/19.22  tff(c_137633, plain, (![C_43287, D_112, C_20]: (k3_zfmisc_1(k2_zfmisc_1(k1_xboole_0, C_43287), D_112, C_20)=k2_zfmisc_1(k4_zfmisc_1('#skF_4', '#skF_5', C_43287, D_112), C_20))), inference(superposition, [status(thm), theory('equality')], [c_137625, c_255])).
% 30.12/19.22  tff(c_140677, plain, (![C_43334, D_43335, C_43336]: (k2_zfmisc_1(k4_zfmisc_1('#skF_4', '#skF_5', C_43334, D_43335), C_43336)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_135582, c_137633])).
% 30.12/19.22  tff(c_140742, plain, (![C_43336]: (k2_zfmisc_1(k1_xboole_0, C_43336)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_140677])).
% 30.12/19.22  tff(c_137358, plain, (![C_20]: (k3_zfmisc_1('#skF_4', '#skF_5', C_20)=k2_zfmisc_1(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_137319, c_16])).
% 30.12/19.22  tff(c_140933, plain, (![C_43341]: (k3_zfmisc_1('#skF_4', '#skF_5', C_43341)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140742, c_137358])).
% 30.12/19.22  tff(c_140980, plain, (![C_43341, D_24]: (k4_zfmisc_1('#skF_4', '#skF_5', C_43341, D_24)=k2_zfmisc_1(k1_xboole_0, D_24))), inference(superposition, [status(thm), theory('equality')], [c_140933, c_18])).
% 30.12/19.22  tff(c_141800, plain, (![C_43351, D_43352]: (k4_zfmisc_1('#skF_4', '#skF_5', C_43351, D_43352)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_140742, c_140980])).
% 30.12/19.22  tff(c_36, plain, (![A_42, B_43, C_44, D_45]: (k4_zfmisc_1(A_42, B_43, C_44, D_45)!=k1_xboole_0 | k1_xboole_0=D_45 | k1_xboole_0=C_44 | k1_xboole_0=B_43 | k1_xboole_0=A_42)), inference(cnfTransformation, [status(thm)], [f_121])).
% 30.12/19.22  tff(c_141817, plain, (![D_43352, C_43351]: (k1_xboole_0=D_43352 | k1_xboole_0=C_43351 | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_141800, c_36])).
% 30.12/19.22  tff(c_141839, plain, (![D_43352, C_43351]: (k1_xboole_0=D_43352 | k1_xboole_0=C_43351)), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_141817])).
% 30.12/19.22  tff(c_141847, plain, (k1_xboole_0='#skF_6'), inference(splitLeft, [status(thm)], [c_141839])).
% 30.12/19.22  tff(c_141845, plain, (![C_43351]: (k1_xboole_0=C_43351)), inference(splitLeft, [status(thm)], [c_141839])).
% 30.12/19.22  tff(c_144332, plain, (![C_50428]: (C_50428='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_141847, c_141845])).
% 30.12/19.22  tff(c_145833, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_144332, c_52])).
% 30.12/19.22  tff(c_145836, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_141839])).
% 30.12/19.22  tff(c_145834, plain, (![D_43352]: (k1_xboole_0=D_43352)), inference(splitRight, [status(thm)], [c_141839])).
% 30.12/19.22  tff(c_148117, plain, (![D_64605]: (D_64605='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_145836, c_145834])).
% 30.12/19.22  tff(c_149616, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_148117, c_52])).
% 30.12/19.22  tff(c_149617, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_137315])).
% 30.12/19.22  tff(c_417, plain, (![A_152, B_153, C_154]: (k4_tarski('#skF_2'(A_152, B_153, C_154), '#skF_3'(A_152, B_153, C_154))=A_152 | ~r2_hidden(A_152, k2_zfmisc_1(B_153, C_154)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 30.12/19.22  tff(c_14, plain, (![A_15, B_16, C_17]: (k4_tarski(k4_tarski(A_15, B_16), C_17)=k3_mcart_1(A_15, B_16, C_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 30.12/19.22  tff(c_136957, plain, (![A_43263, B_43264, C_43265, C_43266]: (k3_mcart_1('#skF_2'(A_43263, B_43264, C_43265), '#skF_3'(A_43263, B_43264, C_43265), C_43266)=k4_tarski(A_43263, C_43266) | ~r2_hidden(A_43263, k2_zfmisc_1(B_43264, C_43265)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_14])).
% 30.12/19.22  tff(c_58, plain, (![H_61, F_55, G_59]: (H_61='#skF_7' | k3_mcart_1(F_55, G_59, H_61)!='#skF_8' | ~m1_subset_1(H_61, '#skF_6') | ~m1_subset_1(G_59, '#skF_5') | ~m1_subset_1(F_55, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_149])).
% 30.12/19.22  tff(c_136980, plain, (![C_43266, A_43263, B_43264, C_43265]: (C_43266='#skF_7' | k4_tarski(A_43263, C_43266)!='#skF_8' | ~m1_subset_1(C_43266, '#skF_6') | ~m1_subset_1('#skF_3'(A_43263, B_43264, C_43265), '#skF_5') | ~m1_subset_1('#skF_2'(A_43263, B_43264, C_43265), '#skF_4') | ~r2_hidden(A_43263, k2_zfmisc_1(B_43264, C_43265)))), inference(superposition, [status(thm), theory('equality')], [c_136957, c_58])).
% 30.12/19.22  tff(c_149621, plain, (![B_43264, C_43265]: (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_43264, C_43265), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_43264, C_43265), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_43264, C_43265)))), inference(superposition, [status(thm), theory('equality')], [c_149617, c_136980])).
% 30.12/19.22  tff(c_149654, plain, (![B_43264, C_43265]: (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_43264, C_43265), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_43264, C_43265), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_43264, C_43265)))), inference(negUnitSimplification, [status(thm)], [c_119823, c_149621])).
% 30.12/19.22  tff(c_149870, plain, (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_149654])).
% 30.12/19.22  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.12/19.22  tff(c_208, plain, (![A_100, B_101, C_102]: (r2_hidden(k1_mcart_1(A_100), B_101) | ~r2_hidden(A_100, k2_zfmisc_1(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 30.12/19.22  tff(c_312, plain, (![B_130, C_131]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_130, C_131))), B_130) | v1_xboole_0(k2_zfmisc_1(B_130, C_131)))), inference(resolution, [status(thm)], [c_4, c_208])).
% 30.12/19.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 30.12/19.22  tff(c_344, plain, (![B_132, C_133]: (~v1_xboole_0(B_132) | v1_xboole_0(k2_zfmisc_1(B_132, C_133)))), inference(resolution, [status(thm)], [c_312, c_2])).
% 30.12/19.22  tff(c_353, plain, (![A_18, B_19, C_20]: (~v1_xboole_0(k2_zfmisc_1(A_18, B_19)) | v1_xboole_0(k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_344])).
% 30.12/19.22  tff(c_12, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | v1_xboole_0(B_14) | ~m1_subset_1(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 30.12/19.22  tff(c_182, plain, (![A_94, C_95, B_96]: (r2_hidden(k2_mcart_1(A_94), C_95) | ~r2_hidden(A_94, k2_zfmisc_1(B_96, C_95)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 30.12/19.22  tff(c_35205, plain, (![A_25977, C_25978, B_25979]: (r2_hidden(k2_mcart_1(A_25977), C_25978) | v1_xboole_0(k2_zfmisc_1(B_25979, C_25978)) | ~m1_subset_1(A_25977, k2_zfmisc_1(B_25979, C_25978)))), inference(resolution, [status(thm)], [c_12, c_182])).
% 30.12/19.22  tff(c_35223, plain, (![A_25977, C_20, A_18, B_19]: (r2_hidden(k2_mcart_1(A_25977), C_20) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_18, B_19), C_20)) | ~m1_subset_1(A_25977, k3_zfmisc_1(A_18, B_19, C_20)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_35205])).
% 30.12/19.22  tff(c_72094, plain, (![A_38431, C_38432, A_38433, B_38434]: (r2_hidden(k2_mcart_1(A_38431), C_38432) | v1_xboole_0(k3_zfmisc_1(A_38433, B_38434, C_38432)) | ~m1_subset_1(A_38431, k3_zfmisc_1(A_38433, B_38434, C_38432)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_35223])).
% 30.12/19.22  tff(c_72170, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_6') | v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_72094])).
% 30.12/19.22  tff(c_72171, plain, (v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_72170])).
% 30.12/19.22  tff(c_36593, plain, (![A_26032, B_26033, C_26034, D_26035]: (~v1_xboole_0(k3_zfmisc_1(A_26032, B_26033, C_26034)) | v1_xboole_0(k4_zfmisc_1(A_26032, B_26033, C_26034, D_26035)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_344])).
% 30.12/19.22  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 30.12/19.22  tff(c_36660, plain, (![A_26032, B_26033, C_26034, D_26035]: (k4_zfmisc_1(A_26032, B_26033, C_26034, D_26035)=k1_xboole_0 | ~v1_xboole_0(k3_zfmisc_1(A_26032, B_26033, C_26034)))), inference(resolution, [status(thm)], [c_36593, c_6])).
% 30.12/19.22  tff(c_72379, plain, (![D_38435]: (k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', D_38435)=k1_xboole_0)), inference(resolution, [status(thm)], [c_72171, c_36660])).
% 30.12/19.22  tff(c_72510, plain, (![D_38435]: (k1_xboole_0=D_38435 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_72379, c_36])).
% 30.12/19.22  tff(c_72598, plain, (![D_38436]: (k1_xboole_0=D_38436)), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_72510])).
% 30.12/19.22  tff(c_539, plain, (![A_164, B_165, C_166, D_167]: (k7_mcart_1(A_164, B_165, C_166, D_167)=k2_mcart_1(D_167) | ~m1_subset_1(D_167, k3_zfmisc_1(A_164, B_165, C_166)) | k1_xboole_0=C_166 | k1_xboole_0=B_165 | k1_xboole_0=A_164)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_546, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_539])).
% 30.12/19.22  tff(c_550, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_546])).
% 30.12/19.22  tff(c_551, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_550, c_50])).
% 30.12/19.22  tff(c_13443, plain, (![A_97, B_98, C_99, C_20]: (k3_zfmisc_1(k2_zfmisc_1(A_97, B_98), C_99, C_20)=k4_zfmisc_1(A_97, B_98, C_99, C_20))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_194])).
% 30.12/19.22  tff(c_14962, plain, (![C_963, A_964, B_965, C_966]: (k4_tarski(k1_mcart_1(C_963), k2_mcart_1(C_963))=C_963 | ~m1_subset_1(C_963, k3_zfmisc_1(A_964, B_965, C_966)) | k1_xboole_0=C_966 | k2_zfmisc_1(A_964, B_965)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_364])).
% 30.12/19.22  tff(c_15067, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_14962])).
% 30.12/19.22  tff(c_15107, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_15067])).
% 30.12/19.22  tff(c_15114, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_15107])).
% 30.12/19.22  tff(c_15184, plain, (![C_971]: (k3_zfmisc_1('#skF_4', '#skF_5', C_971)=k2_zfmisc_1(k1_xboole_0, C_971))), inference(superposition, [status(thm), theory('equality')], [c_15114, c_16])).
% 30.12/19.22  tff(c_15192, plain, (![C_971, D_112, C_20]: (k3_zfmisc_1(k2_zfmisc_1(k1_xboole_0, C_971), D_112, C_20)=k2_zfmisc_1(k4_zfmisc_1('#skF_4', '#skF_5', C_971, D_112), C_20))), inference(superposition, [status(thm), theory('equality')], [c_15184, c_255])).
% 30.12/19.22  tff(c_17188, plain, (![C_1017, D_1018, C_1019]: (k2_zfmisc_1(k4_zfmisc_1('#skF_4', '#skF_5', C_1017, D_1018), C_1019)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_13443, c_15192])).
% 30.12/19.22  tff(c_17235, plain, (![C_1019]: (k2_zfmisc_1(k1_xboole_0, C_1019)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_17188])).
% 30.12/19.22  tff(c_15153, plain, (![C_20]: (k3_zfmisc_1('#skF_4', '#skF_5', C_20)=k2_zfmisc_1(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_15114, c_16])).
% 30.12/19.22  tff(c_17378, plain, (![C_1023]: (k3_zfmisc_1('#skF_4', '#skF_5', C_1023)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17235, c_15153])).
% 30.12/19.22  tff(c_17421, plain, (![C_1023, D_24]: (k4_zfmisc_1('#skF_4', '#skF_5', C_1023, D_24)=k2_zfmisc_1(k1_xboole_0, D_24))), inference(superposition, [status(thm), theory('equality')], [c_17378, c_18])).
% 30.12/19.22  tff(c_17763, plain, (![C_1031, D_1032]: (k4_zfmisc_1('#skF_4', '#skF_5', C_1031, D_1032)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_17235, c_17421])).
% 30.12/19.22  tff(c_17780, plain, (![D_1032, C_1031]: (k1_xboole_0=D_1032 | k1_xboole_0=C_1031 | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_17763, c_36])).
% 30.12/19.22  tff(c_17802, plain, (![D_1032, C_1031]: (k1_xboole_0=D_1032 | k1_xboole_0=C_1031)), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_17780])).
% 30.12/19.22  tff(c_17810, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_17802])).
% 30.12/19.22  tff(c_17808, plain, (![C_1031]: (k1_xboole_0=C_1031)), inference(splitLeft, [status(thm)], [c_17802])).
% 30.12/19.22  tff(c_19258, plain, (![C_7103]: (C_7103='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_17810, c_17808])).
% 30.12/19.22  tff(c_20335, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_19258, c_54])).
% 30.12/19.22  tff(c_20338, plain, (k1_xboole_0='#skF_6'), inference(splitRight, [status(thm)], [c_17802])).
% 30.12/19.22  tff(c_20336, plain, (![D_1032]: (k1_xboole_0=D_1032)), inference(splitRight, [status(thm)], [c_17802])).
% 30.12/19.22  tff(c_21839, plain, (![D_19253]: (D_19253='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_20338, c_20336])).
% 30.12/19.22  tff(c_22905, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_21839, c_52])).
% 30.12/19.22  tff(c_22906, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_15107])).
% 30.12/19.22  tff(c_22951, plain, (![A_25379, B_25380, C_25381, C_25382]: (k3_mcart_1('#skF_2'(A_25379, B_25380, C_25381), '#skF_3'(A_25379, B_25380, C_25381), C_25382)=k4_tarski(A_25379, C_25382) | ~r2_hidden(A_25379, k2_zfmisc_1(B_25380, C_25381)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_14])).
% 30.12/19.22  tff(c_23025, plain, (![C_25384, A_25385, B_25386, C_25387]: (C_25384='#skF_7' | k4_tarski(A_25385, C_25384)!='#skF_8' | ~m1_subset_1(C_25384, '#skF_6') | ~m1_subset_1('#skF_3'(A_25385, B_25386, C_25387), '#skF_5') | ~m1_subset_1('#skF_2'(A_25385, B_25386, C_25387), '#skF_4') | ~r2_hidden(A_25385, k2_zfmisc_1(B_25386, C_25387)))), inference(superposition, [status(thm), theory('equality')], [c_22951, c_58])).
% 30.12/19.22  tff(c_23027, plain, (![B_25386, C_25387]: (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_25386, C_25387), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_25386, C_25387), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_25386, C_25387)))), inference(superposition, [status(thm), theory('equality')], [c_22906, c_23025])).
% 30.12/19.22  tff(c_23034, plain, (![B_25386, C_25387]: (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_25386, C_25387), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_25386, C_25387), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_25386, C_25387)))), inference(negUnitSimplification, [status(thm)], [c_551, c_23027])).
% 30.12/19.22  tff(c_23266, plain, (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_23034])).
% 30.12/19.22  tff(c_341, plain, (![B_130, C_131]: (~v1_xboole_0(B_130) | v1_xboole_0(k2_zfmisc_1(B_130, C_131)))), inference(resolution, [status(thm)], [c_312, c_2])).
% 30.12/19.22  tff(c_355, plain, (![B_134, C_135]: (k2_zfmisc_1(B_134, C_135)=k1_xboole_0 | ~v1_xboole_0(B_134))), inference(resolution, [status(thm)], [c_344, c_6])).
% 30.12/19.22  tff(c_357, plain, (![B_130, C_131, C_135]: (k2_zfmisc_1(k2_zfmisc_1(B_130, C_131), C_135)=k1_xboole_0 | ~v1_xboole_0(B_130))), inference(resolution, [status(thm)], [c_341, c_355])).
% 30.12/19.22  tff(c_360, plain, (![B_136, C_137, C_138]: (k3_zfmisc_1(B_136, C_137, C_138)=k1_xboole_0 | ~v1_xboole_0(B_136))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_357])).
% 30.12/19.22  tff(c_393, plain, (![B_148, C_149, C_150, C_151]: (k3_zfmisc_1(k2_zfmisc_1(B_148, C_149), C_150, C_151)=k1_xboole_0 | ~v1_xboole_0(B_148))), inference(resolution, [status(thm)], [c_341, c_360])).
% 30.12/19.22  tff(c_20, plain, (![A_25, C_27, B_26]: (r2_hidden(k2_mcart_1(A_25), C_27) | ~r2_hidden(A_25, k2_zfmisc_1(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 30.12/19.22  tff(c_199, plain, (![A_25, C_99, A_97, B_98]: (r2_hidden(k2_mcart_1(A_25), C_99) | ~r2_hidden(A_25, k3_zfmisc_1(A_97, B_98, C_99)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_20])).
% 30.12/19.22  tff(c_401, plain, (![A_25, C_151, B_148]: (r2_hidden(k2_mcart_1(A_25), C_151) | ~r2_hidden(A_25, k1_xboole_0) | ~v1_xboole_0(B_148))), inference(superposition, [status(thm), theory('equality')], [c_393, c_199])).
% 30.12/19.22  tff(c_441, plain, (![B_148]: (~v1_xboole_0(B_148))), inference(splitLeft, [status(thm)], [c_401])).
% 30.12/19.22  tff(c_472, plain, (![A_158, B_159]: (r2_hidden(A_158, B_159) | ~m1_subset_1(A_158, B_159))), inference(negUnitSimplification, [status(thm)], [c_441, c_12])).
% 30.12/19.22  tff(c_24376, plain, (![A_25474, C_25475, A_25476, B_25477]: (r2_hidden(k2_mcart_1(A_25474), C_25475) | ~m1_subset_1(A_25474, k3_zfmisc_1(A_25476, B_25477, C_25475)))), inference(resolution, [status(thm)], [c_472, c_199])).
% 30.12/19.22  tff(c_24557, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_60, c_24376])).
% 30.12/19.22  tff(c_10, plain, (![A_11, B_12]: (m1_subset_1(A_11, B_12) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 30.12/19.22  tff(c_24560, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_24557, c_10])).
% 30.12/19.22  tff(c_24564, plain, $false, inference(negUnitSimplification, [status(thm)], [c_23266, c_24560])).
% 30.12/19.22  tff(c_24566, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_23034])).
% 30.12/19.22  tff(c_650, plain, (![A_182, B_183, C_184, D_185]: (k5_mcart_1(A_182, B_183, C_184, D_185)=k1_mcart_1(k1_mcart_1(D_185)) | ~m1_subset_1(D_185, k3_zfmisc_1(A_182, B_183, C_184)) | k1_xboole_0=C_184 | k1_xboole_0=B_183 | k1_xboole_0=A_182)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_669, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_650])).
% 30.12/19.22  tff(c_677, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_669])).
% 30.12/19.22  tff(c_22, plain, (![A_25, B_26, C_27]: (r2_hidden(k1_mcart_1(A_25), B_26) | ~r2_hidden(A_25, k2_zfmisc_1(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 30.12/19.22  tff(c_706, plain, (![A_189, B_190, C_191]: (r2_hidden(k1_mcart_1(A_189), B_190) | ~m1_subset_1(A_189, k2_zfmisc_1(B_190, C_191)))), inference(resolution, [status(thm)], [c_472, c_22])).
% 30.12/19.22  tff(c_31457, plain, (![A_25796, A_25797, B_25798, C_25799]: (r2_hidden(k1_mcart_1(A_25796), k2_zfmisc_1(A_25797, B_25798)) | ~m1_subset_1(A_25796, k3_zfmisc_1(A_25797, B_25798, C_25799)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_706])).
% 30.12/19.22  tff(c_31753, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_31457])).
% 30.12/19.22  tff(c_31770, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_4')), inference(resolution, [status(thm)], [c_31753, c_22])).
% 30.12/19.22  tff(c_31784, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_677, c_31770])).
% 30.12/19.22  tff(c_31952, plain, (m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_31784, c_10])).
% 30.12/19.22  tff(c_607, plain, (![A_175, B_176, C_177, D_178]: (k6_mcart_1(A_175, B_176, C_177, D_178)=k2_mcart_1(k1_mcart_1(D_178)) | ~m1_subset_1(D_178, k3_zfmisc_1(A_175, B_176, C_177)) | k1_xboole_0=C_177 | k1_xboole_0=B_176 | k1_xboole_0=A_175)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_622, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_607])).
% 30.12/19.22  tff(c_629, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_622])).
% 30.12/19.22  tff(c_1848, plain, (![D_238, B_239, A_237, C_240, A_236]: (r2_hidden(k2_mcart_1(A_236), D_238) | ~r2_hidden(A_236, k4_zfmisc_1(A_237, B_239, C_240, D_238)))), inference(superposition, [status(thm), theory('equality')], [c_247, c_20])).
% 30.12/19.22  tff(c_1949, plain, (![A_241, D_242]: (r2_hidden(k2_mcart_1(A_241), D_242) | ~r2_hidden(A_241, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1848])).
% 30.12/19.22  tff(c_1983, plain, (![D_242]: (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), D_242) | ~r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_629, c_1949])).
% 30.12/19.22  tff(c_1999, plain, (~r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1983])).
% 30.12/19.22  tff(c_3889, plain, (![C_380, A_381, B_382, C_383]: (k4_tarski(k1_mcart_1(C_380), k2_mcart_1(C_380))=C_380 | ~m1_subset_1(C_380, k3_zfmisc_1(A_381, B_382, C_383)) | k1_xboole_0=C_383 | k2_zfmisc_1(A_381, B_382)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_364])).
% 30.12/19.22  tff(c_3982, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_3889])).
% 30.12/19.22  tff(c_4018, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_3982])).
% 30.12/19.22  tff(c_4022, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_4018])).
% 30.12/19.22  tff(c_4061, plain, (![C_20]: (k3_zfmisc_1('#skF_4', '#skF_5', C_20)=k2_zfmisc_1(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_4022, c_16])).
% 30.12/19.22  tff(c_4089, plain, (m1_subset_1('#skF_8', k2_zfmisc_1(k1_xboole_0, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_4061, c_60])).
% 30.12/19.22  tff(c_486, plain, (![A_158, B_26, C_27]: (r2_hidden(k1_mcart_1(A_158), B_26) | ~m1_subset_1(A_158, k2_zfmisc_1(B_26, C_27)))), inference(resolution, [status(thm)], [c_472, c_22])).
% 30.12/19.22  tff(c_4184, plain, (r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0)), inference(resolution, [status(thm)], [c_4089, c_486])).
% 30.12/19.22  tff(c_4192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1999, c_4184])).
% 30.12/19.22  tff(c_4193, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_4018])).
% 30.12/19.22  tff(c_4244, plain, (![A_390, B_391, C_392, C_393]: (k3_mcart_1('#skF_2'(A_390, B_391, C_392), '#skF_3'(A_390, B_391, C_392), C_393)=k4_tarski(A_390, C_393) | ~r2_hidden(A_390, k2_zfmisc_1(B_391, C_392)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_14])).
% 30.12/19.22  tff(c_4280, plain, (![C_394, A_395, B_396, C_397]: (C_394='#skF_7' | k4_tarski(A_395, C_394)!='#skF_8' | ~m1_subset_1(C_394, '#skF_6') | ~m1_subset_1('#skF_3'(A_395, B_396, C_397), '#skF_5') | ~m1_subset_1('#skF_2'(A_395, B_396, C_397), '#skF_4') | ~r2_hidden(A_395, k2_zfmisc_1(B_396, C_397)))), inference(superposition, [status(thm), theory('equality')], [c_4244, c_58])).
% 30.12/19.22  tff(c_4282, plain, (![B_396, C_397]: (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_396, C_397), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_396, C_397), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_396, C_397)))), inference(superposition, [status(thm), theory('equality')], [c_4193, c_4280])).
% 30.12/19.22  tff(c_4289, plain, (![B_396, C_397]: (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_396, C_397), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_396, C_397), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_396, C_397)))), inference(negUnitSimplification, [status(thm)], [c_551, c_4282])).
% 30.12/19.22  tff(c_4604, plain, (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_4289])).
% 30.12/19.22  tff(c_5611, plain, (![A_530, C_531, A_532, B_533]: (r2_hidden(k2_mcart_1(A_530), C_531) | ~m1_subset_1(A_530, k3_zfmisc_1(A_532, B_533, C_531)))), inference(resolution, [status(thm)], [c_472, c_199])).
% 30.12/19.22  tff(c_5764, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_60, c_5611])).
% 30.12/19.22  tff(c_5767, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_5764, c_10])).
% 30.12/19.22  tff(c_5771, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4604, c_5767])).
% 30.12/19.22  tff(c_5773, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_4289])).
% 30.12/19.22  tff(c_12070, plain, (![A_814, A_815, B_816, C_817]: (r2_hidden(k1_mcart_1(A_814), k2_zfmisc_1(A_815, B_816)) | ~m1_subset_1(A_814, k3_zfmisc_1(A_815, B_816, C_817)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_706])).
% 30.12/19.22  tff(c_12365, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_12070])).
% 30.12/19.22  tff(c_12382, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_4')), inference(resolution, [status(thm)], [c_12365, c_22])).
% 30.12/19.22  tff(c_12396, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_677, c_12382])).
% 30.12/19.22  tff(c_12498, plain, (m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_12396, c_10])).
% 30.12/19.22  tff(c_12384, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_12365, c_20])).
% 30.12/19.22  tff(c_12398, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_629, c_12384])).
% 30.12/19.22  tff(c_12494, plain, (m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_12398, c_10])).
% 30.12/19.22  tff(c_12399, plain, (m1_subset_1(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_12365, c_10])).
% 30.12/19.22  tff(c_28, plain, (![C_36, A_33, B_34]: (k4_tarski(k1_mcart_1(C_36), k2_mcart_1(C_36))=C_36 | ~m1_subset_1(C_36, k2_zfmisc_1(A_33, B_34)) | k1_xboole_0=B_34 | k1_xboole_0=A_33)), inference(cnfTransformation, [status(thm)], [f_86])).
% 30.12/19.22  tff(c_12417, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')), k2_mcart_1(k1_mcart_1('#skF_8')))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_12399, c_28])).
% 30.12/19.22  tff(c_12429, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_629, c_677, c_12417])).
% 30.12/19.22  tff(c_12430, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_12429])).
% 30.12/19.22  tff(c_12863, plain, (![C_833]: (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), C_833)=k4_tarski(k1_mcart_1('#skF_8'), C_833))), inference(superposition, [status(thm), theory('equality')], [c_12430, c_14])).
% 30.12/19.22  tff(c_12904, plain, (![C_833]: (C_833='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_833)!='#skF_8' | ~m1_subset_1(C_833, '#skF_6') | ~m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12863, c_58])).
% 30.12/19.22  tff(c_13130, plain, (![C_837]: (C_837='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_837)!='#skF_8' | ~m1_subset_1(C_837, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_12498, c_12494, c_12904])).
% 30.12/19.22  tff(c_13133, plain, (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_4193, c_13130])).
% 30.12/19.22  tff(c_13136, plain, (k2_mcart_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_5773, c_13133])).
% 30.12/19.22  tff(c_13138, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_13136])).
% 30.12/19.22  tff(c_13140, plain, (r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_1983])).
% 30.12/19.22  tff(c_13145, plain, (![A_838, D_839]: (m1_subset_1(k2_mcart_1(A_838), D_839) | ~r2_hidden(A_838, k1_xboole_0))), inference(resolution, [status(thm)], [c_1949, c_10])).
% 30.12/19.22  tff(c_13169, plain, (![D_839]: (m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), D_839) | ~r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_629, c_13145])).
% 30.12/19.22  tff(c_13183, plain, (![D_839]: (m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), D_839))), inference(demodulation, [status(thm), theory('equality')], [c_13140, c_13169])).
% 30.12/19.22  tff(c_31787, plain, (m1_subset_1(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_31753, c_10])).
% 30.12/19.22  tff(c_31805, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')), k2_mcart_1(k1_mcart_1('#skF_8')))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_31787, c_28])).
% 30.12/19.22  tff(c_31817, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_629, c_677, c_31805])).
% 30.12/19.22  tff(c_31818, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_31817])).
% 30.12/19.22  tff(c_32176, plain, (![C_25806]: (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), C_25806)=k4_tarski(k1_mcart_1('#skF_8'), C_25806))), inference(superposition, [status(thm), theory('equality')], [c_31818, c_14])).
% 30.12/19.22  tff(c_32224, plain, (![C_25806]: (C_25806='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_25806)!='#skF_8' | ~m1_subset_1(C_25806, '#skF_6') | ~m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_32176, c_58])).
% 30.12/19.22  tff(c_32619, plain, (![C_25816]: (C_25816='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_25816)!='#skF_8' | ~m1_subset_1(C_25816, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_31952, c_13183, c_32224])).
% 30.12/19.22  tff(c_32622, plain, (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_22906, c_32619])).
% 30.12/19.22  tff(c_32625, plain, (k2_mcart_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_24566, c_32622])).
% 30.12/19.22  tff(c_32627, plain, $false, inference(negUnitSimplification, [status(thm)], [c_551, c_32625])).
% 30.12/19.22  tff(c_32629, plain, (![A_25817, C_25818]: (r2_hidden(k2_mcart_1(A_25817), C_25818) | ~r2_hidden(A_25817, k1_xboole_0))), inference(splitRight, [status(thm)], [c_401])).
% 30.12/19.22  tff(c_32655, plain, (![C_25818, A_25817]: (~v1_xboole_0(C_25818) | ~r2_hidden(A_25817, k1_xboole_0))), inference(resolution, [status(thm)], [c_32629, c_2])).
% 30.12/19.22  tff(c_32657, plain, (![A_25819]: (~r2_hidden(A_25819, k1_xboole_0))), inference(splitLeft, [status(thm)], [c_32655])).
% 30.12/19.22  tff(c_32672, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_32657])).
% 30.12/19.22  tff(c_37784, plain, (![C_26071, A_26072, B_26073, C_26074]: (k4_tarski(k1_mcart_1(C_26071), k2_mcart_1(C_26071))=C_26071 | ~m1_subset_1(C_26071, k3_zfmisc_1(A_26072, B_26073, C_26074)) | k1_xboole_0=C_26074 | k2_zfmisc_1(A_26072, B_26073)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_364])).
% 30.12/19.22  tff(c_37821, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_37784])).
% 30.12/19.22  tff(c_37833, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_37821])).
% 30.12/19.22  tff(c_37834, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_37833])).
% 30.12/19.22  tff(c_373, plain, (![A_142, B_143, C_144]: (~v1_xboole_0(k2_zfmisc_1(A_142, B_143)) | v1_xboole_0(k3_zfmisc_1(A_142, B_143, C_144)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_344])).
% 30.12/19.22  tff(c_354, plain, (![B_132, C_133]: (k2_zfmisc_1(B_132, C_133)=k1_xboole_0 | ~v1_xboole_0(B_132))), inference(resolution, [status(thm)], [c_344, c_6])).
% 30.12/19.22  tff(c_377, plain, (![A_142, B_143, C_144, C_133]: (k2_zfmisc_1(k3_zfmisc_1(A_142, B_143, C_144), C_133)=k1_xboole_0 | ~v1_xboole_0(k2_zfmisc_1(A_142, B_143)))), inference(resolution, [status(thm)], [c_373, c_354])).
% 30.12/19.22  tff(c_383, plain, (![A_142, B_143, C_144, C_133]: (k4_zfmisc_1(A_142, B_143, C_144, C_133)=k1_xboole_0 | ~v1_xboole_0(k2_zfmisc_1(A_142, B_143)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_377])).
% 30.12/19.22  tff(c_37906, plain, (![C_144, C_133]: (k4_zfmisc_1('#skF_4', '#skF_5', C_144, C_133)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_37834, c_383])).
% 30.12/19.22  tff(c_38087, plain, (![C_26076, C_26077]: (k4_zfmisc_1('#skF_4', '#skF_5', C_26076, C_26077)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32672, c_37906])).
% 30.12/19.22  tff(c_38126, plain, (![C_26077, C_26076]: (k1_xboole_0=C_26077 | k1_xboole_0=C_26076 | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38087, c_36])).
% 30.12/19.22  tff(c_38169, plain, (![C_26077, C_26076]: (k1_xboole_0=C_26077 | k1_xboole_0=C_26076)), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_38126])).
% 30.12/19.22  tff(c_38181, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_38169])).
% 30.12/19.22  tff(c_38179, plain, (![C_26076]: (k1_xboole_0=C_26076)), inference(splitLeft, [status(thm)], [c_38169])).
% 30.12/19.22  tff(c_38395, plain, (![C_28109]: (C_28109='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_38181, c_38179])).
% 30.12/19.22  tff(c_38588, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_38395, c_54])).
% 30.12/19.22  tff(c_38637, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_38169])).
% 30.12/19.22  tff(c_38589, plain, (![C_26077]: (k1_xboole_0=C_26077)), inference(splitRight, [status(thm)], [c_38169])).
% 30.12/19.22  tff(c_38851, plain, (![C_32246]: (C_32246='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_38637, c_38589])).
% 30.12/19.22  tff(c_39025, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_38851, c_56])).
% 30.12/19.22  tff(c_39027, plain, (k2_zfmisc_1('#skF_4', '#skF_5')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_37833])).
% 30.12/19.22  tff(c_72981, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_72598, c_39027])).
% 30.12/19.22  tff(c_72983, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_72170])).
% 30.12/19.22  tff(c_73008, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_353, c_72983])).
% 30.12/19.22  tff(c_33507, plain, (![A_25897, A_25898, B_25899, C_25900]: (r2_hidden(k1_mcart_1(A_25897), k2_zfmisc_1(A_25898, B_25899)) | ~r2_hidden(A_25897, k3_zfmisc_1(A_25898, B_25899, C_25900)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_208])).
% 30.12/19.22  tff(c_119281, plain, (![A_42398, A_42399, B_42400, C_42401]: (r2_hidden(k1_mcart_1(A_42398), k2_zfmisc_1(A_42399, B_42400)) | v1_xboole_0(k3_zfmisc_1(A_42399, B_42400, C_42401)) | ~m1_subset_1(A_42398, k3_zfmisc_1(A_42399, B_42400, C_42401)))), inference(resolution, [status(thm)], [c_12, c_33507])).
% 30.12/19.22  tff(c_119374, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5')) | v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_119281])).
% 30.12/19.22  tff(c_119388, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_72983, c_119374])).
% 30.12/19.22  tff(c_119425, plain, (m1_subset_1(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_119388, c_10])).
% 30.12/19.22  tff(c_32785, plain, (![A_25828, B_25829, C_25830, D_25831]: (k5_mcart_1(A_25828, B_25829, C_25830, D_25831)=k1_mcart_1(k1_mcart_1(D_25831)) | ~m1_subset_1(D_25831, k3_zfmisc_1(A_25828, B_25829, C_25830)) | k1_xboole_0=C_25830 | k1_xboole_0=B_25829 | k1_xboole_0=A_25828)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_32798, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_32785])).
% 30.12/19.22  tff(c_32803, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_32798])).
% 30.12/19.22  tff(c_119405, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_4')), inference(resolution, [status(thm)], [c_119388, c_22])).
% 30.12/19.22  tff(c_119422, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_32803, c_119405])).
% 30.12/19.22  tff(c_119510, plain, (m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_119422, c_10])).
% 30.12/19.22  tff(c_32811, plain, (![A_25832, B_25833, C_25834, D_25835]: (k6_mcart_1(A_25832, B_25833, C_25834, D_25835)=k2_mcart_1(k1_mcart_1(D_25835)) | ~m1_subset_1(D_25835, k3_zfmisc_1(A_25832, B_25833, C_25834)) | k1_xboole_0=C_25834 | k1_xboole_0=B_25833 | k1_xboole_0=A_25832)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_32824, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_32811])).
% 30.12/19.22  tff(c_32829, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_32824])).
% 30.12/19.22  tff(c_119407, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_119388, c_20])).
% 30.12/19.22  tff(c_119424, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_32829, c_119407])).
% 30.12/19.22  tff(c_119502, plain, (m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_119424, c_10])).
% 30.12/19.22  tff(c_48, plain, (![A_46, B_47]: (k2_mcart_1(k4_tarski(A_46, B_47))=B_47)), inference(cnfTransformation, [status(thm)], [f_125])).
% 30.12/19.22  tff(c_429, plain, (![A_152, B_153, C_154]: (k2_mcart_1(A_152)='#skF_3'(A_152, B_153, C_154) | ~r2_hidden(A_152, k2_zfmisc_1(B_153, C_154)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_48])).
% 30.12/19.22  tff(c_119394, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))='#skF_3'(k1_mcart_1('#skF_8'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_119388, c_429])).
% 30.12/19.22  tff(c_119416, plain, ('#skF_3'(k1_mcart_1('#skF_8'), '#skF_4', '#skF_5')=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32829, c_119394])).
% 30.12/19.22  tff(c_46, plain, (![A_46, B_47]: (k1_mcart_1(k4_tarski(A_46, B_47))=A_46)), inference(cnfTransformation, [status(thm)], [f_125])).
% 30.12/19.22  tff(c_426, plain, (![A_152, B_153, C_154]: (k1_mcart_1(A_152)='#skF_2'(A_152, B_153, C_154) | ~r2_hidden(A_152, k2_zfmisc_1(B_153, C_154)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_46])).
% 30.12/19.22  tff(c_119397, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))='#skF_2'(k1_mcart_1('#skF_8'), '#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_119388, c_426])).
% 30.12/19.22  tff(c_119418, plain, ('#skF_2'(k1_mcart_1('#skF_8'), '#skF_4', '#skF_5')=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_32803, c_119397])).
% 30.12/19.22  tff(c_32698, plain, (![A_25821, B_25822, C_25823, D_25824]: (k7_mcart_1(A_25821, B_25822, C_25823, D_25824)=k2_mcart_1(D_25824) | ~m1_subset_1(D_25824, k3_zfmisc_1(A_25821, B_25822, C_25823)) | k1_xboole_0=C_25823 | k1_xboole_0=B_25822 | k1_xboole_0=A_25821)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_32708, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_32698])).
% 30.12/19.22  tff(c_32712, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_32708])).
% 30.12/19.22  tff(c_32755, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_32712, c_50])).
% 30.12/19.22  tff(c_39026, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_37833])).
% 30.12/19.22  tff(c_36676, plain, (![A_26036, B_26037, C_26038, C_26039]: (k3_mcart_1('#skF_2'(A_26036, B_26037, C_26038), '#skF_3'(A_26036, B_26037, C_26038), C_26039)=k4_tarski(A_26036, C_26039) | ~r2_hidden(A_26036, k2_zfmisc_1(B_26037, C_26038)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_14])).
% 30.12/19.22  tff(c_36695, plain, (![C_26039, A_26036, B_26037, C_26038]: (C_26039='#skF_7' | k4_tarski(A_26036, C_26039)!='#skF_8' | ~m1_subset_1(C_26039, '#skF_6') | ~m1_subset_1('#skF_3'(A_26036, B_26037, C_26038), '#skF_5') | ~m1_subset_1('#skF_2'(A_26036, B_26037, C_26038), '#skF_4') | ~r2_hidden(A_26036, k2_zfmisc_1(B_26037, C_26038)))), inference(superposition, [status(thm), theory('equality')], [c_36676, c_58])).
% 30.12/19.22  tff(c_39030, plain, (![B_26037, C_26038]: (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_26037, C_26038), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_26037, C_26038), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_26037, C_26038)))), inference(superposition, [status(thm), theory('equality')], [c_39026, c_36695])).
% 30.12/19.22  tff(c_39053, plain, (![B_26037, C_26038]: (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_26037, C_26038), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_26037, C_26038), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_26037, C_26038)))), inference(negUnitSimplification, [status(thm)], [c_32755, c_39030])).
% 30.12/19.22  tff(c_39622, plain, (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_39053])).
% 30.12/19.22  tff(c_303, plain, (![A_126, C_127, A_128, B_129]: (r2_hidden(k2_mcart_1(A_126), C_127) | ~r2_hidden(A_126, k3_zfmisc_1(A_128, B_129, C_127)))), inference(superposition, [status(thm), theory('equality')], [c_191, c_20])).
% 30.12/19.22  tff(c_55506, plain, (![A_34758, C_34759, A_34760, B_34761]: (r2_hidden(k2_mcart_1(A_34758), C_34759) | v1_xboole_0(k3_zfmisc_1(A_34760, B_34761, C_34759)) | ~m1_subset_1(A_34758, k3_zfmisc_1(A_34760, B_34761, C_34759)))), inference(resolution, [status(thm)], [c_12, c_303])).
% 30.12/19.22  tff(c_55582, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_6') | v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_60, c_55506])).
% 30.12/19.22  tff(c_55583, plain, (v1_xboole_0(k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_55582])).
% 30.12/19.22  tff(c_55795, plain, (![D_34762]: (k4_zfmisc_1('#skF_4', '#skF_5', '#skF_6', D_34762)=k1_xboole_0)), inference(resolution, [status(thm)], [c_55583, c_36660])).
% 30.12/19.22  tff(c_55923, plain, (![D_34762]: (k1_xboole_0=D_34762 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_55795, c_36])).
% 30.12/19.22  tff(c_56010, plain, (![D_34763]: (k1_xboole_0=D_34763)), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_55923])).
% 30.12/19.22  tff(c_56367, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_56010, c_39027])).
% 30.12/19.22  tff(c_56368, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_55582])).
% 30.12/19.22  tff(c_56372, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_56368, c_10])).
% 30.12/19.22  tff(c_56379, plain, $false, inference(negUnitSimplification, [status(thm)], [c_39622, c_56372])).
% 30.12/19.22  tff(c_58686, plain, (![B_38129, C_38130]: (~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_38129, C_38130), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_38129, C_38130), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_38129, C_38130)))), inference(splitRight, [status(thm)], [c_39053])).
% 30.12/19.22  tff(c_58729, plain, (![B_38129, C_38130]: (~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_38129, C_38130), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_38129, C_38130), '#skF_4') | v1_xboole_0(k2_zfmisc_1(B_38129, C_38130)) | ~m1_subset_1(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_38129, C_38130)))), inference(resolution, [status(thm)], [c_12, c_58686])).
% 30.12/19.22  tff(c_119635, plain, (~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), '#skF_4', '#skF_5'), '#skF_5') | ~m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4') | v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5')) | ~m1_subset_1(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_119418, c_58729])).
% 30.12/19.22  tff(c_119710, plain, (v1_xboole_0(k2_zfmisc_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_119425, c_119510, c_119502, c_119416, c_119635])).
% 30.12/19.22  tff(c_119712, plain, $false, inference(negUnitSimplification, [status(thm)], [c_73008, c_119710])).
% 30.12/19.22  tff(c_119713, plain, (![C_25818]: (~v1_xboole_0(C_25818))), inference(splitRight, [status(thm)], [c_32655])).
% 30.12/19.22  tff(c_119744, plain, (![A_42405, B_42406]: (r2_hidden(A_42405, B_42406) | ~m1_subset_1(A_42405, B_42406))), inference(negUnitSimplification, [status(thm)], [c_119713, c_12])).
% 30.12/19.22  tff(c_133124, plain, (![A_43080, C_43081, B_43082]: (r2_hidden(k2_mcart_1(A_43080), C_43081) | ~m1_subset_1(A_43080, k2_zfmisc_1(B_43082, C_43081)))), inference(resolution, [status(thm)], [c_119744, c_20])).
% 30.12/19.22  tff(c_150294, plain, (![A_71741, C_71742, A_71743, B_71744]: (r2_hidden(k2_mcart_1(A_71741), C_71742) | ~m1_subset_1(A_71741, k3_zfmisc_1(A_71743, B_71744, C_71742)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_133124])).
% 30.12/19.22  tff(c_150502, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_60, c_150294])).
% 30.12/19.22  tff(c_150505, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_150502, c_10])).
% 30.12/19.22  tff(c_150509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_149870, c_150505])).
% 30.12/19.22  tff(c_150511, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_149654])).
% 30.12/19.22  tff(c_119828, plain, (![A_42415, B_42416, C_42417, D_42418]: (k5_mcart_1(A_42415, B_42416, C_42417, D_42418)=k1_mcart_1(k1_mcart_1(D_42418)) | ~m1_subset_1(D_42418, k3_zfmisc_1(A_42415, B_42416, C_42417)) | k1_xboole_0=C_42417 | k1_xboole_0=B_42416 | k1_xboole_0=A_42415)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_119835, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_119828])).
% 30.12/19.22  tff(c_119839, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_119835])).
% 30.12/19.22  tff(c_119717, plain, (![A_13, B_14]: (r2_hidden(A_13, B_14) | ~m1_subset_1(A_13, B_14))), inference(negUnitSimplification, [status(thm)], [c_119713, c_12])).
% 30.12/19.22  tff(c_134933, plain, (![A_43166, A_43167, B_43168, C_43169]: (r2_hidden(k1_mcart_1(A_43166), k2_zfmisc_1(A_43167, B_43168)) | ~r2_hidden(A_43166, k3_zfmisc_1(A_43167, B_43168, C_43169)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_208])).
% 30.12/19.22  tff(c_157186, plain, (![A_72025, A_72026, B_72027, C_72028]: (r2_hidden(k1_mcart_1(A_72025), k2_zfmisc_1(A_72026, B_72027)) | ~m1_subset_1(A_72025, k3_zfmisc_1(A_72026, B_72027, C_72028)))), inference(resolution, [status(thm)], [c_119717, c_134933])).
% 30.12/19.22  tff(c_157512, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_157186])).
% 30.12/19.22  tff(c_157529, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_4')), inference(resolution, [status(thm)], [c_157512, c_22])).
% 30.12/19.22  tff(c_157543, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119839, c_157529])).
% 30.12/19.22  tff(c_157703, plain, (m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_157543, c_10])).
% 30.12/19.22  tff(c_119967, plain, (![A_42433, B_42434, C_42435, D_42436]: (k6_mcart_1(A_42433, B_42434, C_42435, D_42436)=k2_mcart_1(k1_mcart_1(D_42436)) | ~m1_subset_1(D_42436, k3_zfmisc_1(A_42433, B_42434, C_42435)) | k1_xboole_0=C_42435 | k1_xboole_0=B_42434 | k1_xboole_0=A_42433)), inference(cnfTransformation, [status(thm)], [f_106])).
% 30.12/19.22  tff(c_119990, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_60, c_119967])).
% 30.12/19.22  tff(c_119999, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_52, c_119990])).
% 30.12/19.22  tff(c_32628, plain, (![A_25, C_151]: (r2_hidden(k2_mcart_1(A_25), C_151) | ~r2_hidden(A_25, k1_xboole_0))), inference(splitRight, [status(thm)], [c_401])).
% 30.12/19.22  tff(c_120009, plain, (![C_151]: (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), C_151) | ~r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_119999, c_32628])).
% 30.12/19.22  tff(c_120048, plain, (~r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_120009])).
% 30.12/19.22  tff(c_123606, plain, (![C_42614, A_42615, B_42616, C_42617]: (k4_tarski(k1_mcart_1(C_42614), k2_mcart_1(C_42614))=C_42614 | ~m1_subset_1(C_42614, k3_zfmisc_1(A_42615, B_42616, C_42617)) | k1_xboole_0=C_42617 | k2_zfmisc_1(A_42615, B_42616)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_364])).
% 30.12/19.22  tff(c_123729, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_123606])).
% 30.12/19.22  tff(c_123775, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_52, c_123729])).
% 30.12/19.22  tff(c_123810, plain, (k2_zfmisc_1('#skF_4', '#skF_5')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_123775])).
% 30.12/19.22  tff(c_123849, plain, (![C_20]: (k3_zfmisc_1('#skF_4', '#skF_5', C_20)=k2_zfmisc_1(k1_xboole_0, C_20))), inference(superposition, [status(thm), theory('equality')], [c_123810, c_16])).
% 30.12/19.22  tff(c_123939, plain, (m1_subset_1('#skF_8', k2_zfmisc_1(k1_xboole_0, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_123849, c_60])).
% 30.12/19.22  tff(c_119758, plain, (![A_42405, B_26, C_27]: (r2_hidden(k1_mcart_1(A_42405), B_26) | ~m1_subset_1(A_42405, k2_zfmisc_1(B_26, C_27)))), inference(resolution, [status(thm)], [c_119744, c_22])).
% 30.12/19.22  tff(c_123998, plain, (r2_hidden(k1_mcart_1('#skF_8'), k1_xboole_0)), inference(resolution, [status(thm)], [c_123939, c_119758])).
% 30.12/19.22  tff(c_124006, plain, $false, inference(negUnitSimplification, [status(thm)], [c_120048, c_123998])).
% 30.12/19.22  tff(c_124007, plain, (k4_tarski(k1_mcart_1('#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(splitRight, [status(thm)], [c_123775])).
% 30.12/19.22  tff(c_124046, plain, (![A_42627, B_42628, C_42629, C_42630]: (k3_mcart_1('#skF_2'(A_42627, B_42628, C_42629), '#skF_3'(A_42627, B_42628, C_42629), C_42630)=k4_tarski(A_42627, C_42630) | ~r2_hidden(A_42627, k2_zfmisc_1(B_42628, C_42629)))), inference(superposition, [status(thm), theory('equality')], [c_417, c_14])).
% 30.12/19.22  tff(c_124116, plain, (![C_42632, A_42633, B_42634, C_42635]: (C_42632='#skF_7' | k4_tarski(A_42633, C_42632)!='#skF_8' | ~m1_subset_1(C_42632, '#skF_6') | ~m1_subset_1('#skF_3'(A_42633, B_42634, C_42635), '#skF_5') | ~m1_subset_1('#skF_2'(A_42633, B_42634, C_42635), '#skF_4') | ~r2_hidden(A_42633, k2_zfmisc_1(B_42634, C_42635)))), inference(superposition, [status(thm), theory('equality')], [c_124046, c_58])).
% 30.12/19.22  tff(c_124118, plain, (![B_42634, C_42635]: (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_42634, C_42635), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_42634, C_42635), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_42634, C_42635)))), inference(superposition, [status(thm), theory('equality')], [c_124007, c_124116])).
% 30.12/19.22  tff(c_124125, plain, (![B_42634, C_42635]: (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6') | ~m1_subset_1('#skF_3'(k1_mcart_1('#skF_8'), B_42634, C_42635), '#skF_5') | ~m1_subset_1('#skF_2'(k1_mcart_1('#skF_8'), B_42634, C_42635), '#skF_4') | ~r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1(B_42634, C_42635)))), inference(negUnitSimplification, [status(thm)], [c_119823, c_124118])).
% 30.12/19.22  tff(c_124345, plain, (~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitLeft, [status(thm)], [c_124125])).
% 30.12/19.22  tff(c_124361, plain, (![A_42649, C_42650, A_42651, B_42652]: (r2_hidden(k2_mcart_1(A_42649), C_42650) | ~m1_subset_1(A_42649, k3_zfmisc_1(A_42651, B_42652, C_42650)))), inference(resolution, [status(thm)], [c_119744, c_199])).
% 30.12/19.22  tff(c_124550, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_60, c_124361])).
% 30.12/19.22  tff(c_124553, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(resolution, [status(thm)], [c_124550, c_10])).
% 30.12/19.22  tff(c_124557, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124345, c_124553])).
% 30.12/19.22  tff(c_124559, plain, (m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_124125])).
% 30.12/19.22  tff(c_120165, plain, (![A_42458, B_42459, C_42460]: (r2_hidden(k1_mcart_1(A_42458), B_42459) | ~m1_subset_1(A_42458, k2_zfmisc_1(B_42459, C_42460)))), inference(resolution, [status(thm)], [c_119744, c_22])).
% 30.12/19.22  tff(c_131542, plain, (![A_43051, A_43052, B_43053, C_43054]: (r2_hidden(k1_mcart_1(A_43051), k2_zfmisc_1(A_43052, B_43053)) | ~m1_subset_1(A_43051, k3_zfmisc_1(A_43052, B_43053, C_43054)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_120165])).
% 30.12/19.22  tff(c_131881, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_60, c_131542])).
% 30.12/19.22  tff(c_131898, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_4')), inference(resolution, [status(thm)], [c_131881, c_22])).
% 30.12/19.22  tff(c_131912, plain, (r2_hidden(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_119839, c_131898])).
% 30.12/19.22  tff(c_132039, plain, (m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4')), inference(resolution, [status(thm)], [c_131912, c_10])).
% 30.12/19.22  tff(c_131900, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_131881, c_20])).
% 30.12/19.22  tff(c_131914, plain, (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_119999, c_131900])).
% 30.12/19.22  tff(c_132035, plain, (m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5')), inference(resolution, [status(thm)], [c_131914, c_10])).
% 30.12/19.22  tff(c_131915, plain, (m1_subset_1(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_131881, c_10])).
% 30.12/19.22  tff(c_131933, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')), k2_mcart_1(k1_mcart_1('#skF_8')))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_131915, c_28])).
% 30.12/19.22  tff(c_131945, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119839, c_119999, c_131933])).
% 30.12/19.22  tff(c_131946, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_131945])).
% 30.12/19.22  tff(c_132640, plain, (![C_43064]: (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), C_43064)=k4_tarski(k1_mcart_1('#skF_8'), C_43064))), inference(superposition, [status(thm), theory('equality')], [c_131946, c_14])).
% 30.12/19.22  tff(c_132695, plain, (![C_43064]: (C_43064='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_43064)!='#skF_8' | ~m1_subset_1(C_43064, '#skF_6') | ~m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_132640, c_58])).
% 30.12/19.22  tff(c_133072, plain, (![C_43077]: (C_43077='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_43077)!='#skF_8' | ~m1_subset_1(C_43077, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_132039, c_132035, c_132695])).
% 30.12/19.22  tff(c_133075, plain, (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_124007, c_133072])).
% 30.12/19.22  tff(c_133078, plain, (k2_mcart_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_124559, c_133075])).
% 30.12/19.22  tff(c_133080, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119823, c_133078])).
% 30.12/19.22  tff(c_133087, plain, (![C_43078]: (r2_hidden(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), C_43078))), inference(splitRight, [status(thm)], [c_120009])).
% 30.12/19.22  tff(c_133103, plain, (![C_43078]: (m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), C_43078))), inference(resolution, [status(thm)], [c_133087, c_10])).
% 30.12/19.22  tff(c_157546, plain, (m1_subset_1(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_157512, c_10])).
% 30.12/19.22  tff(c_157564, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_8')), k2_mcart_1(k1_mcart_1('#skF_8')))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_157546, c_28])).
% 30.12/19.22  tff(c_157576, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_119839, c_119999, c_157564])).
% 30.12/19.22  tff(c_157577, plain, (k4_tarski(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'))=k1_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_56, c_54, c_157576])).
% 30.12/19.22  tff(c_158136, plain, (![C_72044]: (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), C_72044)=k4_tarski(k1_mcart_1('#skF_8'), C_72044))), inference(superposition, [status(thm), theory('equality')], [c_157577, c_14])).
% 30.12/19.22  tff(c_158184, plain, (![C_72044]: (C_72044='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_72044)!='#skF_8' | ~m1_subset_1(C_72044, '#skF_6') | ~m1_subset_1(k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_5') | ~m1_subset_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_158136, c_58])).
% 30.12/19.22  tff(c_158746, plain, (![C_72062]: (C_72062='#skF_7' | k4_tarski(k1_mcart_1('#skF_8'), C_72062)!='#skF_8' | ~m1_subset_1(C_72062, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_157703, c_133103, c_158184])).
% 30.12/19.22  tff(c_158749, plain, (k2_mcart_1('#skF_8')='#skF_7' | ~m1_subset_1(k2_mcart_1('#skF_8'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_149617, c_158746])).
% 30.12/19.22  tff(c_158752, plain, (k2_mcart_1('#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_150511, c_158749])).
% 30.12/19.22  tff(c_158754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_119823, c_158752])).
% 30.12/19.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 30.12/19.22  
% 30.12/19.22  Inference rules
% 30.12/19.22  ----------------------
% 30.12/19.22  #Ref     : 0
% 30.12/19.22  #Sup     : 42238
% 30.12/19.22  #Fact    : 0
% 30.12/19.22  #Define  : 0
% 30.12/19.22  #Split   : 29
% 30.12/19.22  #Chain   : 0
% 30.12/19.22  #Close   : 0
% 30.12/19.22  
% 30.12/19.22  Ordering : KBO
% 30.12/19.22  
% 30.12/19.22  Simplification rules
% 30.12/19.22  ----------------------
% 30.12/19.22  #Subsume      : 4196
% 30.12/19.22  #Demod        : 20606
% 30.12/19.22  #Tautology    : 16994
% 30.12/19.22  #SimpNegUnit  : 218
% 30.12/19.22  #BackRed      : 47
% 30.12/19.22  
% 30.12/19.22  #Partial instantiations: 7144
% 30.12/19.22  #Strategies tried      : 1
% 30.12/19.22  
% 30.12/19.22  Timing (in seconds)
% 30.12/19.22  ----------------------
% 30.12/19.22  Preprocessing        : 0.35
% 30.12/19.22  Parsing              : 0.19
% 30.12/19.22  CNF conversion       : 0.03
% 30.12/19.22  Main loop            : 17.96
% 30.12/19.22  Inferencing          : 3.57
% 30.12/19.22  Reduction            : 6.79
% 30.12/19.22  Demodulation         : 5.34
% 30.12/19.22  BG Simplification    : 0.44
% 30.12/19.22  Subsumption          : 5.97
% 30.12/19.22  Abstraction          : 0.62
% 30.12/19.22  MUC search           : 0.00
% 30.12/19.22  Cooper               : 0.00
% 30.12/19.22  Total                : 18.42
% 30.12/19.22  Index Insertion      : 0.00
% 30.12/19.22  Index Deletion       : 0.00
% 30.12/19.22  Index Matching       : 0.00
% 30.12/19.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
