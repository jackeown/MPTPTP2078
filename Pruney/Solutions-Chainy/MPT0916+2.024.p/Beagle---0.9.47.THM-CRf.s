%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:13 EST 2020

% Result     : Theorem 2.77s
% Output     : CNFRefutation 2.89s
% Verified   : 
% Statistics : Number of formulae       :  156 ( 444 expanded)
%              Number of leaves         :   28 ( 152 expanded)
%              Depth                    :    9
%              Number of atoms          :  242 (1352 expanded)
%              Number of equality atoms :  111 ( 497 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_61,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_47,plain,(
    ! [C_32,B_33,A_34] :
      ( ~ v1_xboole_0(C_32)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(C_32))
      | ~ r2_hidden(A_34,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_34,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_24,c_47])).

tff(c_274,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_26,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_56,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_34,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_26,c_47])).

tff(c_275,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_28,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_55,plain,(
    ! [A_34] :
      ( ~ v1_xboole_0('#skF_1')
      | ~ r2_hidden(A_34,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_28,c_47])).

tff(c_276,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_22,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_314,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_mcart_1(A_121,B_122,C_123,D_124) = k2_mcart_1(D_124)
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_121,B_122,C_123))
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_321,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_314])).

tff(c_322,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_321])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_324,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_2])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_324])).

tff(c_328,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_329,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k5_mcart_1(A_125,B_126,C_127,D_128) = k1_mcart_1(k1_mcart_1(D_128))
      | ~ m1_subset_1(D_128,k3_zfmisc_1(A_125,B_126,C_127))
      | k1_xboole_0 = C_127
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_336,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_329])).

tff(c_344,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_328,c_336])).

tff(c_345,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_344])).

tff(c_349,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_2])).

tff(c_351,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_349])).

tff(c_353,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_344])).

tff(c_20,plain,(
    r2_hidden('#skF_7',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_zfmisc_1(k2_zfmisc_1(A_4,B_5),C_6) = k3_zfmisc_1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_277,plain,(
    ! [A_106,C_107,B_108] :
      ( r2_hidden(k2_mcart_1(A_106),C_107)
      | ~ r2_hidden(A_106,k2_zfmisc_1(B_108,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_280,plain,(
    ! [A_109,C_110,A_111,B_112] :
      ( r2_hidden(k2_mcart_1(A_109),C_110)
      | ~ r2_hidden(A_109,k3_zfmisc_1(A_111,B_112,C_110)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_277])).

tff(c_283,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_280])).

tff(c_327,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_3'
    | k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(splitRight,[status(thm)],[c_321])).

tff(c_337,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_327])).

tff(c_18,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_6')
    | ~ r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5')
    | ~ r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_57,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_58,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_59,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_60,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_55])).

tff(c_96,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k7_mcart_1(A_50,B_51,C_52,D_53) = k2_mcart_1(D_53)
      | ~ m1_subset_1(D_53,k3_zfmisc_1(A_50,B_51,C_52))
      | k1_xboole_0 = C_52
      | k1_xboole_0 = B_51
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_103,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_96])).

tff(c_105,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_107,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_107])).

tff(c_111,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_117,plain,(
    ! [A_54,B_55,C_56,D_57] :
      ( k6_mcart_1(A_54,B_55,C_56,D_57) = k2_mcart_1(k1_mcart_1(D_57))
      | ~ m1_subset_1(D_57,k3_zfmisc_1(A_54,B_55,C_56))
      | k1_xboole_0 = C_56
      | k1_xboole_0 = B_55
      | k1_xboole_0 = A_54 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_123,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_117])).

tff(c_126,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_123])).

tff(c_127,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_126])).

tff(c_131,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_2])).

tff(c_133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_59,c_131])).

tff(c_135,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_126])).

tff(c_136,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( k5_mcart_1(A_58,B_59,C_60,D_61) = k1_mcart_1(k1_mcart_1(D_61))
      | ~ m1_subset_1(D_61,k3_zfmisc_1(A_58,B_59,C_60))
      | k1_xboole_0 = C_60
      | k1_xboole_0 = B_59
      | k1_xboole_0 = A_58 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_142,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_136])).

tff(c_145,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_111,c_142])).

tff(c_152,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_145])).

tff(c_153,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_152])).

tff(c_159,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_2])).

tff(c_161,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_159])).

tff(c_162,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_152])).

tff(c_44,plain,(
    ! [A_29,B_30,C_31] :
      ( r2_hidden(k1_mcart_1(A_29),B_30)
      | ~ r2_hidden(A_29,k2_zfmisc_1(B_30,C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_83,plain,(
    ! [A_46,A_47,B_48,C_49] :
      ( r2_hidden(k1_mcart_1(A_46),k2_zfmisc_1(A_47,B_48))
      | ~ r2_hidden(A_46,k3_zfmisc_1(A_47,B_48,C_49)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_89,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_83])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] :
      ( r2_hidden(k1_mcart_1(A_7),B_8)
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_95,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_89,c_10])).

tff(c_164,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_95])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_164])).

tff(c_167,plain,(
    ! [A_34] : ~ r2_hidden(A_34,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_192,plain,(
    ! [A_74,A_75,B_76,C_77] :
      ( r2_hidden(k1_mcart_1(A_74),k2_zfmisc_1(A_75,B_76))
      | ~ r2_hidden(A_74,k3_zfmisc_1(A_75,B_76,C_77)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_198,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_192])).

tff(c_202,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_198,c_10])).

tff(c_207,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_167,c_202])).

tff(c_208,plain,(
    ! [A_34] : ~ r2_hidden(A_34,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_242,plain,(
    ! [A_94,A_95,B_96,C_97] :
      ( r2_hidden(k1_mcart_1(A_94),k2_zfmisc_1(A_95,B_96))
      | ~ r2_hidden(A_94,k3_zfmisc_1(A_95,B_96,C_97)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_248,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_242])).

tff(c_8,plain,(
    ! [A_7,C_9,B_8] :
      ( r2_hidden(k2_mcart_1(A_7),C_9)
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_250,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_248,c_8])).

tff(c_256,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_208,c_250])).

tff(c_257,plain,(
    ! [A_34] : ~ r2_hidden(A_34,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_262,plain,(
    ! [A_99,C_100,B_101] :
      ( r2_hidden(k2_mcart_1(A_99),C_100)
      | ~ r2_hidden(A_99,k2_zfmisc_1(B_101,C_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_265,plain,(
    ! [A_102,C_103,A_104,B_105] :
      ( r2_hidden(k2_mcart_1(A_102),C_103)
      | ~ r2_hidden(A_102,k3_zfmisc_1(A_104,B_105,C_103)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_262])).

tff(c_267,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_265])).

tff(c_271,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_257,c_267])).

tff(c_272,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5')
    | ~ r2_hidden(k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_299,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_272])).

tff(c_338,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_299])).

tff(c_341,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_283,c_338])).

tff(c_342,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_327])).

tff(c_354,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_353,c_342])).

tff(c_359,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_354,c_2])).

tff(c_361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_359])).

tff(c_362,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_272])).

tff(c_364,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( k7_mcart_1(A_129,B_130,C_131,D_132) = k2_mcart_1(D_132)
      | ~ m1_subset_1(D_132,k3_zfmisc_1(A_129,B_130,C_131))
      | k1_xboole_0 = C_131
      | k1_xboole_0 = B_130
      | k1_xboole_0 = A_129 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_371,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_364])).

tff(c_385,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_371])).

tff(c_387,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_385,c_2])).

tff(c_389,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_276,c_387])).

tff(c_391,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_371])).

tff(c_399,plain,(
    ! [A_137,B_138,C_139,D_140] :
      ( k5_mcart_1(A_137,B_138,C_139,D_140) = k1_mcart_1(k1_mcart_1(D_140))
      | ~ m1_subset_1(D_140,k3_zfmisc_1(A_137,B_138,C_139))
      | k1_xboole_0 = C_139
      | k1_xboole_0 = B_138
      | k1_xboole_0 = A_137 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_405,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_399])).

tff(c_408,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_405])).

tff(c_410,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_408])).

tff(c_414,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_410,c_2])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_275,c_414])).

tff(c_418,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_408])).

tff(c_426,plain,(
    ! [A_141,B_142,C_143,D_144] :
      ( k6_mcart_1(A_141,B_142,C_143,D_144) = k2_mcart_1(k1_mcart_1(D_144))
      | ~ m1_subset_1(D_144,k3_zfmisc_1(A_141,B_142,C_143))
      | k1_xboole_0 = C_143
      | k1_xboole_0 = B_142
      | k1_xboole_0 = A_141 ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_432,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_426])).

tff(c_435,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7')
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_391,c_418,c_432])).

tff(c_436,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_435])).

tff(c_442,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_2])).

tff(c_444,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_274,c_442])).

tff(c_445,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7') ),
    inference(splitRight,[status(thm)],[c_435])).

tff(c_372,plain,(
    ! [A_133,A_134,B_135,C_136] :
      ( r2_hidden(k1_mcart_1(A_133),k2_zfmisc_1(A_134,B_135))
      | ~ r2_hidden(A_133,k3_zfmisc_1(A_134,B_135,C_136)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_378,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_372])).

tff(c_383,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_378,c_8])).

tff(c_447,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_383])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_362,c_447])).

tff(c_450,plain,(
    ! [A_34] : ~ r2_hidden(A_34,'#skF_4') ),
    inference(splitRight,[status(thm)],[c_55])).

tff(c_273,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_7'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_453,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_450,c_273])).

tff(c_454,plain,(
    ! [A_34] : ~ r2_hidden(A_34,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_480,plain,(
    ! [A_157,A_158,B_159,C_160] :
      ( r2_hidden(k1_mcart_1(A_157),k2_zfmisc_1(A_158,B_159))
      | ~ r2_hidden(A_157,k3_zfmisc_1(A_158,B_159,C_160)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_44])).

tff(c_486,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_20,c_480])).

tff(c_488,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_486,c_8])).

tff(c_494,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_454,c_488])).

tff(c_495,plain,(
    ! [A_34] : ~ r2_hidden(A_34,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_500,plain,(
    ! [A_162,C_163,B_164] :
      ( r2_hidden(k2_mcart_1(A_162),C_163)
      | ~ r2_hidden(A_162,k2_zfmisc_1(B_164,C_163)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_503,plain,(
    ! [A_165,C_166,A_167,B_168] :
      ( r2_hidden(k2_mcart_1(A_165),C_166)
      | ~ r2_hidden(A_165,k3_zfmisc_1(A_167,B_168,C_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_500])).

tff(c_505,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_20,c_503])).

tff(c_509,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_495,c_505])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:47:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.77/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.47  
% 2.89/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.48  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.89/1.48  
% 2.89/1.48  %Foreground sorts:
% 2.89/1.48  
% 2.89/1.48  
% 2.89/1.48  %Background operators:
% 2.89/1.48  
% 2.89/1.48  
% 2.89/1.48  %Foreground operators:
% 2.89/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.89/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.89/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.89/1.48  tff('#skF_7', type, '#skF_7': $i).
% 2.89/1.48  tff('#skF_5', type, '#skF_5': $i).
% 2.89/1.48  tff('#skF_6', type, '#skF_6': $i).
% 2.89/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.89/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.89/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.89/1.48  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.89/1.48  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.89/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.89/1.48  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.89/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.89/1.48  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.89/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.89/1.48  tff('#skF_4', type, '#skF_4': $i).
% 2.89/1.48  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.89/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.89/1.48  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.89/1.48  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.89/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.89/1.48  
% 2.89/1.50  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_mcart_1)).
% 2.89/1.50  tff(f_33, axiom, (![A, B, C]: ~((r2_hidden(A, B) & m1_subset_1(B, k1_zfmisc_1(C))) & v1_xboole_0(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_subset)).
% 2.89/1.50  tff(f_61, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.89/1.50  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.89/1.50  tff(f_35, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 2.89/1.50  tff(f_41, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.89/1.50  tff(c_24, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.50  tff(c_47, plain, (![C_32, B_33, A_34]: (~v1_xboole_0(C_32) | ~m1_subset_1(B_33, k1_zfmisc_1(C_32)) | ~r2_hidden(A_34, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.89/1.50  tff(c_54, plain, (![A_34]: (~v1_xboole_0('#skF_3') | ~r2_hidden(A_34, '#skF_6'))), inference(resolution, [status(thm)], [c_24, c_47])).
% 2.89/1.50  tff(c_274, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 2.89/1.50  tff(c_26, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.50  tff(c_56, plain, (![A_34]: (~v1_xboole_0('#skF_2') | ~r2_hidden(A_34, '#skF_5'))), inference(resolution, [status(thm)], [c_26, c_47])).
% 2.89/1.50  tff(c_275, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 2.89/1.50  tff(c_28, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.50  tff(c_55, plain, (![A_34]: (~v1_xboole_0('#skF_1') | ~r2_hidden(A_34, '#skF_4'))), inference(resolution, [status(thm)], [c_28, c_47])).
% 2.89/1.50  tff(c_276, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_55])).
% 2.89/1.50  tff(c_22, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.50  tff(c_314, plain, (![A_121, B_122, C_123, D_124]: (k7_mcart_1(A_121, B_122, C_123, D_124)=k2_mcart_1(D_124) | ~m1_subset_1(D_124, k3_zfmisc_1(A_121, B_122, C_123)) | k1_xboole_0=C_123 | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_321, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_314])).
% 2.89/1.50  tff(c_322, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_321])).
% 2.89/1.50  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.89/1.50  tff(c_324, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_2])).
% 2.89/1.50  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_324])).
% 2.89/1.50  tff(c_328, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_321])).
% 2.89/1.50  tff(c_329, plain, (![A_125, B_126, C_127, D_128]: (k5_mcart_1(A_125, B_126, C_127, D_128)=k1_mcart_1(k1_mcart_1(D_128)) | ~m1_subset_1(D_128, k3_zfmisc_1(A_125, B_126, C_127)) | k1_xboole_0=C_127 | k1_xboole_0=B_126 | k1_xboole_0=A_125)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_336, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_329])).
% 2.89/1.50  tff(c_344, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_328, c_336])).
% 2.89/1.50  tff(c_345, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_344])).
% 2.89/1.50  tff(c_349, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_2])).
% 2.89/1.50  tff(c_351, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_349])).
% 2.89/1.50  tff(c_353, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_344])).
% 2.89/1.50  tff(c_20, plain, (r2_hidden('#skF_7', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.50  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_zfmisc_1(k2_zfmisc_1(A_4, B_5), C_6)=k3_zfmisc_1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.89/1.50  tff(c_277, plain, (![A_106, C_107, B_108]: (r2_hidden(k2_mcart_1(A_106), C_107) | ~r2_hidden(A_106, k2_zfmisc_1(B_108, C_107)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.50  tff(c_280, plain, (![A_109, C_110, A_111, B_112]: (r2_hidden(k2_mcart_1(A_109), C_110) | ~r2_hidden(A_109, k3_zfmisc_1(A_111, B_112, C_110)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_277])).
% 2.89/1.50  tff(c_283, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_280])).
% 2.89/1.50  tff(c_327, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_3' | k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7')), inference(splitRight, [status(thm)], [c_321])).
% 2.89/1.50  tff(c_337, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7')), inference(splitLeft, [status(thm)], [c_327])).
% 2.89/1.50  tff(c_18, plain, (~r2_hidden(k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_6') | ~r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5') | ~r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.89/1.50  tff(c_57, plain, (~r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(splitLeft, [status(thm)], [c_18])).
% 2.89/1.50  tff(c_58, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_54])).
% 2.89/1.50  tff(c_59, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_56])).
% 2.89/1.50  tff(c_60, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_55])).
% 2.89/1.50  tff(c_96, plain, (![A_50, B_51, C_52, D_53]: (k7_mcart_1(A_50, B_51, C_52, D_53)=k2_mcart_1(D_53) | ~m1_subset_1(D_53, k3_zfmisc_1(A_50, B_51, C_52)) | k1_xboole_0=C_52 | k1_xboole_0=B_51 | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_103, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_96])).
% 2.89/1.50  tff(c_105, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_103])).
% 2.89/1.50  tff(c_107, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_105, c_2])).
% 2.89/1.50  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_107])).
% 2.89/1.50  tff(c_111, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_103])).
% 2.89/1.50  tff(c_117, plain, (![A_54, B_55, C_56, D_57]: (k6_mcart_1(A_54, B_55, C_56, D_57)=k2_mcart_1(k1_mcart_1(D_57)) | ~m1_subset_1(D_57, k3_zfmisc_1(A_54, B_55, C_56)) | k1_xboole_0=C_56 | k1_xboole_0=B_55 | k1_xboole_0=A_54)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_123, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_117])).
% 2.89/1.50  tff(c_126, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_111, c_123])).
% 2.89/1.50  tff(c_127, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_126])).
% 2.89/1.50  tff(c_131, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_127, c_2])).
% 2.89/1.50  tff(c_133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_59, c_131])).
% 2.89/1.50  tff(c_135, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_126])).
% 2.89/1.50  tff(c_136, plain, (![A_58, B_59, C_60, D_61]: (k5_mcart_1(A_58, B_59, C_60, D_61)=k1_mcart_1(k1_mcart_1(D_61)) | ~m1_subset_1(D_61, k3_zfmisc_1(A_58, B_59, C_60)) | k1_xboole_0=C_60 | k1_xboole_0=B_59 | k1_xboole_0=A_58)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_142, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_136])).
% 2.89/1.50  tff(c_145, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_111, c_142])).
% 2.89/1.50  tff(c_152, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_135, c_145])).
% 2.89/1.50  tff(c_153, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_152])).
% 2.89/1.50  tff(c_159, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_153, c_2])).
% 2.89/1.50  tff(c_161, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_159])).
% 2.89/1.50  tff(c_162, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_152])).
% 2.89/1.50  tff(c_44, plain, (![A_29, B_30, C_31]: (r2_hidden(k1_mcart_1(A_29), B_30) | ~r2_hidden(A_29, k2_zfmisc_1(B_30, C_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.50  tff(c_83, plain, (![A_46, A_47, B_48, C_49]: (r2_hidden(k1_mcart_1(A_46), k2_zfmisc_1(A_47, B_48)) | ~r2_hidden(A_46, k3_zfmisc_1(A_47, B_48, C_49)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 2.89/1.50  tff(c_89, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_83])).
% 2.89/1.50  tff(c_10, plain, (![A_7, B_8, C_9]: (r2_hidden(k1_mcart_1(A_7), B_8) | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.50  tff(c_95, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_89, c_10])).
% 2.89/1.50  tff(c_164, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_162, c_95])).
% 2.89/1.50  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_164])).
% 2.89/1.50  tff(c_167, plain, (![A_34]: (~r2_hidden(A_34, '#skF_4'))), inference(splitRight, [status(thm)], [c_55])).
% 2.89/1.50  tff(c_192, plain, (![A_74, A_75, B_76, C_77]: (r2_hidden(k1_mcart_1(A_74), k2_zfmisc_1(A_75, B_76)) | ~r2_hidden(A_74, k3_zfmisc_1(A_75, B_76, C_77)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 2.89/1.50  tff(c_198, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_192])).
% 2.89/1.50  tff(c_202, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_198, c_10])).
% 2.89/1.50  tff(c_207, plain, $false, inference(negUnitSimplification, [status(thm)], [c_167, c_202])).
% 2.89/1.50  tff(c_208, plain, (![A_34]: (~r2_hidden(A_34, '#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 2.89/1.50  tff(c_242, plain, (![A_94, A_95, B_96, C_97]: (r2_hidden(k1_mcart_1(A_94), k2_zfmisc_1(A_95, B_96)) | ~r2_hidden(A_94, k3_zfmisc_1(A_95, B_96, C_97)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 2.89/1.50  tff(c_248, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_242])).
% 2.89/1.50  tff(c_8, plain, (![A_7, C_9, B_8]: (r2_hidden(k2_mcart_1(A_7), C_9) | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.50  tff(c_250, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_5')), inference(resolution, [status(thm)], [c_248, c_8])).
% 2.89/1.50  tff(c_256, plain, $false, inference(negUnitSimplification, [status(thm)], [c_208, c_250])).
% 2.89/1.50  tff(c_257, plain, (![A_34]: (~r2_hidden(A_34, '#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 2.89/1.50  tff(c_262, plain, (![A_99, C_100, B_101]: (r2_hidden(k2_mcart_1(A_99), C_100) | ~r2_hidden(A_99, k2_zfmisc_1(B_101, C_100)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.50  tff(c_265, plain, (![A_102, C_103, A_104, B_105]: (r2_hidden(k2_mcart_1(A_102), C_103) | ~r2_hidden(A_102, k3_zfmisc_1(A_104, B_105, C_103)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_262])).
% 2.89/1.50  tff(c_267, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_265])).
% 2.89/1.50  tff(c_271, plain, $false, inference(negUnitSimplification, [status(thm)], [c_257, c_267])).
% 2.89/1.50  tff(c_272, plain, (~r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5') | ~r2_hidden(k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_6')), inference(splitRight, [status(thm)], [c_18])).
% 2.89/1.50  tff(c_299, plain, (~r2_hidden(k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_6')), inference(splitLeft, [status(thm)], [c_272])).
% 2.89/1.50  tff(c_338, plain, (~r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_337, c_299])).
% 2.89/1.50  tff(c_341, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_283, c_338])).
% 2.89/1.50  tff(c_342, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_327])).
% 2.89/1.50  tff(c_354, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_353, c_342])).
% 2.89/1.50  tff(c_359, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_354, c_2])).
% 2.89/1.50  tff(c_361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_359])).
% 2.89/1.50  tff(c_362, plain, (~r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5')), inference(splitRight, [status(thm)], [c_272])).
% 2.89/1.50  tff(c_364, plain, (![A_129, B_130, C_131, D_132]: (k7_mcart_1(A_129, B_130, C_131, D_132)=k2_mcart_1(D_132) | ~m1_subset_1(D_132, k3_zfmisc_1(A_129, B_130, C_131)) | k1_xboole_0=C_131 | k1_xboole_0=B_130 | k1_xboole_0=A_129)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_371, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_364])).
% 2.89/1.50  tff(c_385, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_371])).
% 2.89/1.50  tff(c_387, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_385, c_2])).
% 2.89/1.50  tff(c_389, plain, $false, inference(negUnitSimplification, [status(thm)], [c_276, c_387])).
% 2.89/1.50  tff(c_391, plain, (k1_xboole_0!='#skF_1'), inference(splitRight, [status(thm)], [c_371])).
% 2.89/1.50  tff(c_399, plain, (![A_137, B_138, C_139, D_140]: (k5_mcart_1(A_137, B_138, C_139, D_140)=k1_mcart_1(k1_mcart_1(D_140)) | ~m1_subset_1(D_140, k3_zfmisc_1(A_137, B_138, C_139)) | k1_xboole_0=C_139 | k1_xboole_0=B_138 | k1_xboole_0=A_137)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_405, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_399])).
% 2.89/1.50  tff(c_408, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_391, c_405])).
% 2.89/1.50  tff(c_410, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_408])).
% 2.89/1.50  tff(c_414, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_410, c_2])).
% 2.89/1.50  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_275, c_414])).
% 2.89/1.50  tff(c_418, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_408])).
% 2.89/1.50  tff(c_426, plain, (![A_141, B_142, C_143, D_144]: (k6_mcart_1(A_141, B_142, C_143, D_144)=k2_mcart_1(k1_mcart_1(D_144)) | ~m1_subset_1(D_144, k3_zfmisc_1(A_141, B_142, C_143)) | k1_xboole_0=C_143 | k1_xboole_0=B_142 | k1_xboole_0=A_141)), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.89/1.50  tff(c_432, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_22, c_426])).
% 2.89/1.50  tff(c_435, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7') | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_391, c_418, c_432])).
% 2.89/1.50  tff(c_436, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_435])).
% 2.89/1.50  tff(c_442, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_436, c_2])).
% 2.89/1.50  tff(c_444, plain, $false, inference(negUnitSimplification, [status(thm)], [c_274, c_442])).
% 2.89/1.50  tff(c_445, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7')), inference(splitRight, [status(thm)], [c_435])).
% 2.89/1.50  tff(c_372, plain, (![A_133, A_134, B_135, C_136]: (r2_hidden(k1_mcart_1(A_133), k2_zfmisc_1(A_134, B_135)) | ~r2_hidden(A_133, k3_zfmisc_1(A_134, B_135, C_136)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 2.89/1.50  tff(c_378, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_372])).
% 2.89/1.50  tff(c_383, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_5')), inference(resolution, [status(thm)], [c_378, c_8])).
% 2.89/1.50  tff(c_447, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_445, c_383])).
% 2.89/1.50  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_362, c_447])).
% 2.89/1.50  tff(c_450, plain, (![A_34]: (~r2_hidden(A_34, '#skF_4'))), inference(splitRight, [status(thm)], [c_55])).
% 2.89/1.50  tff(c_273, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_7'), '#skF_4')), inference(splitRight, [status(thm)], [c_18])).
% 2.89/1.50  tff(c_453, plain, $false, inference(negUnitSimplification, [status(thm)], [c_450, c_273])).
% 2.89/1.50  tff(c_454, plain, (![A_34]: (~r2_hidden(A_34, '#skF_5'))), inference(splitRight, [status(thm)], [c_56])).
% 2.89/1.50  tff(c_480, plain, (![A_157, A_158, B_159, C_160]: (r2_hidden(k1_mcart_1(A_157), k2_zfmisc_1(A_158, B_159)) | ~r2_hidden(A_157, k3_zfmisc_1(A_158, B_159, C_160)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_44])).
% 2.89/1.50  tff(c_486, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_20, c_480])).
% 2.89/1.50  tff(c_488, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_5')), inference(resolution, [status(thm)], [c_486, c_8])).
% 2.89/1.50  tff(c_494, plain, $false, inference(negUnitSimplification, [status(thm)], [c_454, c_488])).
% 2.89/1.50  tff(c_495, plain, (![A_34]: (~r2_hidden(A_34, '#skF_6'))), inference(splitRight, [status(thm)], [c_54])).
% 2.89/1.50  tff(c_500, plain, (![A_162, C_163, B_164]: (r2_hidden(k2_mcart_1(A_162), C_163) | ~r2_hidden(A_162, k2_zfmisc_1(B_164, C_163)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.89/1.50  tff(c_503, plain, (![A_165, C_166, A_167, B_168]: (r2_hidden(k2_mcart_1(A_165), C_166) | ~r2_hidden(A_165, k3_zfmisc_1(A_167, B_168, C_166)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_500])).
% 2.89/1.50  tff(c_505, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_6')), inference(resolution, [status(thm)], [c_20, c_503])).
% 2.89/1.50  tff(c_509, plain, $false, inference(negUnitSimplification, [status(thm)], [c_495, c_505])).
% 2.89/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.89/1.50  
% 2.89/1.50  Inference rules
% 2.89/1.50  ----------------------
% 2.89/1.50  #Ref     : 0
% 2.89/1.50  #Sup     : 92
% 2.89/1.50  #Fact    : 0
% 2.89/1.50  #Define  : 0
% 2.89/1.50  #Split   : 27
% 2.89/1.50  #Chain   : 0
% 2.89/1.50  #Close   : 0
% 2.89/1.50  
% 2.89/1.50  Ordering : KBO
% 2.89/1.50  
% 2.89/1.50  Simplification rules
% 2.89/1.50  ----------------------
% 2.89/1.50  #Subsume      : 13
% 2.89/1.50  #Demod        : 97
% 2.89/1.50  #Tautology    : 30
% 2.89/1.50  #SimpNegUnit  : 24
% 2.89/1.50  #BackRed      : 42
% 2.89/1.50  
% 2.89/1.50  #Partial instantiations: 0
% 2.89/1.50  #Strategies tried      : 1
% 2.89/1.50  
% 2.89/1.50  Timing (in seconds)
% 2.89/1.50  ----------------------
% 2.89/1.51  Preprocessing        : 0.32
% 2.89/1.51  Parsing              : 0.17
% 2.89/1.51  CNF conversion       : 0.02
% 2.89/1.51  Main loop            : 0.33
% 2.89/1.51  Inferencing          : 0.12
% 2.89/1.51  Reduction            : 0.11
% 2.89/1.51  Demodulation         : 0.07
% 2.89/1.51  BG Simplification    : 0.02
% 2.89/1.51  Subsumption          : 0.04
% 2.89/1.51  Abstraction          : 0.02
% 2.89/1.51  MUC search           : 0.00
% 2.89/1.51  Cooper               : 0.00
% 2.89/1.51  Total                : 0.70
% 2.89/1.51  Index Insertion      : 0.00
% 2.89/1.51  Index Deletion       : 0.00
% 2.89/1.51  Index Matching       : 0.00
% 2.89/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
