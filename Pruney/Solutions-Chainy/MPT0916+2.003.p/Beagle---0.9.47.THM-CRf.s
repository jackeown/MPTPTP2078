%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:09 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :  190 ( 531 expanded)
%              Number of leaves         :   33 ( 181 expanded)
%              Depth                    :    9
%              Number of atoms          :  287 (1435 expanded)
%              Number of equality atoms :   96 ( 435 expanded)
%              Maximal formula depth    :   16 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_107,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(c_40,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_872,plain,(
    ! [B_218,A_219] :
      ( v1_xboole_0(B_218)
      | ~ m1_subset_1(B_218,k1_zfmisc_1(A_219))
      | ~ v1_xboole_0(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_882,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_872])).

tff(c_887,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_882])).

tff(c_42,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_883,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_872])).

tff(c_888,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_883])).

tff(c_36,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_913,plain,(
    ! [A_227,B_228,C_229] : k2_zfmisc_1(k2_zfmisc_1(A_227,B_228),C_229) = k3_zfmisc_1(A_227,B_228,C_229) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_16,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(k2_mcart_1(A_16),C_18)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_941,plain,(
    ! [A_233,C_234,A_235,B_236] :
      ( r2_hidden(k2_mcart_1(A_233),C_234)
      | ~ r2_hidden(A_233,k3_zfmisc_1(A_235,B_236,C_234)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_913,c_16])).

tff(c_952,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_941])).

tff(c_72,plain,(
    ! [B_48,A_49] :
      ( v1_xboole_0(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_82,plain,
    ( v1_xboole_0('#skF_7')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_72])).

tff(c_85,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_34,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_56,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_83,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_72])).

tff(c_86,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_83])).

tff(c_44,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_84,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_72])).

tff(c_87,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_84])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_389,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( k7_mcart_1(A_121,B_122,C_123,D_124) = k2_mcart_1(D_124)
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_121,B_122,C_123))
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_396,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_389])).

tff(c_413,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_396])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_57,plain,(
    ! [A_46] :
      ( v1_xboole_0(A_46)
      | r2_hidden('#skF_1'(A_46),A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [B_12,A_11] :
      ( ~ r1_tarski(B_12,A_11)
      | ~ r2_hidden(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_66,plain,(
    ! [A_47] :
      ( ~ r1_tarski(A_47,'#skF_1'(A_47))
      | v1_xboole_0(A_47) ) ),
    inference(resolution,[status(thm)],[c_57,c_12])).

tff(c_71,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_66])).

tff(c_418,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_413,c_71])).

tff(c_421,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_418])).

tff(c_423,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_396])).

tff(c_425,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k5_mcart_1(A_125,B_126,C_127,D_128) = k1_mcart_1(k1_mcart_1(D_128))
      | ~ m1_subset_1(D_128,k3_zfmisc_1(A_125,B_126,C_127))
      | k1_xboole_0 = C_127
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_125 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_431,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_425])).

tff(c_434,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_423,c_431])).

tff(c_439,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_434])).

tff(c_446,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_439,c_71])).

tff(c_449,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_446])).

tff(c_450,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_434])).

tff(c_452,plain,(
    k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15] : k2_zfmisc_1(k2_zfmisc_1(A_13,B_14),C_15) = k3_zfmisc_1(A_13,B_14,C_15) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,(
    ! [A_60,B_61,C_62] :
      ( r2_hidden(k1_mcart_1(A_60),B_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_61,C_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_349,plain,(
    ! [A_117,A_118,B_119,C_120] :
      ( r2_hidden(k1_mcart_1(A_117),k2_zfmisc_1(A_118,B_119))
      | ~ r2_hidden(A_117,k3_zfmisc_1(A_118,B_119,C_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_374,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_349])).

tff(c_18,plain,(
    ! [A_16,B_17,C_18] :
      ( r2_hidden(k1_mcart_1(A_16),B_17)
      | ~ r2_hidden(A_16,k2_zfmisc_1(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_385,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')),'#skF_5') ),
    inference(resolution,[status(thm)],[c_374,c_18])).

tff(c_454,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_385])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_454])).

tff(c_457,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_466,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_71])).

tff(c_469,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_466])).

tff(c_470,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_84])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_492,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden(k1_mcart_1(A_133),B_134)
      | ~ r2_hidden(A_133,k2_zfmisc_1(B_134,C_135)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_554,plain,(
    ! [B_152,C_153] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_152,C_153))),B_152)
      | v1_xboole_0(k2_zfmisc_1(B_152,C_153)) ) ),
    inference(resolution,[status(thm)],[c_4,c_492])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_579,plain,(
    ! [B_152,C_153] :
      ( ~ v1_xboole_0(B_152)
      | v1_xboole_0(k2_zfmisc_1(B_152,C_153)) ) ),
    inference(resolution,[status(thm)],[c_554,c_2])).

tff(c_581,plain,(
    ! [B_154,C_155] :
      ( ~ v1_xboole_0(B_154)
      | v1_xboole_0(k2_zfmisc_1(B_154,C_155)) ) ),
    inference(resolution,[status(thm)],[c_554,c_2])).

tff(c_585,plain,(
    ! [A_156,B_157,C_158] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_156,B_157))
      | v1_xboole_0(k3_zfmisc_1(A_156,B_157,C_158)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_581])).

tff(c_50,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_36,c_2])).

tff(c_589,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_585,c_50])).

tff(c_592,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_579,c_589])).

tff(c_596,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_592])).

tff(c_597,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_83])).

tff(c_645,plain,(
    ! [A_169,C_170,B_171] :
      ( r2_hidden(k2_mcart_1(A_169),C_170)
      | ~ r2_hidden(A_169,k2_zfmisc_1(B_171,C_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_722,plain,(
    ! [B_189,C_190] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_189,C_190))),C_190)
      | v1_xboole_0(k2_zfmisc_1(B_189,C_190)) ) ),
    inference(resolution,[status(thm)],[c_4,c_645])).

tff(c_747,plain,(
    ! [C_191,B_192] :
      ( ~ v1_xboole_0(C_191)
      | v1_xboole_0(k2_zfmisc_1(B_192,C_191)) ) ),
    inference(resolution,[status(thm)],[c_722,c_2])).

tff(c_634,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden(k1_mcart_1(A_166),B_167)
      | ~ r2_hidden(A_166,k2_zfmisc_1(B_167,C_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_682,plain,(
    ! [B_182,C_183] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_182,C_183))),B_182)
      | v1_xboole_0(k2_zfmisc_1(B_182,C_183)) ) ),
    inference(resolution,[status(thm)],[c_4,c_634])).

tff(c_709,plain,(
    ! [B_184,C_185] :
      ( ~ v1_xboole_0(B_184)
      | v1_xboole_0(k2_zfmisc_1(B_184,C_185)) ) ),
    inference(resolution,[status(thm)],[c_682,c_2])).

tff(c_713,plain,(
    ! [A_186,B_187,C_188] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_186,B_187))
      | v1_xboole_0(k3_zfmisc_1(A_186,B_187,C_188)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_709])).

tff(c_717,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_713,c_50])).

tff(c_750,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_747,c_717])).

tff(c_757,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_597,c_750])).

tff(c_758,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_796,plain,(
    ! [A_200,C_201,B_202] :
      ( r2_hidden(k2_mcart_1(A_200),C_201)
      | ~ r2_hidden(A_200,k2_zfmisc_1(B_202,C_201)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_824,plain,(
    ! [A_212,C_213,A_214,B_215] :
      ( r2_hidden(k2_mcart_1(A_212),C_213)
      | ~ r2_hidden(A_212,k3_zfmisc_1(A_214,B_215,C_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_796])).

tff(c_835,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_824])).

tff(c_841,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_835,c_2])).

tff(c_846,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_758,c_841])).

tff(c_848,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_871,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_848,c_2])).

tff(c_881,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_872])).

tff(c_886,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_871,c_881])).

tff(c_1199,plain,(
    ! [A_291,B_292,C_293,D_294] :
      ( k7_mcart_1(A_291,B_292,C_293,D_294) = k2_mcart_1(D_294)
      | ~ m1_subset_1(D_294,k3_zfmisc_1(A_291,B_292,C_293))
      | k1_xboole_0 = C_293
      | k1_xboole_0 = B_292
      | k1_xboole_0 = A_291 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1206,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_1199])).

tff(c_1215,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1206])).

tff(c_849,plain,(
    ! [A_216] :
      ( v1_xboole_0(A_216)
      | r2_hidden('#skF_1'(A_216),A_216) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_858,plain,(
    ! [A_217] :
      ( ~ r1_tarski(A_217,'#skF_1'(A_217))
      | v1_xboole_0(A_217) ) ),
    inference(resolution,[status(thm)],[c_849,c_12])).

tff(c_863,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_858])).

tff(c_1220,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1215,c_863])).

tff(c_1223,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_1220])).

tff(c_1224,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_4'
    | k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_1226,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1224])).

tff(c_847,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_961,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_847])).

tff(c_1228,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1226,c_961])).

tff(c_1231,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_952,c_1228])).

tff(c_1232,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1224])).

tff(c_1244,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1232])).

tff(c_1251,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1244,c_863])).

tff(c_1254,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_1251])).

tff(c_1256,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_1225,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1206])).

tff(c_1234,plain,(
    ! [A_295,B_296,C_297,D_298] :
      ( k5_mcart_1(A_295,B_296,C_297,D_298) = k1_mcart_1(k1_mcart_1(D_298))
      | ~ m1_subset_1(D_298,k3_zfmisc_1(A_295,B_296,C_297))
      | k1_xboole_0 = C_297
      | k1_xboole_0 = B_296
      | k1_xboole_0 = A_295 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1240,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_1234])).

tff(c_1243,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1225,c_1240])).

tff(c_1257,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_8')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_1256,c_1243])).

tff(c_1258,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1257])).

tff(c_1266,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1258,c_863])).

tff(c_1269,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_887,c_1266])).

tff(c_1271,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1257])).

tff(c_1255,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1232])).

tff(c_1272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1271,c_1255])).

tff(c_1273,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_847])).

tff(c_1565,plain,(
    ! [A_362,B_363,C_364,D_365] :
      ( k7_mcart_1(A_362,B_363,C_364,D_365) = k2_mcart_1(D_365)
      | ~ m1_subset_1(D_365,k3_zfmisc_1(A_362,B_363,C_364))
      | k1_xboole_0 = C_364
      | k1_xboole_0 = B_363
      | k1_xboole_0 = A_362 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1572,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_1565])).

tff(c_1573,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1572])).

tff(c_1578,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1573,c_863])).

tff(c_1581,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_886,c_1578])).

tff(c_1583,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1572])).

tff(c_1592,plain,(
    ! [A_366,B_367,C_368,D_369] :
      ( k6_mcart_1(A_366,B_367,C_368,D_369) = k2_mcart_1(k1_mcart_1(D_369))
      | ~ m1_subset_1(D_369,k3_zfmisc_1(A_366,B_367,C_368))
      | k1_xboole_0 = C_368
      | k1_xboole_0 = B_367
      | k1_xboole_0 = A_366 ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1598,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_1592])).

tff(c_1601,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_1583,c_1598])).

tff(c_1602,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1601])).

tff(c_1609,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1602,c_863])).

tff(c_1612,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_888,c_1609])).

tff(c_1613,plain,
    ( k1_xboole_0 = '#skF_4'
    | k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1601])).

tff(c_1615,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1613])).

tff(c_930,plain,(
    ! [A_230,B_231,C_232] :
      ( r2_hidden(k1_mcart_1(A_230),B_231)
      | ~ r2_hidden(A_230,k2_zfmisc_1(B_231,C_232)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1444,plain,(
    ! [A_343,A_344,B_345,C_346] :
      ( r2_hidden(k1_mcart_1(A_343),k2_zfmisc_1(A_344,B_345))
      | ~ r2_hidden(A_343,k3_zfmisc_1(A_344,B_345,C_346)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_930])).

tff(c_1466,plain,(
    r2_hidden(k1_mcart_1('#skF_8'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_36,c_1444])).

tff(c_1478,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')),'#skF_6') ),
    inference(resolution,[status(thm)],[c_1466,c_16])).

tff(c_1617,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1615,c_1478])).

tff(c_1619,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1273,c_1617])).

tff(c_1620,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1613])).

tff(c_1629,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1620,c_863])).

tff(c_1632,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_887,c_1629])).

tff(c_1633,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_883])).

tff(c_1650,plain,(
    ! [A_374,C_375,B_376] :
      ( r2_hidden(k2_mcart_1(A_374),C_375)
      | ~ r2_hidden(A_374,k2_zfmisc_1(B_376,C_375)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1763,plain,(
    ! [B_406,C_407] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_406,C_407))),C_407)
      | v1_xboole_0(k2_zfmisc_1(B_406,C_407)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1650])).

tff(c_1793,plain,(
    ! [C_414,B_415] :
      ( ~ v1_xboole_0(C_414)
      | v1_xboole_0(k2_zfmisc_1(B_415,C_414)) ) ),
    inference(resolution,[status(thm)],[c_1763,c_2])).

tff(c_1681,plain,(
    ! [A_380,B_381,C_382] :
      ( r2_hidden(k1_mcart_1(A_380),B_381)
      | ~ r2_hidden(A_380,k2_zfmisc_1(B_381,C_382)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1723,plain,(
    ! [B_399,C_400] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_399,C_400))),B_399)
      | v1_xboole_0(k2_zfmisc_1(B_399,C_400)) ) ),
    inference(resolution,[status(thm)],[c_4,c_1681])).

tff(c_1750,plain,(
    ! [B_401,C_402] :
      ( ~ v1_xboole_0(B_401)
      | v1_xboole_0(k2_zfmisc_1(B_401,C_402)) ) ),
    inference(resolution,[status(thm)],[c_1723,c_2])).

tff(c_1754,plain,(
    ! [A_403,B_404,C_405] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_403,B_404))
      | v1_xboole_0(k3_zfmisc_1(A_403,B_404,C_405)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1750])).

tff(c_1758,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_1754,c_50])).

tff(c_1796,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_1793,c_1758])).

tff(c_1803,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1633,c_1796])).

tff(c_1804,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_882])).

tff(c_1831,plain,(
    ! [A_423,B_424,C_425] : k2_zfmisc_1(k2_zfmisc_1(A_423,B_424),C_425) = k3_zfmisc_1(A_423,B_424,C_425) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1859,plain,(
    ! [A_429,C_430,A_431,B_432] :
      ( r2_hidden(k2_mcart_1(A_429),C_430)
      | ~ r2_hidden(A_429,k3_zfmisc_1(A_431,B_432,C_430)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1831,c_16])).

tff(c_1870,plain,(
    r2_hidden(k2_mcart_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_36,c_1859])).

tff(c_1876,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_1870,c_2])).

tff(c_1881,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1804,c_1876])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:01:57 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.63  
% 3.76/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.63  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4
% 3.76/1.63  
% 3.76/1.63  %Foreground sorts:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Background operators:
% 3.76/1.63  
% 3.76/1.63  
% 3.76/1.63  %Foreground operators:
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.63  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.76/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.76/1.63  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.76/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.76/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.63  tff('#skF_5', type, '#skF_5': $i).
% 3.76/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.76/1.63  tff('#skF_2', type, '#skF_2': $i).
% 3.76/1.63  tff('#skF_3', type, '#skF_3': $i).
% 3.76/1.63  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.76/1.63  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.76/1.63  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.76/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.76/1.63  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.63  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.76/1.63  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.76/1.63  tff('#skF_4', type, '#skF_4': $i).
% 3.76/1.63  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.76/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.63  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.76/1.63  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.76/1.63  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.76/1.63  
% 3.76/1.66  tff(f_107, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(A)) => (![E]: (m1_subset_1(E, k1_zfmisc_1(B)) => (![F]: (m1_subset_1(F, k1_zfmisc_1(C)) => (![G]: (m1_subset_1(G, k3_zfmisc_1(A, B, C)) => (r2_hidden(G, k3_zfmisc_1(D, E, F)) => ((r2_hidden(k5_mcart_1(A, B, C, G), D) & r2_hidden(k6_mcart_1(A, B, C, G), E)) & r2_hidden(k7_mcart_1(A, B, C, G), F))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_mcart_1)).
% 3.76/1.66  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.76/1.66  tff(f_53, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.76/1.66  tff(f_59, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.76/1.66  tff(f_79, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.76/1.66  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.76/1.66  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 3.76/1.66  tff(f_51, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.76/1.66  tff(c_40, plain, (m1_subset_1('#skF_7', k1_zfmisc_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.76/1.66  tff(c_872, plain, (![B_218, A_219]: (v1_xboole_0(B_218) | ~m1_subset_1(B_218, k1_zfmisc_1(A_219)) | ~v1_xboole_0(A_219))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.76/1.66  tff(c_882, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_872])).
% 3.76/1.66  tff(c_887, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_882])).
% 3.76/1.66  tff(c_42, plain, (m1_subset_1('#skF_6', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.76/1.66  tff(c_883, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_872])).
% 3.76/1.66  tff(c_888, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_883])).
% 3.76/1.66  tff(c_36, plain, (r2_hidden('#skF_8', k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.76/1.66  tff(c_913, plain, (![A_227, B_228, C_229]: (k2_zfmisc_1(k2_zfmisc_1(A_227, B_228), C_229)=k3_zfmisc_1(A_227, B_228, C_229))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.76/1.66  tff(c_16, plain, (![A_16, C_18, B_17]: (r2_hidden(k2_mcart_1(A_16), C_18) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_941, plain, (![A_233, C_234, A_235, B_236]: (r2_hidden(k2_mcart_1(A_233), C_234) | ~r2_hidden(A_233, k3_zfmisc_1(A_235, B_236, C_234)))), inference(superposition, [status(thm), theory('equality')], [c_913, c_16])).
% 3.76/1.66  tff(c_952, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_36, c_941])).
% 3.76/1.66  tff(c_72, plain, (![B_48, A_49]: (v1_xboole_0(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.76/1.66  tff(c_82, plain, (v1_xboole_0('#skF_7') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_40, c_72])).
% 3.76/1.66  tff(c_85, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_82])).
% 3.76/1.66  tff(c_34, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7') | ~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.76/1.66  tff(c_56, plain, (~r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitLeft, [status(thm)], [c_34])).
% 3.76/1.66  tff(c_83, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_42, c_72])).
% 3.76/1.66  tff(c_86, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_83])).
% 3.76/1.66  tff(c_44, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.76/1.66  tff(c_84, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_72])).
% 3.76/1.66  tff(c_87, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_84])).
% 3.76/1.66  tff(c_38, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.76/1.66  tff(c_389, plain, (![A_121, B_122, C_123, D_124]: (k7_mcart_1(A_121, B_122, C_123, D_124)=k2_mcart_1(D_124) | ~m1_subset_1(D_124, k3_zfmisc_1(A_121, B_122, C_123)) | k1_xboole_0=C_123 | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.66  tff(c_396, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_389])).
% 3.76/1.66  tff(c_413, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_396])).
% 3.76/1.66  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.76/1.66  tff(c_57, plain, (![A_46]: (v1_xboole_0(A_46) | r2_hidden('#skF_1'(A_46), A_46))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.66  tff(c_12, plain, (![B_12, A_11]: (~r1_tarski(B_12, A_11) | ~r2_hidden(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.76/1.66  tff(c_66, plain, (![A_47]: (~r1_tarski(A_47, '#skF_1'(A_47)) | v1_xboole_0(A_47))), inference(resolution, [status(thm)], [c_57, c_12])).
% 3.76/1.66  tff(c_71, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_66])).
% 3.76/1.66  tff(c_418, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_413, c_71])).
% 3.76/1.66  tff(c_421, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_418])).
% 3.76/1.66  tff(c_423, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_396])).
% 3.76/1.66  tff(c_425, plain, (![A_125, B_126, C_127, D_128]: (k5_mcart_1(A_125, B_126, C_127, D_128)=k1_mcart_1(k1_mcart_1(D_128)) | ~m1_subset_1(D_128, k3_zfmisc_1(A_125, B_126, C_127)) | k1_xboole_0=C_127 | k1_xboole_0=B_126 | k1_xboole_0=A_125)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.66  tff(c_431, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_425])).
% 3.76/1.66  tff(c_434, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_423, c_431])).
% 3.76/1.66  tff(c_439, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_434])).
% 3.76/1.66  tff(c_446, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_439, c_71])).
% 3.76/1.66  tff(c_449, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_446])).
% 3.76/1.66  tff(c_450, plain, (k1_xboole_0='#skF_4' | k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_434])).
% 3.76/1.66  tff(c_452, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_450])).
% 3.76/1.66  tff(c_14, plain, (![A_13, B_14, C_15]: (k2_zfmisc_1(k2_zfmisc_1(A_13, B_14), C_15)=k3_zfmisc_1(A_13, B_14, C_15))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.76/1.66  tff(c_133, plain, (![A_60, B_61, C_62]: (r2_hidden(k1_mcart_1(A_60), B_61) | ~r2_hidden(A_60, k2_zfmisc_1(B_61, C_62)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_349, plain, (![A_117, A_118, B_119, C_120]: (r2_hidden(k1_mcart_1(A_117), k2_zfmisc_1(A_118, B_119)) | ~r2_hidden(A_117, k3_zfmisc_1(A_118, B_119, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_133])).
% 3.76/1.66  tff(c_374, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_349])).
% 3.76/1.66  tff(c_18, plain, (![A_16, B_17, C_18]: (r2_hidden(k1_mcart_1(A_16), B_17) | ~r2_hidden(A_16, k2_zfmisc_1(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_385, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_8')), '#skF_5')), inference(resolution, [status(thm)], [c_374, c_18])).
% 3.76/1.66  tff(c_454, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_452, c_385])).
% 3.76/1.66  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_454])).
% 3.76/1.66  tff(c_457, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_450])).
% 3.76/1.66  tff(c_466, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_457, c_71])).
% 3.76/1.66  tff(c_469, plain, $false, inference(negUnitSimplification, [status(thm)], [c_85, c_466])).
% 3.76/1.66  tff(c_470, plain, (v1_xboole_0('#skF_5')), inference(splitRight, [status(thm)], [c_84])).
% 3.76/1.66  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.66  tff(c_492, plain, (![A_133, B_134, C_135]: (r2_hidden(k1_mcart_1(A_133), B_134) | ~r2_hidden(A_133, k2_zfmisc_1(B_134, C_135)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_554, plain, (![B_152, C_153]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_152, C_153))), B_152) | v1_xboole_0(k2_zfmisc_1(B_152, C_153)))), inference(resolution, [status(thm)], [c_4, c_492])).
% 3.76/1.66  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.66  tff(c_579, plain, (![B_152, C_153]: (~v1_xboole_0(B_152) | v1_xboole_0(k2_zfmisc_1(B_152, C_153)))), inference(resolution, [status(thm)], [c_554, c_2])).
% 3.76/1.66  tff(c_581, plain, (![B_154, C_155]: (~v1_xboole_0(B_154) | v1_xboole_0(k2_zfmisc_1(B_154, C_155)))), inference(resolution, [status(thm)], [c_554, c_2])).
% 3.76/1.66  tff(c_585, plain, (![A_156, B_157, C_158]: (~v1_xboole_0(k2_zfmisc_1(A_156, B_157)) | v1_xboole_0(k3_zfmisc_1(A_156, B_157, C_158)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_581])).
% 3.76/1.66  tff(c_50, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_5', '#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_36, c_2])).
% 3.76/1.66  tff(c_589, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_585, c_50])).
% 3.76/1.66  tff(c_592, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_579, c_589])).
% 3.76/1.66  tff(c_596, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_470, c_592])).
% 3.76/1.66  tff(c_597, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_83])).
% 3.76/1.66  tff(c_645, plain, (![A_169, C_170, B_171]: (r2_hidden(k2_mcart_1(A_169), C_170) | ~r2_hidden(A_169, k2_zfmisc_1(B_171, C_170)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_722, plain, (![B_189, C_190]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_189, C_190))), C_190) | v1_xboole_0(k2_zfmisc_1(B_189, C_190)))), inference(resolution, [status(thm)], [c_4, c_645])).
% 3.76/1.66  tff(c_747, plain, (![C_191, B_192]: (~v1_xboole_0(C_191) | v1_xboole_0(k2_zfmisc_1(B_192, C_191)))), inference(resolution, [status(thm)], [c_722, c_2])).
% 3.76/1.66  tff(c_634, plain, (![A_166, B_167, C_168]: (r2_hidden(k1_mcart_1(A_166), B_167) | ~r2_hidden(A_166, k2_zfmisc_1(B_167, C_168)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_682, plain, (![B_182, C_183]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_182, C_183))), B_182) | v1_xboole_0(k2_zfmisc_1(B_182, C_183)))), inference(resolution, [status(thm)], [c_4, c_634])).
% 3.76/1.66  tff(c_709, plain, (![B_184, C_185]: (~v1_xboole_0(B_184) | v1_xboole_0(k2_zfmisc_1(B_184, C_185)))), inference(resolution, [status(thm)], [c_682, c_2])).
% 3.76/1.66  tff(c_713, plain, (![A_186, B_187, C_188]: (~v1_xboole_0(k2_zfmisc_1(A_186, B_187)) | v1_xboole_0(k3_zfmisc_1(A_186, B_187, C_188)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_709])).
% 3.76/1.66  tff(c_717, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_713, c_50])).
% 3.76/1.66  tff(c_750, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_747, c_717])).
% 3.76/1.66  tff(c_757, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_597, c_750])).
% 3.76/1.66  tff(c_758, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_82])).
% 3.76/1.66  tff(c_796, plain, (![A_200, C_201, B_202]: (r2_hidden(k2_mcart_1(A_200), C_201) | ~r2_hidden(A_200, k2_zfmisc_1(B_202, C_201)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_824, plain, (![A_212, C_213, A_214, B_215]: (r2_hidden(k2_mcart_1(A_212), C_213) | ~r2_hidden(A_212, k3_zfmisc_1(A_214, B_215, C_213)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_796])).
% 3.76/1.66  tff(c_835, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_36, c_824])).
% 3.76/1.66  tff(c_841, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_835, c_2])).
% 3.76/1.66  tff(c_846, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_758, c_841])).
% 3.76/1.66  tff(c_848, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_5')), inference(splitRight, [status(thm)], [c_34])).
% 3.76/1.66  tff(c_871, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_848, c_2])).
% 3.76/1.66  tff(c_881, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_44, c_872])).
% 3.76/1.66  tff(c_886, plain, (~v1_xboole_0('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_871, c_881])).
% 3.76/1.66  tff(c_1199, plain, (![A_291, B_292, C_293, D_294]: (k7_mcart_1(A_291, B_292, C_293, D_294)=k2_mcart_1(D_294) | ~m1_subset_1(D_294, k3_zfmisc_1(A_291, B_292, C_293)) | k1_xboole_0=C_293 | k1_xboole_0=B_292 | k1_xboole_0=A_291)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.66  tff(c_1206, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_1199])).
% 3.76/1.66  tff(c_1215, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1206])).
% 3.76/1.66  tff(c_849, plain, (![A_216]: (v1_xboole_0(A_216) | r2_hidden('#skF_1'(A_216), A_216))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.76/1.66  tff(c_858, plain, (![A_217]: (~r1_tarski(A_217, '#skF_1'(A_217)) | v1_xboole_0(A_217))), inference(resolution, [status(thm)], [c_849, c_12])).
% 3.76/1.66  tff(c_863, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_858])).
% 3.76/1.66  tff(c_1220, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1215, c_863])).
% 3.76/1.66  tff(c_1223, plain, $false, inference(negUnitSimplification, [status(thm)], [c_886, c_1220])).
% 3.76/1.66  tff(c_1224, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_4' | k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitRight, [status(thm)], [c_1206])).
% 3.76/1.66  tff(c_1226, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8')), inference(splitLeft, [status(thm)], [c_1224])).
% 3.76/1.66  tff(c_847, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6') | ~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitRight, [status(thm)], [c_34])).
% 3.76/1.66  tff(c_961, plain, (~r2_hidden(k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_7')), inference(splitLeft, [status(thm)], [c_847])).
% 3.76/1.66  tff(c_1228, plain, (~r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_1226, c_961])).
% 3.76/1.66  tff(c_1231, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_952, c_1228])).
% 3.76/1.66  tff(c_1232, plain, (k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_1224])).
% 3.76/1.66  tff(c_1244, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1232])).
% 3.76/1.66  tff(c_1251, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1244, c_863])).
% 3.76/1.66  tff(c_1254, plain, $false, inference(negUnitSimplification, [status(thm)], [c_888, c_1251])).
% 3.76/1.66  tff(c_1256, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_1232])).
% 3.76/1.66  tff(c_1225, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1206])).
% 3.76/1.66  tff(c_1234, plain, (![A_295, B_296, C_297, D_298]: (k5_mcart_1(A_295, B_296, C_297, D_298)=k1_mcart_1(k1_mcart_1(D_298)) | ~m1_subset_1(D_298, k3_zfmisc_1(A_295, B_296, C_297)) | k1_xboole_0=C_297 | k1_xboole_0=B_296 | k1_xboole_0=A_295)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.66  tff(c_1240, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_1234])).
% 3.76/1.66  tff(c_1243, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1225, c_1240])).
% 3.76/1.66  tff(c_1257, plain, (k1_mcart_1(k1_mcart_1('#skF_8'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_1256, c_1243])).
% 3.76/1.66  tff(c_1258, plain, (k1_xboole_0='#skF_4'), inference(splitLeft, [status(thm)], [c_1257])).
% 3.76/1.66  tff(c_1266, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1258, c_863])).
% 3.76/1.66  tff(c_1269, plain, $false, inference(negUnitSimplification, [status(thm)], [c_887, c_1266])).
% 3.76/1.66  tff(c_1271, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_1257])).
% 3.76/1.66  tff(c_1255, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1232])).
% 3.76/1.66  tff(c_1272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1271, c_1255])).
% 3.76/1.66  tff(c_1273, plain, (~r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(splitRight, [status(thm)], [c_847])).
% 3.76/1.66  tff(c_1565, plain, (![A_362, B_363, C_364, D_365]: (k7_mcart_1(A_362, B_363, C_364, D_365)=k2_mcart_1(D_365) | ~m1_subset_1(D_365, k3_zfmisc_1(A_362, B_363, C_364)) | k1_xboole_0=C_364 | k1_xboole_0=B_363 | k1_xboole_0=A_362)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.66  tff(c_1572, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_1565])).
% 3.76/1.66  tff(c_1573, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_1572])).
% 3.76/1.66  tff(c_1578, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1573, c_863])).
% 3.76/1.66  tff(c_1581, plain, $false, inference(negUnitSimplification, [status(thm)], [c_886, c_1578])).
% 3.76/1.66  tff(c_1583, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_1572])).
% 3.76/1.66  tff(c_1592, plain, (![A_366, B_367, C_368, D_369]: (k6_mcart_1(A_366, B_367, C_368, D_369)=k2_mcart_1(k1_mcart_1(D_369)) | ~m1_subset_1(D_369, k3_zfmisc_1(A_366, B_367, C_368)) | k1_xboole_0=C_368 | k1_xboole_0=B_367 | k1_xboole_0=A_366)), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.76/1.66  tff(c_1598, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_1592])).
% 3.76/1.66  tff(c_1601, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_1583, c_1598])).
% 3.76/1.66  tff(c_1602, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_1601])).
% 3.76/1.66  tff(c_1609, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1602, c_863])).
% 3.76/1.66  tff(c_1612, plain, $false, inference(negUnitSimplification, [status(thm)], [c_888, c_1609])).
% 3.76/1.66  tff(c_1613, plain, (k1_xboole_0='#skF_4' | k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitRight, [status(thm)], [c_1601])).
% 3.76/1.66  tff(c_1615, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8')), inference(splitLeft, [status(thm)], [c_1613])).
% 3.76/1.66  tff(c_930, plain, (![A_230, B_231, C_232]: (r2_hidden(k1_mcart_1(A_230), B_231) | ~r2_hidden(A_230, k2_zfmisc_1(B_231, C_232)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_1444, plain, (![A_343, A_344, B_345, C_346]: (r2_hidden(k1_mcart_1(A_343), k2_zfmisc_1(A_344, B_345)) | ~r2_hidden(A_343, k3_zfmisc_1(A_344, B_345, C_346)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_930])).
% 3.76/1.66  tff(c_1466, plain, (r2_hidden(k1_mcart_1('#skF_8'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_1444])).
% 3.76/1.66  tff(c_1478, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_8')), '#skF_6')), inference(resolution, [status(thm)], [c_1466, c_16])).
% 3.76/1.66  tff(c_1617, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_8'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_1615, c_1478])).
% 3.76/1.66  tff(c_1619, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1273, c_1617])).
% 3.76/1.66  tff(c_1620, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_1613])).
% 3.76/1.66  tff(c_1629, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1620, c_863])).
% 3.76/1.66  tff(c_1632, plain, $false, inference(negUnitSimplification, [status(thm)], [c_887, c_1629])).
% 3.76/1.66  tff(c_1633, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_883])).
% 3.76/1.66  tff(c_1650, plain, (![A_374, C_375, B_376]: (r2_hidden(k2_mcart_1(A_374), C_375) | ~r2_hidden(A_374, k2_zfmisc_1(B_376, C_375)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_1763, plain, (![B_406, C_407]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_406, C_407))), C_407) | v1_xboole_0(k2_zfmisc_1(B_406, C_407)))), inference(resolution, [status(thm)], [c_4, c_1650])).
% 3.76/1.66  tff(c_1793, plain, (![C_414, B_415]: (~v1_xboole_0(C_414) | v1_xboole_0(k2_zfmisc_1(B_415, C_414)))), inference(resolution, [status(thm)], [c_1763, c_2])).
% 3.76/1.66  tff(c_1681, plain, (![A_380, B_381, C_382]: (r2_hidden(k1_mcart_1(A_380), B_381) | ~r2_hidden(A_380, k2_zfmisc_1(B_381, C_382)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.76/1.66  tff(c_1723, plain, (![B_399, C_400]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_399, C_400))), B_399) | v1_xboole_0(k2_zfmisc_1(B_399, C_400)))), inference(resolution, [status(thm)], [c_4, c_1681])).
% 3.76/1.66  tff(c_1750, plain, (![B_401, C_402]: (~v1_xboole_0(B_401) | v1_xboole_0(k2_zfmisc_1(B_401, C_402)))), inference(resolution, [status(thm)], [c_1723, c_2])).
% 3.76/1.66  tff(c_1754, plain, (![A_403, B_404, C_405]: (~v1_xboole_0(k2_zfmisc_1(A_403, B_404)) | v1_xboole_0(k3_zfmisc_1(A_403, B_404, C_405)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1750])).
% 3.76/1.66  tff(c_1758, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_1754, c_50])).
% 3.76/1.66  tff(c_1796, plain, (~v1_xboole_0('#skF_6')), inference(resolution, [status(thm)], [c_1793, c_1758])).
% 3.76/1.66  tff(c_1803, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1633, c_1796])).
% 3.76/1.66  tff(c_1804, plain, (v1_xboole_0('#skF_7')), inference(splitRight, [status(thm)], [c_882])).
% 3.76/1.66  tff(c_1831, plain, (![A_423, B_424, C_425]: (k2_zfmisc_1(k2_zfmisc_1(A_423, B_424), C_425)=k3_zfmisc_1(A_423, B_424, C_425))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.76/1.66  tff(c_1859, plain, (![A_429, C_430, A_431, B_432]: (r2_hidden(k2_mcart_1(A_429), C_430) | ~r2_hidden(A_429, k3_zfmisc_1(A_431, B_432, C_430)))), inference(superposition, [status(thm), theory('equality')], [c_1831, c_16])).
% 3.76/1.66  tff(c_1870, plain, (r2_hidden(k2_mcart_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_36, c_1859])).
% 3.76/1.66  tff(c_1876, plain, (~v1_xboole_0('#skF_7')), inference(resolution, [status(thm)], [c_1870, c_2])).
% 3.76/1.66  tff(c_1881, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1804, c_1876])).
% 3.76/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.66  
% 3.76/1.66  Inference rules
% 3.76/1.66  ----------------------
% 3.76/1.66  #Ref     : 0
% 3.76/1.66  #Sup     : 399
% 3.76/1.66  #Fact    : 0
% 3.76/1.66  #Define  : 0
% 3.76/1.66  #Split   : 29
% 3.76/1.66  #Chain   : 0
% 3.76/1.66  #Close   : 0
% 3.76/1.66  
% 3.76/1.66  Ordering : KBO
% 3.76/1.66  
% 3.76/1.66  Simplification rules
% 3.76/1.66  ----------------------
% 3.76/1.66  #Subsume      : 31
% 3.76/1.66  #Demod        : 183
% 3.76/1.66  #Tautology    : 59
% 3.76/1.66  #SimpNegUnit  : 18
% 3.76/1.66  #BackRed      : 77
% 3.76/1.66  
% 3.76/1.66  #Partial instantiations: 0
% 3.76/1.66  #Strategies tried      : 1
% 3.76/1.66  
% 3.76/1.66  Timing (in seconds)
% 3.76/1.66  ----------------------
% 3.76/1.66  Preprocessing        : 0.31
% 3.76/1.66  Parsing              : 0.17
% 3.76/1.66  CNF conversion       : 0.02
% 3.76/1.66  Main loop            : 0.57
% 3.76/1.66  Inferencing          : 0.21
% 3.76/1.66  Reduction            : 0.17
% 3.76/1.66  Demodulation         : 0.11
% 3.76/1.66  BG Simplification    : 0.03
% 3.76/1.66  Subsumption          : 0.09
% 3.76/1.66  Abstraction          : 0.03
% 3.76/1.66  MUC search           : 0.00
% 3.76/1.66  Cooper               : 0.00
% 3.76/1.66  Total                : 0.94
% 3.76/1.66  Index Insertion      : 0.00
% 3.76/1.66  Index Deletion       : 0.00
% 3.76/1.66  Index Matching       : 0.00
% 3.76/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
