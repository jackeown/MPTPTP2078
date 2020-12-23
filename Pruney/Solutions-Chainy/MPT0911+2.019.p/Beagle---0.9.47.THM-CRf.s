%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:04 EST 2020

% Result     : Theorem 16.65s
% Output     : CNFRefutation 16.85s
% Verified   : 
% Statistics : Number of formulae       :  127 ( 322 expanded)
%              Number of leaves         :   46 ( 131 expanded)
%              Depth                    :   14
%              Number of atoms          :  208 ( 880 expanded)
%              Number of equality atoms :   92 ( 402 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_150,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_111,axiom,(
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

tff(f_57,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

tff(f_61,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_91,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] :
            ~ ( r2_hidden(B,A)
              & ! [C,D,E,F] :
                  ~ ( ( r2_hidden(C,A)
                      | r2_hidden(D,A) )
                    & B = k4_mcart_1(C,D,E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_mcart_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_126,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_40,axiom,(
    ! [A,B] : ~ v1_xboole_0(k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_60,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_66,plain,(
    m1_subset_1('#skF_7',k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_599,plain,(
    ! [A_184,B_185,C_186,D_187] :
      ( k7_mcart_1(A_184,B_185,C_186,D_187) = k2_mcart_1(D_187)
      | ~ m1_subset_1(D_187,k3_zfmisc_1(A_184,B_185,C_186))
      | k1_xboole_0 = C_186
      | k1_xboole_0 = B_185
      | k1_xboole_0 = A_184 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_616,plain,
    ( k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_599])).

tff(c_623,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') = k2_mcart_1('#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60,c_58,c_616])).

tff(c_56,plain,(
    k7_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_624,plain,(
    k2_mcart_1('#skF_7') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_56])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_167,plain,(
    ! [B_101,A_102] :
      ( ~ r1_tarski(B_101,A_102)
      | ~ r2_hidden(A_102,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_185,plain,(
    ! [A_108] :
      ( ~ r1_tarski(A_108,'#skF_1'(A_108))
      | v1_xboole_0(A_108) ) ),
    inference(resolution,[status(thm)],[c_4,c_167])).

tff(c_190,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_185])).

tff(c_225,plain,(
    ! [A_116,B_117,C_118] : k2_zfmisc_1(k2_zfmisc_1(A_116,B_117),C_118) = k3_zfmisc_1(A_116,B_117,C_118) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_233,plain,(
    ! [A_116,B_117,C_118] : v1_relat_1(k3_zfmisc_1(A_116,B_117,C_118)) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_18])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( r2_hidden(A_15,B_16)
      | v1_xboole_0(B_16)
      | ~ m1_subset_1(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_328,plain,(
    ! [A_142,B_143] :
      ( k4_tarski(k1_mcart_1(A_142),k2_mcart_1(A_142)) = A_142
      | ~ r2_hidden(A_142,B_143)
      | ~ v1_relat_1(B_143) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_9193,plain,(
    ! [A_520,B_521] :
      ( k4_tarski(k1_mcart_1(A_520),k2_mcart_1(A_520)) = A_520
      | ~ v1_relat_1(B_521)
      | v1_xboole_0(B_521)
      | ~ m1_subset_1(A_520,B_521) ) ),
    inference(resolution,[status(thm)],[c_16,c_328])).

tff(c_9207,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_3','#skF_4','#skF_5'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_9193])).

tff(c_9216,plain,
    ( k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7'
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_9207])).

tff(c_9217,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_9216])).

tff(c_79,plain,(
    ! [A_89] :
      ( r2_hidden('#skF_2'(A_89),A_89)
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_89] :
      ( ~ v1_xboole_0(A_89)
      | k1_xboole_0 = A_89 ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_9251,plain,(
    k3_zfmisc_1('#skF_3','#skF_4','#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9217,c_87])).

tff(c_26,plain,(
    ! [A_27,B_28,C_29,D_30] : k2_zfmisc_1(k3_zfmisc_1(A_27,B_28,C_29),D_30) = k4_zfmisc_1(A_27,B_28,C_29,D_30) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_258,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_hidden(k1_mcart_1(A_125),B_126)
      | ~ r2_hidden(A_125,k2_zfmisc_1(B_126,C_127)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1058,plain,(
    ! [B_224,C_225] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_224,C_225))),B_224)
      | v1_xboole_0(k2_zfmisc_1(B_224,C_225)) ) ),
    inference(resolution,[status(thm)],[c_4,c_258])).

tff(c_1124,plain,(
    ! [B_226,C_227] :
      ( ~ v1_xboole_0(B_226)
      | v1_xboole_0(k2_zfmisc_1(B_226,C_227)) ) ),
    inference(resolution,[status(thm)],[c_1058,c_2])).

tff(c_4404,plain,(
    ! [A_391,B_392,C_393,D_394] :
      ( ~ v1_xboole_0(k3_zfmisc_1(A_391,B_392,C_393))
      | v1_xboole_0(k4_zfmisc_1(A_391,B_392,C_393,D_394)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1124])).

tff(c_4471,plain,(
    ! [A_391,B_392,C_393,D_394] :
      ( k4_zfmisc_1(A_391,B_392,C_393,D_394) = k1_xboole_0
      | ~ v1_xboole_0(k3_zfmisc_1(A_391,B_392,C_393)) ) ),
    inference(resolution,[status(thm)],[c_4404,c_87])).

tff(c_9278,plain,(
    ! [D_394] :
      ( k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_394) = k1_xboole_0
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9251,c_4471])).

tff(c_9371,plain,(
    ! [D_522] : k4_zfmisc_1('#skF_3','#skF_4','#skF_5',D_522) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_9278])).

tff(c_46,plain,(
    ! [A_59,B_60,C_61,D_62] :
      ( k4_zfmisc_1(A_59,B_60,C_61,D_62) != k1_xboole_0
      | k1_xboole_0 = D_62
      | k1_xboole_0 = C_61
      | k1_xboole_0 = B_60
      | k1_xboole_0 = A_59 ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_9417,plain,(
    ! [D_522] :
      ( k1_xboole_0 = D_522
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9371,c_46])).

tff(c_9470,plain,(
    ! [D_523] : k1_xboole_0 = D_523 ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60,c_58,c_9417])).

tff(c_12,plain,(
    ! [A_11,B_12] : ~ v1_xboole_0(k2_tarski(A_11,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_9645,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_9470,c_12])).

tff(c_9691,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_9645])).

tff(c_9693,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(splitRight,[status(thm)],[c_9216])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] : k2_zfmisc_1(k2_zfmisc_1(A_24,B_25),C_26) = k3_zfmisc_1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_273,plain,(
    ! [A_128,C_129,B_130] :
      ( r2_hidden(k2_mcart_1(A_128),C_129)
      | ~ r2_hidden(A_128,k2_zfmisc_1(B_130,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_9133,plain,(
    ! [A_517,C_518,B_519] :
      ( r2_hidden(k2_mcart_1(A_517),C_518)
      | v1_xboole_0(k2_zfmisc_1(B_519,C_518))
      | ~ m1_subset_1(A_517,k2_zfmisc_1(B_519,C_518)) ) ),
    inference(resolution,[status(thm)],[c_16,c_273])).

tff(c_9173,plain,(
    ! [A_517,C_26,A_24,B_25] :
      ( r2_hidden(k2_mcart_1(A_517),C_26)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_24,B_25),C_26))
      | ~ m1_subset_1(A_517,k3_zfmisc_1(A_24,B_25,C_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_9133])).

tff(c_35356,plain,(
    ! [A_3344,C_3345,A_3346,B_3347] :
      ( r2_hidden(k2_mcart_1(A_3344),C_3345)
      | v1_xboole_0(k3_zfmisc_1(A_3346,B_3347,C_3345))
      | ~ m1_subset_1(A_3344,k3_zfmisc_1(A_3346,B_3347,C_3345)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_9173])).

tff(c_35438,plain,
    ( r2_hidden(k2_mcart_1('#skF_7'),'#skF_5')
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_35356])).

tff(c_35455,plain,(
    r2_hidden(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_9693,c_35438])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(A_13,B_14)
      | ~ r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_35479,plain,(
    m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_35455,c_14])).

tff(c_9692,plain,(
    k4_tarski(k1_mcart_1('#skF_7'),k2_mcart_1('#skF_7')) = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_9216])).

tff(c_663,plain,(
    ! [A_190,B_191,C_192,D_193] :
      ( k5_mcart_1(A_190,B_191,C_192,D_193) = k1_mcart_1(k1_mcart_1(D_193))
      | ~ m1_subset_1(D_193,k3_zfmisc_1(A_190,B_191,C_192))
      | k1_xboole_0 = C_192
      | k1_xboole_0 = B_191
      | k1_xboole_0 = A_190 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_680,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_663])).

tff(c_687,plain,(
    k1_mcart_1(k1_mcart_1('#skF_7')) = k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60,c_58,c_680])).

tff(c_3994,plain,(
    ! [A_367,A_368,B_369,C_370] :
      ( r2_hidden(k1_mcart_1(A_367),k2_zfmisc_1(A_368,B_369))
      | ~ r2_hidden(A_367,k3_zfmisc_1(A_368,B_369,C_370)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_258])).

tff(c_76493,plain,(
    ! [A_3880,A_3881,B_3882,C_3883] :
      ( r2_hidden(k1_mcart_1(A_3880),k2_zfmisc_1(A_3881,B_3882))
      | v1_xboole_0(k3_zfmisc_1(A_3881,B_3882,C_3883))
      | ~ m1_subset_1(A_3880,k3_zfmisc_1(A_3881,B_3882,C_3883)) ) ),
    inference(resolution,[status(thm)],[c_16,c_3994])).

tff(c_76601,plain,
    ( r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_3','#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_76493])).

tff(c_76621,plain,(
    r2_hidden(k1_mcart_1('#skF_7'),k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_9693,c_76601])).

tff(c_30,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden(k1_mcart_1(A_31),B_32)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76631,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_76621,c_30])).

tff(c_76649,plain,(
    r2_hidden(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_687,c_76631])).

tff(c_76718,plain,(
    m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_76649,c_14])).

tff(c_760,plain,(
    ! [A_197,B_198,C_199,D_200] :
      ( k6_mcart_1(A_197,B_198,C_199,D_200) = k2_mcart_1(k1_mcart_1(D_200))
      | ~ m1_subset_1(D_200,k3_zfmisc_1(A_197,B_198,C_199))
      | k1_xboole_0 = C_199
      | k1_xboole_0 = B_198
      | k1_xboole_0 = A_197 ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_780,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_66,c_760])).

tff(c_788,plain,(
    k2_mcart_1(k1_mcart_1('#skF_7')) = k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_60,c_58,c_780])).

tff(c_28,plain,(
    ! [A_31,C_33,B_32] :
      ( r2_hidden(k2_mcart_1(A_31),C_33)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_76629,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')),'#skF_4') ),
    inference(resolution,[status(thm)],[c_76621,c_28])).

tff(c_76647,plain,(
    r2_hidden(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_788,c_76629])).

tff(c_76693,plain,(
    m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_76647,c_14])).

tff(c_32,plain,(
    ! [A_34,B_35] :
      ( k4_tarski(k1_mcart_1(A_34),k2_mcart_1(A_34)) = A_34
      | ~ r2_hidden(A_34,B_35)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_76627,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')),k2_mcart_1(k1_mcart_1('#skF_7'))) = k1_mcart_1('#skF_7')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_76621,c_32])).

tff(c_76645,plain,(
    k4_tarski(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7')) = k1_mcart_1('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_687,c_788,c_76627])).

tff(c_22,plain,(
    ! [A_21,B_22,C_23] : k4_tarski(k4_tarski(A_21,B_22),C_23) = k3_mcart_1(A_21,B_22,C_23) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_86596,plain,(
    ! [C_3993] : k3_mcart_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),C_3993) = k4_tarski(k1_mcart_1('#skF_7'),C_3993) ),
    inference(superposition,[status(thm),theory(equality)],[c_76645,c_22])).

tff(c_64,plain,(
    ! [H_76,F_70,G_74] :
      ( H_76 = '#skF_6'
      | k3_mcart_1(F_70,G_74,H_76) != '#skF_7'
      | ~ m1_subset_1(H_76,'#skF_5')
      | ~ m1_subset_1(G_74,'#skF_4')
      | ~ m1_subset_1(F_70,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_150])).

tff(c_86603,plain,(
    ! [C_3993] :
      ( C_3993 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_3993) != '#skF_7'
      | ~ m1_subset_1(C_3993,'#skF_5')
      | ~ m1_subset_1(k6_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_4')
      | ~ m1_subset_1(k5_mcart_1('#skF_3','#skF_4','#skF_5','#skF_7'),'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_86596,c_64])).

tff(c_86612,plain,(
    ! [C_3994] :
      ( C_3994 = '#skF_6'
      | k4_tarski(k1_mcart_1('#skF_7'),C_3994) != '#skF_7'
      | ~ m1_subset_1(C_3994,'#skF_5') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76718,c_76693,c_86603])).

tff(c_86615,plain,
    ( k2_mcart_1('#skF_7') = '#skF_6'
    | ~ m1_subset_1(k2_mcart_1('#skF_7'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_9692,c_86612])).

tff(c_86618,plain,(
    k2_mcart_1('#skF_7') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35479,c_86615])).

tff(c_86620,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_624,c_86618])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.65/8.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.65/8.49  
% 16.65/8.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.65/8.50  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k2_enumset1 > k3_zfmisc_1 > k3_mcart_1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 16.65/8.50  
% 16.65/8.50  %Foreground sorts:
% 16.65/8.50  
% 16.65/8.50  
% 16.65/8.50  %Background operators:
% 16.65/8.50  
% 16.65/8.50  
% 16.65/8.50  %Foreground operators:
% 16.65/8.50  tff('#skF_2', type, '#skF_2': $i > $i).
% 16.65/8.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.65/8.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 16.65/8.50  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 16.65/8.50  tff('#skF_1', type, '#skF_1': $i > $i).
% 16.65/8.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.65/8.50  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 16.65/8.50  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 16.65/8.50  tff('#skF_7', type, '#skF_7': $i).
% 16.65/8.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.65/8.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 16.65/8.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 16.65/8.50  tff('#skF_5', type, '#skF_5': $i).
% 16.65/8.50  tff('#skF_6', type, '#skF_6': $i).
% 16.65/8.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 16.65/8.50  tff('#skF_3', type, '#skF_3': $i).
% 16.65/8.50  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 16.65/8.50  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 16.65/8.50  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 16.65/8.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.65/8.50  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 16.65/8.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.65/8.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.65/8.50  tff('#skF_4', type, '#skF_4': $i).
% 16.65/8.50  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 16.65/8.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.65/8.50  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 16.65/8.50  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 16.65/8.50  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 16.65/8.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.65/8.50  
% 16.65/8.51  tff(f_150, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 16.65/8.51  tff(f_111, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 16.65/8.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 16.65/8.51  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 16.65/8.51  tff(f_57, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 16.65/8.51  tff(f_61, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 16.65/8.51  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 16.65/8.51  tff(f_50, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 16.65/8.51  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_mcart_1)).
% 16.65/8.51  tff(f_91, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & (![C, D, E, F]: ~((r2_hidden(C, A) | r2_hidden(D, A)) & (B = k4_mcart_1(C, D, E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_mcart_1)).
% 16.65/8.51  tff(f_63, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 16.65/8.51  tff(f_69, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 16.65/8.51  tff(f_126, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_mcart_1)).
% 16.65/8.51  tff(f_40, axiom, (![A, B]: ~v1_xboole_0(k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_xboole_0)).
% 16.65/8.51  tff(f_44, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_subset)).
% 16.65/8.51  tff(f_59, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 16.65/8.51  tff(c_62, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.65/8.51  tff(c_60, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.65/8.51  tff(c_58, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.65/8.51  tff(c_66, plain, (m1_subset_1('#skF_7', k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.65/8.51  tff(c_599, plain, (![A_184, B_185, C_186, D_187]: (k7_mcart_1(A_184, B_185, C_186, D_187)=k2_mcart_1(D_187) | ~m1_subset_1(D_187, k3_zfmisc_1(A_184, B_185, C_186)) | k1_xboole_0=C_186 | k1_xboole_0=B_185 | k1_xboole_0=A_184)), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.65/8.51  tff(c_616, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_66, c_599])).
% 16.65/8.51  tff(c_623, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')=k2_mcart_1('#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_60, c_58, c_616])).
% 16.85/8.51  tff(c_56, plain, (k7_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.85/8.51  tff(c_624, plain, (k2_mcart_1('#skF_7')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_56])).
% 16.85/8.51  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 16.85/8.51  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.85/8.51  tff(c_167, plain, (![B_101, A_102]: (~r1_tarski(B_101, A_102) | ~r2_hidden(A_102, B_101))), inference(cnfTransformation, [status(thm)], [f_57])).
% 16.85/8.51  tff(c_185, plain, (![A_108]: (~r1_tarski(A_108, '#skF_1'(A_108)) | v1_xboole_0(A_108))), inference(resolution, [status(thm)], [c_4, c_167])).
% 16.85/8.51  tff(c_190, plain, (v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_185])).
% 16.85/8.51  tff(c_225, plain, (![A_116, B_117, C_118]: (k2_zfmisc_1(k2_zfmisc_1(A_116, B_117), C_118)=k3_zfmisc_1(A_116, B_117, C_118))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.85/8.51  tff(c_18, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 16.85/8.51  tff(c_233, plain, (![A_116, B_117, C_118]: (v1_relat_1(k3_zfmisc_1(A_116, B_117, C_118)))), inference(superposition, [status(thm), theory('equality')], [c_225, c_18])).
% 16.85/8.51  tff(c_16, plain, (![A_15, B_16]: (r2_hidden(A_15, B_16) | v1_xboole_0(B_16) | ~m1_subset_1(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_50])).
% 16.85/8.51  tff(c_328, plain, (![A_142, B_143]: (k4_tarski(k1_mcart_1(A_142), k2_mcart_1(A_142))=A_142 | ~r2_hidden(A_142, B_143) | ~v1_relat_1(B_143))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.85/8.51  tff(c_9193, plain, (![A_520, B_521]: (k4_tarski(k1_mcart_1(A_520), k2_mcart_1(A_520))=A_520 | ~v1_relat_1(B_521) | v1_xboole_0(B_521) | ~m1_subset_1(A_520, B_521))), inference(resolution, [status(thm)], [c_16, c_328])).
% 16.85/8.51  tff(c_9207, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | ~v1_relat_1(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_9193])).
% 16.85/8.51  tff(c_9216, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7' | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_233, c_9207])).
% 16.85/8.51  tff(c_9217, plain, (v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_9216])).
% 16.85/8.51  tff(c_79, plain, (![A_89]: (r2_hidden('#skF_2'(A_89), A_89) | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_91])).
% 16.85/8.51  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.85/8.51  tff(c_87, plain, (![A_89]: (~v1_xboole_0(A_89) | k1_xboole_0=A_89)), inference(resolution, [status(thm)], [c_79, c_2])).
% 16.85/8.51  tff(c_9251, plain, (k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_9217, c_87])).
% 16.85/8.51  tff(c_26, plain, (![A_27, B_28, C_29, D_30]: (k2_zfmisc_1(k3_zfmisc_1(A_27, B_28, C_29), D_30)=k4_zfmisc_1(A_27, B_28, C_29, D_30))), inference(cnfTransformation, [status(thm)], [f_63])).
% 16.85/8.51  tff(c_258, plain, (![A_125, B_126, C_127]: (r2_hidden(k1_mcart_1(A_125), B_126) | ~r2_hidden(A_125, k2_zfmisc_1(B_126, C_127)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.85/8.51  tff(c_1058, plain, (![B_224, C_225]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_224, C_225))), B_224) | v1_xboole_0(k2_zfmisc_1(B_224, C_225)))), inference(resolution, [status(thm)], [c_4, c_258])).
% 16.85/8.51  tff(c_1124, plain, (![B_226, C_227]: (~v1_xboole_0(B_226) | v1_xboole_0(k2_zfmisc_1(B_226, C_227)))), inference(resolution, [status(thm)], [c_1058, c_2])).
% 16.85/8.51  tff(c_4404, plain, (![A_391, B_392, C_393, D_394]: (~v1_xboole_0(k3_zfmisc_1(A_391, B_392, C_393)) | v1_xboole_0(k4_zfmisc_1(A_391, B_392, C_393, D_394)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1124])).
% 16.85/8.51  tff(c_4471, plain, (![A_391, B_392, C_393, D_394]: (k4_zfmisc_1(A_391, B_392, C_393, D_394)=k1_xboole_0 | ~v1_xboole_0(k3_zfmisc_1(A_391, B_392, C_393)))), inference(resolution, [status(thm)], [c_4404, c_87])).
% 16.85/8.51  tff(c_9278, plain, (![D_394]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_394)=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_9251, c_4471])).
% 16.85/8.51  tff(c_9371, plain, (![D_522]: (k4_zfmisc_1('#skF_3', '#skF_4', '#skF_5', D_522)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_9278])).
% 16.85/8.51  tff(c_46, plain, (![A_59, B_60, C_61, D_62]: (k4_zfmisc_1(A_59, B_60, C_61, D_62)!=k1_xboole_0 | k1_xboole_0=D_62 | k1_xboole_0=C_61 | k1_xboole_0=B_60 | k1_xboole_0=A_59)), inference(cnfTransformation, [status(thm)], [f_126])).
% 16.85/8.51  tff(c_9417, plain, (![D_522]: (k1_xboole_0=D_522 | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_9371, c_46])).
% 16.85/8.51  tff(c_9470, plain, (![D_523]: (k1_xboole_0=D_523)), inference(negUnitSimplification, [status(thm)], [c_62, c_60, c_58, c_9417])).
% 16.85/8.51  tff(c_12, plain, (![A_11, B_12]: (~v1_xboole_0(k2_tarski(A_11, B_12)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 16.85/8.51  tff(c_9645, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_9470, c_12])).
% 16.85/8.51  tff(c_9691, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_9645])).
% 16.85/8.51  tff(c_9693, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(splitRight, [status(thm)], [c_9216])).
% 16.85/8.51  tff(c_24, plain, (![A_24, B_25, C_26]: (k2_zfmisc_1(k2_zfmisc_1(A_24, B_25), C_26)=k3_zfmisc_1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.85/8.51  tff(c_273, plain, (![A_128, C_129, B_130]: (r2_hidden(k2_mcart_1(A_128), C_129) | ~r2_hidden(A_128, k2_zfmisc_1(B_130, C_129)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.85/8.51  tff(c_9133, plain, (![A_517, C_518, B_519]: (r2_hidden(k2_mcart_1(A_517), C_518) | v1_xboole_0(k2_zfmisc_1(B_519, C_518)) | ~m1_subset_1(A_517, k2_zfmisc_1(B_519, C_518)))), inference(resolution, [status(thm)], [c_16, c_273])).
% 16.85/8.51  tff(c_9173, plain, (![A_517, C_26, A_24, B_25]: (r2_hidden(k2_mcart_1(A_517), C_26) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_24, B_25), C_26)) | ~m1_subset_1(A_517, k3_zfmisc_1(A_24, B_25, C_26)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_9133])).
% 16.85/8.51  tff(c_35356, plain, (![A_3344, C_3345, A_3346, B_3347]: (r2_hidden(k2_mcart_1(A_3344), C_3345) | v1_xboole_0(k3_zfmisc_1(A_3346, B_3347, C_3345)) | ~m1_subset_1(A_3344, k3_zfmisc_1(A_3346, B_3347, C_3345)))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_9173])).
% 16.85/8.51  tff(c_35438, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_5') | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_35356])).
% 16.85/8.51  tff(c_35455, plain, (r2_hidden(k2_mcart_1('#skF_7'), '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_9693, c_35438])).
% 16.85/8.51  tff(c_14, plain, (![A_13, B_14]: (m1_subset_1(A_13, B_14) | ~r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.85/8.51  tff(c_35479, plain, (m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(resolution, [status(thm)], [c_35455, c_14])).
% 16.85/8.51  tff(c_9692, plain, (k4_tarski(k1_mcart_1('#skF_7'), k2_mcart_1('#skF_7'))='#skF_7'), inference(splitRight, [status(thm)], [c_9216])).
% 16.85/8.51  tff(c_663, plain, (![A_190, B_191, C_192, D_193]: (k5_mcart_1(A_190, B_191, C_192, D_193)=k1_mcart_1(k1_mcart_1(D_193)) | ~m1_subset_1(D_193, k3_zfmisc_1(A_190, B_191, C_192)) | k1_xboole_0=C_192 | k1_xboole_0=B_191 | k1_xboole_0=A_190)), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.85/8.51  tff(c_680, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_66, c_663])).
% 16.85/8.51  tff(c_687, plain, (k1_mcart_1(k1_mcart_1('#skF_7'))=k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_60, c_58, c_680])).
% 16.85/8.51  tff(c_3994, plain, (![A_367, A_368, B_369, C_370]: (r2_hidden(k1_mcart_1(A_367), k2_zfmisc_1(A_368, B_369)) | ~r2_hidden(A_367, k3_zfmisc_1(A_368, B_369, C_370)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_258])).
% 16.85/8.51  tff(c_76493, plain, (![A_3880, A_3881, B_3882, C_3883]: (r2_hidden(k1_mcart_1(A_3880), k2_zfmisc_1(A_3881, B_3882)) | v1_xboole_0(k3_zfmisc_1(A_3881, B_3882, C_3883)) | ~m1_subset_1(A_3880, k3_zfmisc_1(A_3881, B_3882, C_3883)))), inference(resolution, [status(thm)], [c_16, c_3994])).
% 16.85/8.51  tff(c_76601, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_3', '#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_76493])).
% 16.85/8.51  tff(c_76621, plain, (r2_hidden(k1_mcart_1('#skF_7'), k2_zfmisc_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_9693, c_76601])).
% 16.85/8.51  tff(c_30, plain, (![A_31, B_32, C_33]: (r2_hidden(k1_mcart_1(A_31), B_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.85/8.51  tff(c_76631, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_7')), '#skF_3')), inference(resolution, [status(thm)], [c_76621, c_30])).
% 16.85/8.51  tff(c_76649, plain, (r2_hidden(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_687, c_76631])).
% 16.85/8.51  tff(c_76718, plain, (m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3')), inference(resolution, [status(thm)], [c_76649, c_14])).
% 16.85/8.51  tff(c_760, plain, (![A_197, B_198, C_199, D_200]: (k6_mcart_1(A_197, B_198, C_199, D_200)=k2_mcart_1(k1_mcart_1(D_200)) | ~m1_subset_1(D_200, k3_zfmisc_1(A_197, B_198, C_199)) | k1_xboole_0=C_199 | k1_xboole_0=B_198 | k1_xboole_0=A_197)), inference(cnfTransformation, [status(thm)], [f_111])).
% 16.85/8.51  tff(c_780, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7') | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_66, c_760])).
% 16.85/8.51  tff(c_788, plain, (k2_mcart_1(k1_mcart_1('#skF_7'))=k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_62, c_60, c_58, c_780])).
% 16.85/8.51  tff(c_28, plain, (![A_31, C_33, B_32]: (r2_hidden(k2_mcart_1(A_31), C_33) | ~r2_hidden(A_31, k2_zfmisc_1(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 16.85/8.51  tff(c_76629, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_7')), '#skF_4')), inference(resolution, [status(thm)], [c_76621, c_28])).
% 16.85/8.51  tff(c_76647, plain, (r2_hidden(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_788, c_76629])).
% 16.85/8.51  tff(c_76693, plain, (m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4')), inference(resolution, [status(thm)], [c_76647, c_14])).
% 16.85/8.51  tff(c_32, plain, (![A_34, B_35]: (k4_tarski(k1_mcart_1(A_34), k2_mcart_1(A_34))=A_34 | ~r2_hidden(A_34, B_35) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_75])).
% 16.85/8.51  tff(c_76627, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_7')), k2_mcart_1(k1_mcart_1('#skF_7')))=k1_mcart_1('#skF_7') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_76621, c_32])).
% 16.85/8.51  tff(c_76645, plain, (k4_tarski(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'))=k1_mcart_1('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_687, c_788, c_76627])).
% 16.85/8.51  tff(c_22, plain, (![A_21, B_22, C_23]: (k4_tarski(k4_tarski(A_21, B_22), C_23)=k3_mcart_1(A_21, B_22, C_23))), inference(cnfTransformation, [status(thm)], [f_59])).
% 16.85/8.51  tff(c_86596, plain, (![C_3993]: (k3_mcart_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), C_3993)=k4_tarski(k1_mcart_1('#skF_7'), C_3993))), inference(superposition, [status(thm), theory('equality')], [c_76645, c_22])).
% 16.85/8.51  tff(c_64, plain, (![H_76, F_70, G_74]: (H_76='#skF_6' | k3_mcart_1(F_70, G_74, H_76)!='#skF_7' | ~m1_subset_1(H_76, '#skF_5') | ~m1_subset_1(G_74, '#skF_4') | ~m1_subset_1(F_70, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_150])).
% 16.85/8.51  tff(c_86603, plain, (![C_3993]: (C_3993='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_3993)!='#skF_7' | ~m1_subset_1(C_3993, '#skF_5') | ~m1_subset_1(k6_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_4') | ~m1_subset_1(k5_mcart_1('#skF_3', '#skF_4', '#skF_5', '#skF_7'), '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_86596, c_64])).
% 16.85/8.51  tff(c_86612, plain, (![C_3994]: (C_3994='#skF_6' | k4_tarski(k1_mcart_1('#skF_7'), C_3994)!='#skF_7' | ~m1_subset_1(C_3994, '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_76718, c_76693, c_86603])).
% 16.85/8.51  tff(c_86615, plain, (k2_mcart_1('#skF_7')='#skF_6' | ~m1_subset_1(k2_mcart_1('#skF_7'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_9692, c_86612])).
% 16.85/8.51  tff(c_86618, plain, (k2_mcart_1('#skF_7')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_35479, c_86615])).
% 16.85/8.51  tff(c_86620, plain, $false, inference(negUnitSimplification, [status(thm)], [c_624, c_86618])).
% 16.85/8.51  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.85/8.51  
% 16.85/8.51  Inference rules
% 16.85/8.51  ----------------------
% 16.85/8.51  #Ref     : 0
% 16.85/8.51  #Sup     : 22402
% 16.85/8.51  #Fact    : 0
% 16.85/8.51  #Define  : 0
% 16.85/8.51  #Split   : 6
% 16.85/8.51  #Chain   : 0
% 16.85/8.51  #Close   : 0
% 16.85/8.51  
% 16.85/8.51  Ordering : KBO
% 16.85/8.51  
% 16.85/8.51  Simplification rules
% 16.85/8.51  ----------------------
% 16.85/8.51  #Subsume      : 2241
% 16.85/8.51  #Demod        : 19475
% 16.85/8.51  #Tautology    : 16808
% 16.85/8.51  #SimpNegUnit  : 147
% 16.85/8.51  #BackRed      : 11
% 16.85/8.51  
% 16.85/8.51  #Partial instantiations: 275
% 16.85/8.51  #Strategies tried      : 1
% 16.85/8.51  
% 16.85/8.51  Timing (in seconds)
% 16.85/8.51  ----------------------
% 16.85/8.52  Preprocessing        : 0.36
% 16.85/8.52  Parsing              : 0.19
% 16.85/8.52  CNF conversion       : 0.03
% 16.85/8.52  Main loop            : 7.36
% 16.85/8.52  Inferencing          : 1.68
% 16.85/8.52  Reduction            : 2.32
% 16.85/8.52  Demodulation         : 1.70
% 16.85/8.52  BG Simplification    : 0.16
% 16.85/8.52  Subsumption          : 2.82
% 16.85/8.52  Abstraction          : 0.24
% 16.85/8.52  MUC search           : 0.00
% 16.85/8.52  Cooper               : 0.00
% 16.85/8.52  Total                : 7.77
% 16.85/8.52  Index Insertion      : 0.00
% 16.85/8.52  Index Deletion       : 0.00
% 16.85/8.52  Index Matching       : 0.00
% 16.85/8.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
