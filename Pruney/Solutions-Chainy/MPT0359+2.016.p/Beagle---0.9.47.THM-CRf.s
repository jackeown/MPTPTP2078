%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:11 EST 2020

% Result     : Theorem 17.20s
% Output     : CNFRefutation 17.20s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 193 expanded)
%              Number of leaves         :   33 (  76 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 294 expanded)
%              Number of equality atoms :   47 ( 121 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_53,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_51,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_805,plain,(
    ! [A_82,C_83,B_84] :
      ( r1_tarski(k5_xboole_0(A_82,C_83),B_84)
      | ~ r1_tarski(C_83,B_84)
      | ~ r1_tarski(A_82,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1924,plain,(
    ! [B_116,A_117] :
      ( r1_tarski(k1_xboole_0,B_116)
      | ~ r1_tarski(A_117,B_116)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_805])).

tff(c_1930,plain,(
    ! [B_6] :
      ( r1_tarski(k1_xboole_0,B_6)
      | ~ r1_tarski(B_6,B_6) ) ),
    inference(resolution,[status(thm)],[c_10,c_1924])).

tff(c_1935,plain,(
    ! [B_6] : r1_tarski(k1_xboole_0,B_6) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1930])).

tff(c_253,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_257,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_253])).

tff(c_297,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_310,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_297])).

tff(c_323,plain,(
    ! [B_6] : k4_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_310])).

tff(c_44,plain,(
    ! [A_26] : k2_subset_1(A_26) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_58,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_59,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_58])).

tff(c_226,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_59])).

tff(c_50,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_227,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_50])).

tff(c_433,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_443,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_227,c_433])).

tff(c_447,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_443])).

tff(c_52,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_60,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_52])).

tff(c_252,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_226,c_226,c_60])).

tff(c_448,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_447,c_252])).

tff(c_1939,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1935,c_448])).

tff(c_1941,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_48,plain,(
    ! [A_29] : ~ v1_xboole_0(k1_zfmisc_1(A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2079,plain,(
    ! [B_139,A_140] :
      ( r2_hidden(B_139,A_140)
      | ~ m1_subset_1(B_139,A_140)
      | v1_xboole_0(A_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_24,plain,(
    ! [C_23,A_19] :
      ( r1_tarski(C_23,A_19)
      | ~ r2_hidden(C_23,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2086,plain,(
    ! [B_139,A_19] :
      ( r1_tarski(B_139,A_19)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_19))
      | v1_xboole_0(k1_zfmisc_1(A_19)) ) ),
    inference(resolution,[status(thm)],[c_2079,c_24])).

tff(c_2092,plain,(
    ! [B_141,A_142] :
      ( r1_tarski(B_141,A_142)
      | ~ m1_subset_1(B_141,k1_zfmisc_1(A_142)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_2086])).

tff(c_2105,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_2092])).

tff(c_6,plain,(
    ! [B_6,A_5] :
      ( B_6 = A_5
      | ~ r1_tarski(B_6,A_5)
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2107,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2105,c_6])).

tff(c_2113,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_1941,c_2107])).

tff(c_1940,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_59])).

tff(c_2569,plain,(
    ! [A_154,B_155] :
      ( k4_xboole_0(A_154,B_155) = k3_subset_1(A_154,B_155)
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_154)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2582,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_50,c_2569])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2114,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2105,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1995,plain,(
    ! [A_129,B_130] : k5_xboole_0(A_129,k3_xboole_0(A_129,B_130)) = k4_xboole_0(A_129,B_130) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2590,plain,(
    ! [A_156,B_157] : k5_xboole_0(A_156,k3_xboole_0(B_157,A_156)) = k4_xboole_0(A_156,B_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1995])).

tff(c_2633,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2114,c_2590])).

tff(c_2658,plain,(
    k5_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2582,c_2633])).

tff(c_132,plain,(
    ! [B_37,A_38] : k5_xboole_0(B_37,A_38) = k5_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_18,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_148,plain,(
    ! [A_38] : k5_xboole_0(k1_xboole_0,A_38) = A_38 ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_18])).

tff(c_2123,plain,(
    ! [A_143,B_144,C_145] : k5_xboole_0(k5_xboole_0(A_143,B_144),C_145) = k5_xboole_0(A_143,k5_xboole_0(B_144,C_145)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2187,plain,(
    ! [A_18,C_145] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_145)) = k5_xboole_0(k1_xboole_0,C_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_2123])).

tff(c_2200,plain,(
    ! [A_18,C_145] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_145)) = C_145 ),
    inference(demodulation,[status(thm),theory(equality)],[c_148,c_2187])).

tff(c_2701,plain,(
    k5_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2658,c_2200])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2752,plain,(
    ! [A_159,C_160,B_161] :
      ( r1_tarski(k5_xboole_0(A_159,C_160),B_161)
      | ~ r1_tarski(C_160,B_161)
      | ~ r1_tarski(A_159,B_161) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_14673,plain,(
    ! [A_270,B_271,C_272,B_273] :
      ( r1_tarski(k5_xboole_0(A_270,k5_xboole_0(B_271,C_272)),B_273)
      | ~ r1_tarski(C_272,B_273)
      | ~ r1_tarski(k5_xboole_0(A_270,B_271),B_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_2752])).

tff(c_14993,plain,(
    ! [A_270,B_273,A_18] :
      ( r1_tarski(k5_xboole_0(A_270,k1_xboole_0),B_273)
      | ~ r1_tarski(A_18,B_273)
      | ~ r1_tarski(k5_xboole_0(A_270,A_18),B_273) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_14673])).

tff(c_35997,plain,(
    ! [A_353,B_354,A_355] :
      ( r1_tarski(A_353,B_354)
      | ~ r1_tarski(A_355,B_354)
      | ~ r1_tarski(k5_xboole_0(A_353,A_355),B_354) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_14993])).

tff(c_38096,plain,(
    ! [A_360,A_361] :
      ( r1_tarski(A_360,k5_xboole_0(A_360,A_361))
      | ~ r1_tarski(A_361,k5_xboole_0(A_360,A_361)) ) ),
    inference(resolution,[status(thm)],[c_10,c_35997])).

tff(c_38246,plain,
    ( r1_tarski('#skF_3',k5_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')))
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2701,c_38096])).

tff(c_38348,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1940,c_2701,c_38246])).

tff(c_38350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2113,c_38348])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:51 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 17.20/9.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.20/9.65  
% 17.20/9.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.20/9.65  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 17.20/9.65  
% 17.20/9.65  %Foreground sorts:
% 17.20/9.65  
% 17.20/9.65  
% 17.20/9.65  %Background operators:
% 17.20/9.65  
% 17.20/9.65  
% 17.20/9.65  %Foreground operators:
% 17.20/9.65  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 17.20/9.65  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 17.20/9.65  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 17.20/9.65  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 17.20/9.65  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 17.20/9.65  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 17.20/9.65  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 17.20/9.65  tff('#skF_3', type, '#skF_3': $i).
% 17.20/9.65  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 17.20/9.65  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 17.20/9.65  tff('#skF_4', type, '#skF_4': $i).
% 17.20/9.65  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 17.20/9.65  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 17.20/9.65  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 17.20/9.65  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 17.20/9.65  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 17.20/9.65  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 17.20/9.65  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 17.20/9.65  
% 17.20/9.67  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 17.20/9.67  tff(f_53, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 17.20/9.67  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 17.20/9.67  tff(f_47, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 17.20/9.67  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 17.20/9.67  tff(f_75, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 17.20/9.67  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 17.20/9.67  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 17.20/9.67  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 17.20/9.67  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 17.20/9.67  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 17.20/9.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 17.20/9.67  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 17.20/9.67  tff(f_49, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 17.20/9.67  tff(f_51, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 17.20/9.67  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.20/9.67  tff(c_22, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 17.20/9.67  tff(c_805, plain, (![A_82, C_83, B_84]: (r1_tarski(k5_xboole_0(A_82, C_83), B_84) | ~r1_tarski(C_83, B_84) | ~r1_tarski(A_82, B_84))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.20/9.67  tff(c_1924, plain, (![B_116, A_117]: (r1_tarski(k1_xboole_0, B_116) | ~r1_tarski(A_117, B_116) | ~r1_tarski(A_117, B_116))), inference(superposition, [status(thm), theory('equality')], [c_22, c_805])).
% 17.20/9.67  tff(c_1930, plain, (![B_6]: (r1_tarski(k1_xboole_0, B_6) | ~r1_tarski(B_6, B_6))), inference(resolution, [status(thm)], [c_10, c_1924])).
% 17.20/9.67  tff(c_1935, plain, (![B_6]: (r1_tarski(k1_xboole_0, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1930])).
% 17.20/9.67  tff(c_253, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.20/9.67  tff(c_257, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_253])).
% 17.20/9.67  tff(c_297, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.20/9.67  tff(c_310, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_257, c_297])).
% 17.20/9.67  tff(c_323, plain, (![B_6]: (k4_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_310])).
% 17.20/9.67  tff(c_44, plain, (![A_26]: (k2_subset_1(A_26)=A_26)), inference(cnfTransformation, [status(thm)], [f_75])).
% 17.20/9.67  tff(c_58, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.20/9.67  tff(c_59, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_44, c_58])).
% 17.20/9.67  tff(c_226, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_59])).
% 17.20/9.67  tff(c_50, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.20/9.67  tff(c_227, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_226, c_50])).
% 17.20/9.67  tff(c_433, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.20/9.67  tff(c_443, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_227, c_433])).
% 17.20/9.67  tff(c_447, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_323, c_443])).
% 17.20/9.67  tff(c_52, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 17.20/9.67  tff(c_60, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_44, c_52])).
% 17.20/9.67  tff(c_252, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_226, c_226, c_60])).
% 17.20/9.67  tff(c_448, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_447, c_252])).
% 17.20/9.67  tff(c_1939, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1935, c_448])).
% 17.20/9.67  tff(c_1941, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_59])).
% 17.20/9.67  tff(c_48, plain, (![A_29]: (~v1_xboole_0(k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 17.20/9.67  tff(c_2079, plain, (![B_139, A_140]: (r2_hidden(B_139, A_140) | ~m1_subset_1(B_139, A_140) | v1_xboole_0(A_140))), inference(cnfTransformation, [status(thm)], [f_73])).
% 17.20/9.67  tff(c_24, plain, (![C_23, A_19]: (r1_tarski(C_23, A_19) | ~r2_hidden(C_23, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 17.20/9.67  tff(c_2086, plain, (![B_139, A_19]: (r1_tarski(B_139, A_19) | ~m1_subset_1(B_139, k1_zfmisc_1(A_19)) | v1_xboole_0(k1_zfmisc_1(A_19)))), inference(resolution, [status(thm)], [c_2079, c_24])).
% 17.20/9.67  tff(c_2092, plain, (![B_141, A_142]: (r1_tarski(B_141, A_142) | ~m1_subset_1(B_141, k1_zfmisc_1(A_142)))), inference(negUnitSimplification, [status(thm)], [c_48, c_2086])).
% 17.20/9.67  tff(c_2105, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_50, c_2092])).
% 17.20/9.67  tff(c_6, plain, (![B_6, A_5]: (B_6=A_5 | ~r1_tarski(B_6, A_5) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 17.20/9.67  tff(c_2107, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2105, c_6])).
% 17.20/9.67  tff(c_2113, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_1941, c_2107])).
% 17.20/9.67  tff(c_1940, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_59])).
% 17.20/9.67  tff(c_2569, plain, (![A_154, B_155]: (k4_xboole_0(A_154, B_155)=k3_subset_1(A_154, B_155) | ~m1_subset_1(B_155, k1_zfmisc_1(A_154)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 17.20/9.67  tff(c_2582, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_50, c_2569])).
% 17.20/9.67  tff(c_16, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 17.20/9.67  tff(c_2114, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_2105, c_16])).
% 17.20/9.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 17.20/9.67  tff(c_1995, plain, (![A_129, B_130]: (k5_xboole_0(A_129, k3_xboole_0(A_129, B_130))=k4_xboole_0(A_129, B_130))), inference(cnfTransformation, [status(thm)], [f_37])).
% 17.20/9.67  tff(c_2590, plain, (![A_156, B_157]: (k5_xboole_0(A_156, k3_xboole_0(B_157, A_156))=k4_xboole_0(A_156, B_157))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1995])).
% 17.20/9.67  tff(c_2633, plain, (k5_xboole_0('#skF_3', '#skF_4')=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2114, c_2590])).
% 17.20/9.67  tff(c_2658, plain, (k5_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2582, c_2633])).
% 17.20/9.67  tff(c_132, plain, (![B_37, A_38]: (k5_xboole_0(B_37, A_38)=k5_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_29])).
% 17.20/9.67  tff(c_18, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_49])).
% 17.20/9.67  tff(c_148, plain, (![A_38]: (k5_xboole_0(k1_xboole_0, A_38)=A_38)), inference(superposition, [status(thm), theory('equality')], [c_132, c_18])).
% 17.20/9.67  tff(c_2123, plain, (![A_143, B_144, C_145]: (k5_xboole_0(k5_xboole_0(A_143, B_144), C_145)=k5_xboole_0(A_143, k5_xboole_0(B_144, C_145)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.20/9.67  tff(c_2187, plain, (![A_18, C_145]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_145))=k5_xboole_0(k1_xboole_0, C_145))), inference(superposition, [status(thm), theory('equality')], [c_22, c_2123])).
% 17.20/9.67  tff(c_2200, plain, (![A_18, C_145]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_145))=C_145)), inference(demodulation, [status(thm), theory('equality')], [c_148, c_2187])).
% 17.20/9.67  tff(c_2701, plain, (k5_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2658, c_2200])).
% 17.20/9.67  tff(c_20, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 17.20/9.67  tff(c_2752, plain, (![A_159, C_160, B_161]: (r1_tarski(k5_xboole_0(A_159, C_160), B_161) | ~r1_tarski(C_160, B_161) | ~r1_tarski(A_159, B_161))), inference(cnfTransformation, [status(thm)], [f_43])).
% 17.20/9.67  tff(c_14673, plain, (![A_270, B_271, C_272, B_273]: (r1_tarski(k5_xboole_0(A_270, k5_xboole_0(B_271, C_272)), B_273) | ~r1_tarski(C_272, B_273) | ~r1_tarski(k5_xboole_0(A_270, B_271), B_273))), inference(superposition, [status(thm), theory('equality')], [c_20, c_2752])).
% 17.20/9.67  tff(c_14993, plain, (![A_270, B_273, A_18]: (r1_tarski(k5_xboole_0(A_270, k1_xboole_0), B_273) | ~r1_tarski(A_18, B_273) | ~r1_tarski(k5_xboole_0(A_270, A_18), B_273))), inference(superposition, [status(thm), theory('equality')], [c_22, c_14673])).
% 17.20/9.67  tff(c_35997, plain, (![A_353, B_354, A_355]: (r1_tarski(A_353, B_354) | ~r1_tarski(A_355, B_354) | ~r1_tarski(k5_xboole_0(A_353, A_355), B_354))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_14993])).
% 17.20/9.67  tff(c_38096, plain, (![A_360, A_361]: (r1_tarski(A_360, k5_xboole_0(A_360, A_361)) | ~r1_tarski(A_361, k5_xboole_0(A_360, A_361)))), inference(resolution, [status(thm)], [c_10, c_35997])).
% 17.20/9.67  tff(c_38246, plain, (r1_tarski('#skF_3', k5_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))) | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2701, c_38096])).
% 17.20/9.67  tff(c_38348, plain, (r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1940, c_2701, c_38246])).
% 17.20/9.67  tff(c_38350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2113, c_38348])).
% 17.20/9.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 17.20/9.67  
% 17.20/9.67  Inference rules
% 17.20/9.67  ----------------------
% 17.20/9.67  #Ref     : 0
% 17.20/9.67  #Sup     : 9854
% 17.20/9.67  #Fact    : 0
% 17.20/9.67  #Define  : 0
% 17.20/9.67  #Split   : 3
% 17.20/9.67  #Chain   : 0
% 17.20/9.67  #Close   : 0
% 17.20/9.67  
% 17.20/9.67  Ordering : KBO
% 17.20/9.67  
% 17.20/9.67  Simplification rules
% 17.20/9.67  ----------------------
% 17.20/9.67  #Subsume      : 935
% 17.20/9.67  #Demod        : 14627
% 17.20/9.67  #Tautology    : 3897
% 17.20/9.67  #SimpNegUnit  : 11
% 17.20/9.67  #BackRed      : 13
% 17.20/9.67  
% 17.20/9.67  #Partial instantiations: 0
% 17.20/9.67  #Strategies tried      : 1
% 17.20/9.67  
% 17.20/9.67  Timing (in seconds)
% 17.20/9.67  ----------------------
% 17.41/9.67  Preprocessing        : 0.35
% 17.41/9.67  Parsing              : 0.18
% 17.41/9.67  CNF conversion       : 0.02
% 17.41/9.67  Main loop            : 8.52
% 17.41/9.67  Inferencing          : 1.02
% 17.41/9.67  Reduction            : 6.29
% 17.41/9.67  Demodulation         : 5.98
% 17.41/9.67  BG Simplification    : 0.16
% 17.41/9.67  Subsumption          : 0.85
% 17.41/9.67  Abstraction          : 0.25
% 17.41/9.67  MUC search           : 0.00
% 17.41/9.67  Cooper               : 0.00
% 17.41/9.67  Total                : 8.91
% 17.41/9.67  Index Insertion      : 0.00
% 17.41/9.67  Index Deletion       : 0.00
% 17.41/9.67  Index Matching       : 0.00
% 17.41/9.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------
