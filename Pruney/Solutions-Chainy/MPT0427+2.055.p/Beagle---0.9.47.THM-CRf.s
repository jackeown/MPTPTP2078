%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:04 EST 2020

% Result     : Theorem 2.53s
% Output     : CNFRefutation 2.64s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 246 expanded)
%              Number of leaves         :   24 (  89 expanded)
%              Depth                    :   10
%              Number of atoms          :   93 ( 505 expanded)
%              Number of equality atoms :   42 ( 227 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_6,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_5] :
      ( k8_setfam_1(A_5,k1_xboole_0) = A_5
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    ! [A_5] : k8_setfam_1(A_5,k1_xboole_0) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_173,plain,(
    ! [A_53,B_54] :
      ( m1_subset_1(k8_setfam_1(A_53,B_54),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(k1_zfmisc_1(A_53))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_185,plain,(
    ! [A_5] :
      ( m1_subset_1(A_5,k1_zfmisc_1(A_5))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_5))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_173])).

tff(c_191,plain,(
    ! [A_55] : m1_subset_1(A_55,k1_zfmisc_1(A_55)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_185])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_203,plain,(
    ! [A_55] : r1_tarski(A_55,A_55) ),
    inference(resolution,[status(thm)],[c_191,c_16])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ! [A_33,B_34] :
      ( k6_setfam_1(A_33,B_34) = k1_setfam_1(B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(k1_zfmisc_1(A_33))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_115,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_99])).

tff(c_227,plain,(
    ! [A_60,B_61] :
      ( k8_setfam_1(A_60,B_61) = k6_setfam_1(A_60,B_61)
      | k1_xboole_0 = B_61
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_242,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_30,c_227])).

tff(c_255,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_115,c_242])).

tff(c_261,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_255])).

tff(c_28,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_116,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_28,c_99])).

tff(c_245,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_227])).

tff(c_257,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_245])).

tff(c_284,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_257])).

tff(c_285,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_284])).

tff(c_24,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_292,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_24])).

tff(c_297,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_292])).

tff(c_298,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_284])).

tff(c_270,plain,(
    ! [A_5] : k8_setfam_1(A_5,'#skF_2') = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_261,c_32])).

tff(c_315,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_24])).

tff(c_354,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_315])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(k8_setfam_1(A_7,B_8),k1_zfmisc_1(A_7))
      | ~ m1_subset_1(B_8,k1_zfmisc_1(k1_zfmisc_1(A_7))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_340,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_298,c_12])).

tff(c_344,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_340])).

tff(c_372,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_344,c_16])).

tff(c_377,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_354,c_372])).

tff(c_379,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( r1_tarski(k1_setfam_1(B_17),k1_setfam_1(A_16))
      | k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_397,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_257])).

tff(c_398,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_379])).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(k1_xboole_0,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [A_27,B_28] :
      ( k1_xboole_0 = A_27
      | ~ r1_tarski(A_27,k4_xboole_0(B_28,A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_69])).

tff(c_465,plain,(
    ! [A_74] :
      ( A_74 = '#skF_3'
      | ~ r1_tarski(A_74,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_397,c_76])).

tff(c_476,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_26,c_465])).

tff(c_484,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_398,c_476])).

tff(c_485,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_257])).

tff(c_378,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_255])).

tff(c_380,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_378,c_24])).

tff(c_487,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_380])).

tff(c_499,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_487])).

tff(c_502,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_499])).

tff(c_504,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_379,c_502])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:05:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.53/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.35  
% 2.53/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.53/1.36  %$ r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.53/1.36  
% 2.53/1.36  %Foreground sorts:
% 2.53/1.36  
% 2.53/1.36  
% 2.53/1.36  %Background operators:
% 2.53/1.36  
% 2.53/1.36  
% 2.53/1.36  %Foreground operators:
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.53/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.53/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.53/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.53/1.36  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.53/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.53/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.53/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.53/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.53/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.53/1.36  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.53/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.53/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.53/1.36  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.53/1.36  
% 2.64/1.37  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.64/1.37  tff(f_44, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.64/1.37  tff(f_48, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.64/1.37  tff(f_56, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.64/1.37  tff(f_78, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.64/1.37  tff(f_52, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.64/1.37  tff(f_68, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.64/1.37  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.64/1.37  tff(f_29, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.64/1.37  tff(c_6, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.64/1.37  tff(c_8, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.64/1.37  tff(c_32, plain, (![A_5]: (k8_setfam_1(A_5, k1_xboole_0)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.64/1.37  tff(c_173, plain, (![A_53, B_54]: (m1_subset_1(k8_setfam_1(A_53, B_54), k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(k1_zfmisc_1(A_53))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.37  tff(c_185, plain, (![A_5]: (m1_subset_1(A_5, k1_zfmisc_1(A_5)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_5))))), inference(superposition, [status(thm), theory('equality')], [c_32, c_173])).
% 2.64/1.37  tff(c_191, plain, (![A_55]: (m1_subset_1(A_55, k1_zfmisc_1(A_55)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_185])).
% 2.64/1.37  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.64/1.37  tff(c_203, plain, (![A_55]: (r1_tarski(A_55, A_55))), inference(resolution, [status(thm)], [c_191, c_16])).
% 2.64/1.37  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.37  tff(c_99, plain, (![A_33, B_34]: (k6_setfam_1(A_33, B_34)=k1_setfam_1(B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(k1_zfmisc_1(A_33))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.64/1.37  tff(c_115, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_30, c_99])).
% 2.64/1.37  tff(c_227, plain, (![A_60, B_61]: (k8_setfam_1(A_60, B_61)=k6_setfam_1(A_60, B_61) | k1_xboole_0=B_61 | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.64/1.37  tff(c_242, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_30, c_227])).
% 2.64/1.37  tff(c_255, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_115, c_242])).
% 2.64/1.37  tff(c_261, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_255])).
% 2.64/1.37  tff(c_28, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.37  tff(c_116, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_28, c_99])).
% 2.64/1.37  tff(c_245, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_227])).
% 2.64/1.37  tff(c_257, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_245])).
% 2.64/1.37  tff(c_284, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_261, c_257])).
% 2.64/1.37  tff(c_285, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_284])).
% 2.64/1.37  tff(c_24, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.37  tff(c_292, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_285, c_24])).
% 2.64/1.37  tff(c_297, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_292])).
% 2.64/1.37  tff(c_298, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_284])).
% 2.64/1.37  tff(c_270, plain, (![A_5]: (k8_setfam_1(A_5, '#skF_2')=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_261, c_32])).
% 2.64/1.37  tff(c_315, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_24])).
% 2.64/1.37  tff(c_354, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_298, c_315])).
% 2.64/1.37  tff(c_12, plain, (![A_7, B_8]: (m1_subset_1(k8_setfam_1(A_7, B_8), k1_zfmisc_1(A_7)) | ~m1_subset_1(B_8, k1_zfmisc_1(k1_zfmisc_1(A_7))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.64/1.37  tff(c_340, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_298, c_12])).
% 2.64/1.37  tff(c_344, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_340])).
% 2.64/1.37  tff(c_372, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_344, c_16])).
% 2.64/1.37  tff(c_377, plain, $false, inference(negUnitSimplification, [status(thm)], [c_354, c_372])).
% 2.64/1.37  tff(c_379, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_255])).
% 2.64/1.37  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.64/1.37  tff(c_22, plain, (![B_17, A_16]: (r1_tarski(k1_setfam_1(B_17), k1_setfam_1(A_16)) | k1_xboole_0=A_16 | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.64/1.37  tff(c_397, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_257])).
% 2.64/1.37  tff(c_398, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_397, c_379])).
% 2.64/1.37  tff(c_4, plain, (![A_3]: (k4_xboole_0(k1_xboole_0, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.64/1.37  tff(c_69, plain, (![A_27, B_28]: (k1_xboole_0=A_27 | ~r1_tarski(A_27, k4_xboole_0(B_28, A_27)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.64/1.37  tff(c_76, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_69])).
% 2.64/1.37  tff(c_465, plain, (![A_74]: (A_74='#skF_3' | ~r1_tarski(A_74, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_397, c_397, c_76])).
% 2.64/1.37  tff(c_476, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_26, c_465])).
% 2.64/1.37  tff(c_484, plain, $false, inference(negUnitSimplification, [status(thm)], [c_398, c_476])).
% 2.64/1.37  tff(c_485, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_257])).
% 2.64/1.37  tff(c_378, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_255])).
% 2.64/1.37  tff(c_380, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_378, c_24])).
% 2.64/1.37  tff(c_487, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_380])).
% 2.64/1.37  tff(c_499, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_487])).
% 2.64/1.37  tff(c_502, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_499])).
% 2.64/1.37  tff(c_504, plain, $false, inference(negUnitSimplification, [status(thm)], [c_379, c_502])).
% 2.64/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.64/1.37  
% 2.64/1.37  Inference rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Ref     : 0
% 2.64/1.37  #Sup     : 94
% 2.64/1.37  #Fact    : 0
% 2.64/1.37  #Define  : 0
% 2.64/1.37  #Split   : 3
% 2.64/1.37  #Chain   : 0
% 2.64/1.37  #Close   : 0
% 2.64/1.37  
% 2.64/1.37  Ordering : KBO
% 2.64/1.37  
% 2.64/1.37  Simplification rules
% 2.64/1.37  ----------------------
% 2.64/1.37  #Subsume      : 3
% 2.64/1.37  #Demod        : 71
% 2.64/1.37  #Tautology    : 59
% 2.64/1.37  #SimpNegUnit  : 3
% 2.64/1.37  #BackRed      : 33
% 2.64/1.37  
% 2.64/1.37  #Partial instantiations: 0
% 2.64/1.37  #Strategies tried      : 1
% 2.64/1.37  
% 2.64/1.37  Timing (in seconds)
% 2.64/1.37  ----------------------
% 2.64/1.38  Preprocessing        : 0.31
% 2.64/1.38  Parsing              : 0.17
% 2.64/1.38  CNF conversion       : 0.02
% 2.64/1.38  Main loop            : 0.29
% 2.64/1.38  Inferencing          : 0.11
% 2.64/1.38  Reduction            : 0.09
% 2.64/1.38  Demodulation         : 0.07
% 2.64/1.38  BG Simplification    : 0.02
% 2.64/1.38  Subsumption          : 0.05
% 2.64/1.38  Abstraction          : 0.02
% 2.64/1.38  MUC search           : 0.00
% 2.64/1.38  Cooper               : 0.00
% 2.64/1.38  Total                : 0.64
% 2.64/1.38  Index Insertion      : 0.00
% 2.64/1.38  Index Deletion       : 0.00
% 2.64/1.38  Index Matching       : 0.00
% 2.64/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
