%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:02 EST 2020

% Result     : Theorem 2.45s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 249 expanded)
%              Number of leaves         :   24 (  90 expanded)
%              Depth                    :   10
%              Number of atoms          :  110 ( 501 expanded)
%              Number of equality atoms :   39 ( 196 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(r2_xboole_0,type,(
    r2_xboole_0: ( $i * $i ) > $o )).

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

tff(f_39,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r2_xboole_0(A,B)
    <=> ( r1_tarski(A,B)
        & A != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ~ ( r1_tarski(A,B)
        & r2_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_6] :
      ( k8_setfam_1(A_6,k1_xboole_0) = A_6
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_36,plain,(
    ! [A_6] : k8_setfam_1(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12])).

tff(c_526,plain,(
    ! [A_88,B_89] :
      ( m1_subset_1(k8_setfam_1(A_88,B_89),k1_zfmisc_1(A_88))
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_538,plain,(
    ! [A_6] :
      ( m1_subset_1(A_6,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_526])).

tff(c_544,plain,(
    ! [A_90] : m1_subset_1(A_90,k1_zfmisc_1(A_90)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_538])).

tff(c_20,plain,(
    ! [A_12,B_13] :
      ( r1_tarski(A_12,B_13)
      | ~ m1_subset_1(A_12,k1_zfmisc_1(B_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_556,plain,(
    ! [A_90] : r1_tarski(A_90,A_90) ),
    inference(resolution,[status(thm)],[c_544,c_20])).

tff(c_197,plain,(
    ! [A_60,B_61] :
      ( m1_subset_1(k8_setfam_1(A_60,B_61),k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(k1_zfmisc_1(A_60))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_209,plain,(
    ! [A_6] :
      ( m1_subset_1(A_6,k1_zfmisc_1(A_6))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_6))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_197])).

tff(c_243,plain,(
    ! [A_64] : m1_subset_1(A_64,k1_zfmisc_1(A_64)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_209])).

tff(c_260,plain,(
    ! [A_64] : r1_tarski(A_64,A_64) ),
    inference(resolution,[status(thm)],[c_243,c_20])).

tff(c_34,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_137,plain,(
    ! [A_46,B_47] :
      ( k6_setfam_1(A_46,B_47) = k1_setfam_1(B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(k1_zfmisc_1(A_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_153,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_137])).

tff(c_215,plain,(
    ! [A_62,B_63] :
      ( k8_setfam_1(A_62,B_63) = k6_setfam_1(A_62,B_63)
      | k1_xboole_0 = B_63
      | ~ m1_subset_1(B_63,k1_zfmisc_1(k1_zfmisc_1(A_62))) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_226,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_34,c_215])).

tff(c_237,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_153,c_226])).

tff(c_280,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_237])).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_154,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_137])).

tff(c_229,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_32,c_215])).

tff(c_239,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_229])).

tff(c_358,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_239])).

tff(c_359,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_358])).

tff(c_30,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( r2_xboole_0(A_32,B_33)
      | B_33 = A_32
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [B_4,A_3] :
      ( ~ r2_xboole_0(B_4,A_3)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [B_43,A_44] :
      ( ~ r1_tarski(B_43,A_44)
      | B_43 = A_44
      | ~ r1_tarski(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_69,c_8])).

tff(c_128,plain,
    ( '#skF_2' = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_116])).

tff(c_136,plain,(
    ~ r1_tarski('#skF_3','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_369,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_359,c_136])).

tff(c_373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_260,c_369])).

tff(c_374,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_358])).

tff(c_287,plain,(
    ! [A_6] : k8_setfam_1(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_280,c_36])).

tff(c_28,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_319,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_28])).

tff(c_376,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_374,c_319])).

tff(c_16,plain,(
    ! [A_8,B_9] :
      ( m1_subset_1(k8_setfam_1(A_8,B_9),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(k1_zfmisc_1(A_8))) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_380,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_374,c_16])).

tff(c_384,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_380])).

tff(c_390,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_384,c_20])).

tff(c_395,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_376,c_390])).

tff(c_397,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_26,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k1_setfam_1(B_18),k1_setfam_1(A_17))
      | k1_xboole_0 = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_418,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_239])).

tff(c_50,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_62,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_10,c_50])).

tff(c_425,plain,(
    ! [A_5] : r1_tarski('#skF_3',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_418,c_62])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_136])).

tff(c_437,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_239])).

tff(c_396,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_237])).

tff(c_398,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_396,c_28])).

tff(c_439,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_398])).

tff(c_451,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_439])).

tff(c_454,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_451])).

tff(c_456,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_397,c_454])).

tff(c_457,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_462,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_457,c_28])).

tff(c_560,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_462])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:28:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.45/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.53  
% 2.45/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.45/1.53  %$ r2_xboole_0 > r2_hidden > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.45/1.53  
% 2.45/1.53  %Foreground sorts:
% 2.45/1.53  
% 2.45/1.53  
% 2.45/1.53  %Background operators:
% 2.45/1.53  
% 2.45/1.53  
% 2.45/1.53  %Foreground operators:
% 2.45/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.45/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.45/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.45/1.53  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.45/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.45/1.53  tff('#skF_2', type, '#skF_2': $i).
% 2.45/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.45/1.53  tff('#skF_1', type, '#skF_1': $i).
% 2.45/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.45/1.53  tff(r2_xboole_0, type, r2_xboole_0: ($i * $i) > $o).
% 2.45/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.45/1.53  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.45/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.45/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.45/1.53  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.45/1.53  
% 2.76/1.54  tff(f_39, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.76/1.54  tff(f_50, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 2.76/1.54  tff(f_54, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 2.76/1.54  tff(f_62, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.76/1.54  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 2.76/1.54  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 2.76/1.54  tff(f_32, axiom, (![A, B]: (r2_xboole_0(A, B) <=> (r1_tarski(A, B) & ~(A = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d8_xboole_0)).
% 2.76/1.54  tff(f_37, axiom, (![A, B]: ~(r1_tarski(A, B) & r2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_xboole_1)).
% 2.76/1.54  tff(f_74, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 2.76/1.54  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.76/1.54  tff(c_12, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.54  tff(c_36, plain, (![A_6]: (k8_setfam_1(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12])).
% 2.76/1.54  tff(c_526, plain, (![A_88, B_89]: (m1_subset_1(k8_setfam_1(A_88, B_89), k1_zfmisc_1(A_88)) | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_88))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.54  tff(c_538, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_526])).
% 2.76/1.54  tff(c_544, plain, (![A_90]: (m1_subset_1(A_90, k1_zfmisc_1(A_90)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_538])).
% 2.76/1.54  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, B_13) | ~m1_subset_1(A_12, k1_zfmisc_1(B_13)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.54  tff(c_556, plain, (![A_90]: (r1_tarski(A_90, A_90))), inference(resolution, [status(thm)], [c_544, c_20])).
% 2.76/1.54  tff(c_197, plain, (![A_60, B_61]: (m1_subset_1(k8_setfam_1(A_60, B_61), k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(k1_zfmisc_1(A_60))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.54  tff(c_209, plain, (![A_6]: (m1_subset_1(A_6, k1_zfmisc_1(A_6)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_6))))), inference(superposition, [status(thm), theory('equality')], [c_36, c_197])).
% 2.76/1.54  tff(c_243, plain, (![A_64]: (m1_subset_1(A_64, k1_zfmisc_1(A_64)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_209])).
% 2.76/1.54  tff(c_260, plain, (![A_64]: (r1_tarski(A_64, A_64))), inference(resolution, [status(thm)], [c_243, c_20])).
% 2.76/1.54  tff(c_34, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.76/1.54  tff(c_137, plain, (![A_46, B_47]: (k6_setfam_1(A_46, B_47)=k1_setfam_1(B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(k1_zfmisc_1(A_46))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.76/1.54  tff(c_153, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_34, c_137])).
% 2.76/1.54  tff(c_215, plain, (![A_62, B_63]: (k8_setfam_1(A_62, B_63)=k6_setfam_1(A_62, B_63) | k1_xboole_0=B_63 | ~m1_subset_1(B_63, k1_zfmisc_1(k1_zfmisc_1(A_62))))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.76/1.54  tff(c_226, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_34, c_215])).
% 2.76/1.54  tff(c_237, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_153, c_226])).
% 2.76/1.54  tff(c_280, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_237])).
% 2.76/1.54  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.76/1.54  tff(c_154, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_137])).
% 2.76/1.54  tff(c_229, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_32, c_215])).
% 2.76/1.54  tff(c_239, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_154, c_229])).
% 2.76/1.54  tff(c_358, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_280, c_239])).
% 2.76/1.54  tff(c_359, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_358])).
% 2.76/1.54  tff(c_30, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.76/1.54  tff(c_69, plain, (![A_32, B_33]: (r2_xboole_0(A_32, B_33) | B_33=A_32 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.76/1.54  tff(c_8, plain, (![B_4, A_3]: (~r2_xboole_0(B_4, A_3) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.76/1.54  tff(c_116, plain, (![B_43, A_44]: (~r1_tarski(B_43, A_44) | B_43=A_44 | ~r1_tarski(A_44, B_43))), inference(resolution, [status(thm)], [c_69, c_8])).
% 2.76/1.54  tff(c_128, plain, ('#skF_2'='#skF_3' | ~r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_116])).
% 2.76/1.54  tff(c_136, plain, (~r1_tarski('#skF_3', '#skF_2')), inference(splitLeft, [status(thm)], [c_128])).
% 2.76/1.54  tff(c_369, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_359, c_136])).
% 2.76/1.54  tff(c_373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_260, c_369])).
% 2.76/1.54  tff(c_374, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_358])).
% 2.76/1.54  tff(c_287, plain, (![A_6]: (k8_setfam_1(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_280, c_36])).
% 2.76/1.54  tff(c_28, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.76/1.54  tff(c_319, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_287, c_28])).
% 2.76/1.54  tff(c_376, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_374, c_319])).
% 2.76/1.54  tff(c_16, plain, (![A_8, B_9]: (m1_subset_1(k8_setfam_1(A_8, B_9), k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(k1_zfmisc_1(A_8))))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.76/1.54  tff(c_380, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_374, c_16])).
% 2.76/1.54  tff(c_384, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_380])).
% 2.76/1.54  tff(c_390, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_384, c_20])).
% 2.76/1.54  tff(c_395, plain, $false, inference(negUnitSimplification, [status(thm)], [c_376, c_390])).
% 2.76/1.54  tff(c_397, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_237])).
% 2.76/1.54  tff(c_26, plain, (![B_18, A_17]: (r1_tarski(k1_setfam_1(B_18), k1_setfam_1(A_17)) | k1_xboole_0=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.76/1.54  tff(c_418, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_239])).
% 2.76/1.54  tff(c_50, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.76/1.54  tff(c_62, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_10, c_50])).
% 2.76/1.54  tff(c_425, plain, (![A_5]: (r1_tarski('#skF_3', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_418, c_62])).
% 2.76/1.54  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_425, c_136])).
% 2.76/1.54  tff(c_437, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_239])).
% 2.76/1.54  tff(c_396, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_237])).
% 2.76/1.54  tff(c_398, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_396, c_28])).
% 2.76/1.54  tff(c_439, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_437, c_398])).
% 2.76/1.54  tff(c_451, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_439])).
% 2.76/1.54  tff(c_454, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_451])).
% 2.76/1.54  tff(c_456, plain, $false, inference(negUnitSimplification, [status(thm)], [c_397, c_454])).
% 2.76/1.54  tff(c_457, plain, ('#skF_2'='#skF_3'), inference(splitRight, [status(thm)], [c_128])).
% 2.76/1.54  tff(c_462, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_457, c_28])).
% 2.76/1.54  tff(c_560, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_556, c_462])).
% 2.76/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.54  
% 2.76/1.54  Inference rules
% 2.76/1.54  ----------------------
% 2.76/1.54  #Ref     : 0
% 2.76/1.54  #Sup     : 103
% 2.76/1.54  #Fact    : 0
% 2.76/1.54  #Define  : 0
% 2.76/1.54  #Split   : 7
% 2.76/1.54  #Chain   : 0
% 2.76/1.54  #Close   : 0
% 2.76/1.54  
% 2.76/1.54  Ordering : KBO
% 2.76/1.54  
% 2.76/1.54  Simplification rules
% 2.76/1.54  ----------------------
% 2.76/1.54  #Subsume      : 8
% 2.76/1.54  #Demod        : 84
% 2.76/1.54  #Tautology    : 56
% 2.76/1.54  #SimpNegUnit  : 2
% 2.76/1.54  #BackRed      : 40
% 2.76/1.54  
% 2.76/1.54  #Partial instantiations: 0
% 2.76/1.54  #Strategies tried      : 1
% 2.76/1.54  
% 2.76/1.54  Timing (in seconds)
% 2.76/1.54  ----------------------
% 2.76/1.55  Preprocessing        : 0.41
% 2.76/1.55  Parsing              : 0.25
% 2.76/1.55  CNF conversion       : 0.02
% 2.76/1.55  Main loop            : 0.28
% 2.76/1.55  Inferencing          : 0.10
% 2.76/1.55  Reduction            : 0.09
% 2.76/1.55  Demodulation         : 0.06
% 2.76/1.55  BG Simplification    : 0.01
% 2.76/1.55  Subsumption          : 0.05
% 2.76/1.55  Abstraction          : 0.02
% 2.76/1.55  MUC search           : 0.00
% 2.76/1.55  Cooper               : 0.00
% 2.76/1.55  Total                : 0.72
% 2.76/1.55  Index Insertion      : 0.00
% 2.76/1.55  Index Deletion       : 0.00
% 2.76/1.55  Index Matching       : 0.00
% 2.76/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------
