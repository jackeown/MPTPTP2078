%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:19 EST 2020

% Result     : Theorem 2.97s
% Output     : CNFRefutation 3.28s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 212 expanded)
%              Number of leaves         :   26 (  79 expanded)
%              Depth                    :    9
%              Number of atoms          :  110 ( 504 expanded)
%              Number of equality atoms :   79 ( 381 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(c_40,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_193,plain,(
    ! [A_49,C_50,B_51] :
      ( r1_tarski(A_49,k2_xboole_0(C_50,B_51))
      | ~ r1_tarski(A_49,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_208,plain,(
    ! [A_49] :
      ( r1_tarski(A_49,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_49,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_193])).

tff(c_248,plain,(
    ! [B_57,A_58] :
      ( k1_tarski(B_57) = A_58
      | k1_xboole_0 = A_58
      | ~ r1_tarski(A_58,k1_tarski(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_372,plain,(
    ! [A_65] :
      ( k1_tarski('#skF_1') = A_65
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_208,c_248])).

tff(c_382,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_372])).

tff(c_383,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_396,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_66])).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_56,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_71,plain,(
    ! [A_33,B_34] : k4_xboole_0(A_33,k2_xboole_0(A_33,B_34)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_81,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_71])).

tff(c_394,plain,(
    k4_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_81])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_264,plain,(
    ! [B_57,A_3] :
      ( k1_tarski(B_57) = A_3
      | k1_xboole_0 = A_3
      | k4_xboole_0(A_3,k1_tarski(B_57)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_248])).

tff(c_847,plain,(
    ! [B_100,A_101] :
      ( k1_tarski(B_100) = A_101
      | A_101 = '#skF_3'
      | k4_xboole_0(A_101,k1_tarski(B_100)) != '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_383,c_383,c_264])).

tff(c_857,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_847])).

tff(c_868,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_396,c_56,c_857])).

tff(c_869,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_877,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_56])).

tff(c_875,plain,(
    k4_xboole_0('#skF_2','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_81])).

tff(c_263,plain,(
    ! [A_49] :
      ( k1_tarski('#skF_1') = A_49
      | k1_xboole_0 = A_49
      | ~ r1_tarski(A_49,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_208,c_248])).

tff(c_954,plain,(
    ! [A_105] :
      ( A_105 = '#skF_3'
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_869,c_263])).

tff(c_1021,plain,(
    ! [A_108] :
      ( A_108 = '#skF_3'
      | k1_xboole_0 = A_108
      | k4_xboole_0(A_108,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_954])).

tff(c_1024,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_1021])).

tff(c_1036,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_877,c_1024])).

tff(c_1037,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_1038,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_20,plain,(
    ! [A_14] : k4_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1039,plain,(
    ! [A_14] : k4_xboole_0('#skF_2',A_14) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_1038,c_20])).

tff(c_1103,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1038,c_8])).

tff(c_1169,plain,(
    ! [A_124,B_125] :
      ( k2_xboole_0(A_124,B_125) = B_125
      | ~ r1_tarski(A_124,B_125) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1280,plain,(
    ! [A_138,B_139] :
      ( k2_xboole_0(A_138,B_139) = B_139
      | k4_xboole_0(A_138,B_139) != '#skF_2' ) ),
    inference(resolution,[status(thm)],[c_1103,c_1169])).

tff(c_1293,plain,(
    ! [A_14] : k2_xboole_0('#skF_2',A_14) = A_14 ),
    inference(superposition,[status(thm),theory(equality)],[c_1039,c_1280])).

tff(c_1295,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1293,c_44])).

tff(c_1297,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1037,c_1295])).

tff(c_1298,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1299,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1349,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1299,c_42])).

tff(c_1304,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_44])).

tff(c_1510,plain,(
    ! [A_161,C_162,B_163] :
      ( r1_tarski(A_161,k2_xboole_0(C_162,B_163))
      | ~ r1_tarski(A_161,B_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1530,plain,(
    ! [A_161] :
      ( r1_tarski(A_161,'#skF_2')
      | ~ r1_tarski(A_161,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1304,c_1510])).

tff(c_1786,plain,(
    ! [B_180,A_181] :
      ( k1_tarski(B_180) = A_181
      | k1_xboole_0 = A_181
      | ~ r1_tarski(A_181,k1_tarski(B_180)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1793,plain,(
    ! [A_181] :
      ( k1_tarski('#skF_1') = A_181
      | k1_xboole_0 = A_181
      | ~ r1_tarski(A_181,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1299,c_1786])).

tff(c_1807,plain,(
    ! [A_182] :
      ( A_182 = '#skF_2'
      | k1_xboole_0 = A_182
      | ~ r1_tarski(A_182,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1299,c_1793])).

tff(c_1832,plain,(
    ! [A_183] :
      ( A_183 = '#skF_2'
      | k1_xboole_0 = A_183
      | ~ r1_tarski(A_183,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1530,c_1807])).

tff(c_1840,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_6,c_1832])).

tff(c_1845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1298,c_1349,c_1840])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:48:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.97/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.54  
% 3.28/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.55  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.28/1.55  
% 3.28/1.55  %Foreground sorts:
% 3.28/1.55  
% 3.28/1.55  
% 3.28/1.55  %Background operators:
% 3.28/1.55  
% 3.28/1.55  
% 3.28/1.55  %Foreground operators:
% 3.28/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.28/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.28/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.28/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.28/1.55  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.28/1.55  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.28/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.28/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.28/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.28/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.28/1.55  tff('#skF_2', type, '#skF_2': $i).
% 3.28/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.28/1.55  tff('#skF_1', type, '#skF_1': $i).
% 3.28/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.28/1.55  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.28/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.28/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.28/1.55  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.28/1.55  
% 3.28/1.56  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.28/1.56  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.28/1.56  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.28/1.56  tff(f_63, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.28/1.56  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.28/1.56  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.28/1.56  tff(f_49, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.28/1.56  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.28/1.56  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.56  tff(c_66, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 3.28/1.56  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.28/1.56  tff(c_44, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.56  tff(c_193, plain, (![A_49, C_50, B_51]: (r1_tarski(A_49, k2_xboole_0(C_50, B_51)) | ~r1_tarski(A_49, B_51))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.56  tff(c_208, plain, (![A_49]: (r1_tarski(A_49, k1_tarski('#skF_1')) | ~r1_tarski(A_49, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_193])).
% 3.28/1.56  tff(c_248, plain, (![B_57, A_58]: (k1_tarski(B_57)=A_58 | k1_xboole_0=A_58 | ~r1_tarski(A_58, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.28/1.56  tff(c_372, plain, (![A_65]: (k1_tarski('#skF_1')=A_65 | k1_xboole_0=A_65 | ~r1_tarski(A_65, '#skF_3'))), inference(resolution, [status(thm)], [c_208, c_248])).
% 3.28/1.56  tff(c_382, plain, (k1_tarski('#skF_1')='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_372])).
% 3.28/1.56  tff(c_383, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_382])).
% 3.28/1.56  tff(c_396, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_66])).
% 3.28/1.56  tff(c_38, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.56  tff(c_56, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 3.28/1.56  tff(c_71, plain, (![A_33, B_34]: (k4_xboole_0(A_33, k2_xboole_0(A_33, B_34))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.28/1.56  tff(c_81, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_44, c_71])).
% 3.28/1.56  tff(c_394, plain, (k4_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_383, c_81])).
% 3.28/1.56  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.28/1.56  tff(c_264, plain, (![B_57, A_3]: (k1_tarski(B_57)=A_3 | k1_xboole_0=A_3 | k4_xboole_0(A_3, k1_tarski(B_57))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_248])).
% 3.28/1.56  tff(c_847, plain, (![B_100, A_101]: (k1_tarski(B_100)=A_101 | A_101='#skF_3' | k4_xboole_0(A_101, k1_tarski(B_100))!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_383, c_383, c_264])).
% 3.28/1.56  tff(c_857, plain, (k1_tarski('#skF_1')='#skF_2' | '#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_394, c_847])).
% 3.28/1.56  tff(c_868, plain, $false, inference(negUnitSimplification, [status(thm)], [c_396, c_56, c_857])).
% 3.28/1.56  tff(c_869, plain, (k1_tarski('#skF_1')='#skF_3'), inference(splitRight, [status(thm)], [c_382])).
% 3.28/1.56  tff(c_877, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_869, c_56])).
% 3.28/1.56  tff(c_875, plain, (k4_xboole_0('#skF_2', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_869, c_81])).
% 3.28/1.56  tff(c_263, plain, (![A_49]: (k1_tarski('#skF_1')=A_49 | k1_xboole_0=A_49 | ~r1_tarski(A_49, '#skF_3'))), inference(resolution, [status(thm)], [c_208, c_248])).
% 3.28/1.56  tff(c_954, plain, (![A_105]: (A_105='#skF_3' | k1_xboole_0=A_105 | ~r1_tarski(A_105, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_869, c_263])).
% 3.28/1.56  tff(c_1021, plain, (![A_108]: (A_108='#skF_3' | k1_xboole_0=A_108 | k4_xboole_0(A_108, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_954])).
% 3.28/1.56  tff(c_1024, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_875, c_1021])).
% 3.28/1.56  tff(c_1036, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_877, c_1024])).
% 3.28/1.56  tff(c_1037, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.28/1.56  tff(c_1038, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.28/1.56  tff(c_20, plain, (![A_14]: (k4_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.28/1.56  tff(c_1039, plain, (![A_14]: (k4_xboole_0('#skF_2', A_14)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_1038, c_20])).
% 3.28/1.56  tff(c_1103, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1038, c_8])).
% 3.28/1.56  tff(c_1169, plain, (![A_124, B_125]: (k2_xboole_0(A_124, B_125)=B_125 | ~r1_tarski(A_124, B_125))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.28/1.56  tff(c_1280, plain, (![A_138, B_139]: (k2_xboole_0(A_138, B_139)=B_139 | k4_xboole_0(A_138, B_139)!='#skF_2')), inference(resolution, [status(thm)], [c_1103, c_1169])).
% 3.28/1.56  tff(c_1293, plain, (![A_14]: (k2_xboole_0('#skF_2', A_14)=A_14)), inference(superposition, [status(thm), theory('equality')], [c_1039, c_1280])).
% 3.28/1.56  tff(c_1295, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1293, c_44])).
% 3.28/1.56  tff(c_1297, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1037, c_1295])).
% 3.28/1.56  tff(c_1298, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.28/1.56  tff(c_1299, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 3.28/1.56  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.28/1.56  tff(c_1349, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1299, c_42])).
% 3.28/1.56  tff(c_1304, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_44])).
% 3.28/1.56  tff(c_1510, plain, (![A_161, C_162, B_163]: (r1_tarski(A_161, k2_xboole_0(C_162, B_163)) | ~r1_tarski(A_161, B_163))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.28/1.56  tff(c_1530, plain, (![A_161]: (r1_tarski(A_161, '#skF_2') | ~r1_tarski(A_161, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1304, c_1510])).
% 3.28/1.56  tff(c_1786, plain, (![B_180, A_181]: (k1_tarski(B_180)=A_181 | k1_xboole_0=A_181 | ~r1_tarski(A_181, k1_tarski(B_180)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.28/1.56  tff(c_1793, plain, (![A_181]: (k1_tarski('#skF_1')=A_181 | k1_xboole_0=A_181 | ~r1_tarski(A_181, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1299, c_1786])).
% 3.28/1.56  tff(c_1807, plain, (![A_182]: (A_182='#skF_2' | k1_xboole_0=A_182 | ~r1_tarski(A_182, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1299, c_1793])).
% 3.28/1.56  tff(c_1832, plain, (![A_183]: (A_183='#skF_2' | k1_xboole_0=A_183 | ~r1_tarski(A_183, '#skF_3'))), inference(resolution, [status(thm)], [c_1530, c_1807])).
% 3.28/1.56  tff(c_1840, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_6, c_1832])).
% 3.28/1.56  tff(c_1845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1298, c_1349, c_1840])).
% 3.28/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.28/1.56  
% 3.28/1.56  Inference rules
% 3.28/1.56  ----------------------
% 3.28/1.56  #Ref     : 0
% 3.28/1.56  #Sup     : 413
% 3.28/1.56  #Fact    : 0
% 3.28/1.56  #Define  : 0
% 3.28/1.56  #Split   : 4
% 3.28/1.56  #Chain   : 0
% 3.28/1.56  #Close   : 0
% 3.28/1.56  
% 3.28/1.56  Ordering : KBO
% 3.28/1.56  
% 3.28/1.56  Simplification rules
% 3.28/1.56  ----------------------
% 3.28/1.56  #Subsume      : 27
% 3.28/1.56  #Demod        : 166
% 3.28/1.56  #Tautology    : 307
% 3.28/1.56  #SimpNegUnit  : 14
% 3.28/1.56  #BackRed      : 27
% 3.28/1.56  
% 3.28/1.56  #Partial instantiations: 0
% 3.28/1.56  #Strategies tried      : 1
% 3.28/1.56  
% 3.28/1.56  Timing (in seconds)
% 3.28/1.56  ----------------------
% 3.28/1.56  Preprocessing        : 0.29
% 3.28/1.56  Parsing              : 0.15
% 3.28/1.56  CNF conversion       : 0.02
% 3.28/1.56  Main loop            : 0.45
% 3.28/1.56  Inferencing          : 0.17
% 3.28/1.56  Reduction            : 0.14
% 3.28/1.56  Demodulation         : 0.10
% 3.28/1.56  BG Simplification    : 0.02
% 3.28/1.56  Subsumption          : 0.08
% 3.28/1.56  Abstraction          : 0.02
% 3.28/1.56  MUC search           : 0.00
% 3.28/1.56  Cooper               : 0.00
% 3.28/1.56  Total                : 0.77
% 3.28/1.56  Index Insertion      : 0.00
% 3.28/1.56  Index Deletion       : 0.00
% 3.28/1.56  Index Matching       : 0.00
% 3.28/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
