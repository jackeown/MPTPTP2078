%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:19 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.97s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 107 expanded)
%              Number of leaves         :   35 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 124 expanded)
%              Number of equality atoms :   46 (  98 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_395,plain,(
    ! [A_104,B_105] : k3_xboole_0(k1_tarski(A_104),k2_tarski(A_104,B_105)) = k1_tarski(A_104) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_404,plain,(
    ! [A_4] : k3_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_tarski(A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_395])).

tff(c_422,plain,(
    ! [A_107,B_108] : k5_xboole_0(A_107,k3_xboole_0(A_107,B_108)) = k4_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_431,plain,(
    ! [A_4] : k5_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_404,c_422])).

tff(c_440,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_431])).

tff(c_30,plain,(
    ! [B_39] : k4_xboole_0(k1_tarski(B_39),k1_tarski(B_39)) != k1_tarski(B_39) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_452,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_30])).

tff(c_380,plain,(
    ! [A_102,B_103] :
      ( r1_tarski(k1_tarski(A_102),B_103)
      | ~ r2_hidden(A_102,B_103) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(B_35,A_34))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_392,plain,(
    ! [A_102,B_35] :
      ( k1_tarski(A_102) = k1_xboole_0
      | ~ r2_hidden(A_102,k2_zfmisc_1(B_35,k1_tarski(A_102))) ) ),
    inference(resolution,[status(thm)],[c_380,c_24])).

tff(c_523,plain,(
    ! [A_102,B_35] : ~ r2_hidden(A_102,k2_zfmisc_1(B_35,k1_tarski(A_102))) ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_392])).

tff(c_194,plain,(
    ! [A_72,B_73] : k3_xboole_0(k1_tarski(A_72),k2_tarski(A_72,B_73)) = k1_tarski(A_72) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_200,plain,(
    ! [A_72,B_73] : k5_xboole_0(k1_tarski(A_72),k1_tarski(A_72)) = k4_xboole_0(k1_tarski(A_72),k2_tarski(A_72,B_73)) ),
    inference(superposition,[status(thm),theory(equality)],[c_194,c_2])).

tff(c_210,plain,(
    ! [A_74,B_75] : k4_xboole_0(k1_tarski(A_74),k2_tarski(A_74,B_75)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_200])).

tff(c_217,plain,(
    ! [A_4] : k4_xboole_0(k1_tarski(A_4),k1_tarski(A_4)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_210])).

tff(c_220,plain,(
    ! [B_39] : k1_tarski(B_39) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_30])).

tff(c_167,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tarski(A_68),B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ! [A_34,B_35] :
      ( ~ r1_tarski(A_34,k2_zfmisc_1(A_34,B_35))
      | k1_xboole_0 = A_34 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_181,plain,(
    ! [A_68,B_35] :
      ( k1_tarski(A_68) = k1_xboole_0
      | ~ r2_hidden(A_68,k2_zfmisc_1(k1_tarski(A_68),B_35)) ) ),
    inference(resolution,[status(thm)],[c_167,c_26])).

tff(c_311,plain,(
    ! [A_68,B_35] : ~ r2_hidden(A_68,k2_zfmisc_1(k1_tarski(A_68),B_35)) ),
    inference(negUnitSimplification,[status(thm)],[c_220,c_181])).

tff(c_48,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_60,plain,(
    ! [A_51,B_52] : k1_mcart_1(k4_tarski(A_51,B_52)) = A_51 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_69,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_60])).

tff(c_85,plain,(
    ! [A_54,B_55] : k2_mcart_1(k4_tarski(A_54,B_55)) = B_55 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_94,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_85])).

tff(c_46,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_101,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_94,c_46])).

tff(c_102,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_104,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_48])).

tff(c_229,plain,(
    ! [C_78,D_79] : r2_hidden(k4_tarski(C_78,D_79),k2_zfmisc_1(k1_tarski(C_78),k1_tarski(D_79))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_232,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_229])).

tff(c_313,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_311,c_232])).

tff(c_314,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_326,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_48])).

tff(c_519,plain,(
    ! [C_120,D_121] : r2_hidden(k4_tarski(C_120,D_121),k2_zfmisc_1(k1_tarski(C_120),k1_tarski(D_121))) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_522,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1(k1_tarski('#skF_2'),k1_tarski('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_519])).

tff(c_525,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_523,c_522])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:19:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.70  
% 2.97/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.70  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_setfam_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.97/1.70  
% 2.97/1.70  %Foreground sorts:
% 2.97/1.70  
% 2.97/1.70  
% 2.97/1.70  %Background operators:
% 2.97/1.70  
% 2.97/1.70  
% 2.97/1.70  %Foreground operators:
% 2.97/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.97/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.97/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.97/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.97/1.70  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.97/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.97/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.97/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.97/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.97/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.97/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.97/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.97/1.70  tff('#skF_2', type, '#skF_2': $i).
% 2.97/1.70  tff('#skF_3', type, '#skF_3': $i).
% 2.97/1.70  tff('#skF_1', type, '#skF_1': $i).
% 2.97/1.70  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.70  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.97/1.70  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.97/1.70  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.97/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.97/1.70  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.97/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.97/1.70  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.97/1.70  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.97/1.70  
% 2.97/1.72  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.97/1.72  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.97/1.72  tff(f_55, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.97/1.72  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.97/1.72  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.97/1.72  tff(f_47, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.97/1.72  tff(f_53, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.97/1.72  tff(f_82, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.97/1.72  tff(f_72, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.97/1.72  tff(f_66, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.97/1.72  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.97/1.72  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.97/1.72  tff(c_395, plain, (![A_104, B_105]: (k3_xboole_0(k1_tarski(A_104), k2_tarski(A_104, B_105))=k1_tarski(A_104))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.72  tff(c_404, plain, (![A_4]: (k3_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_tarski(A_4))), inference(superposition, [status(thm), theory('equality')], [c_6, c_395])).
% 2.97/1.72  tff(c_422, plain, (![A_107, B_108]: (k5_xboole_0(A_107, k3_xboole_0(A_107, B_108))=k4_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.72  tff(c_431, plain, (![A_4]: (k5_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_404, c_422])).
% 2.97/1.72  tff(c_440, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_431])).
% 2.97/1.72  tff(c_30, plain, (![B_39]: (k4_xboole_0(k1_tarski(B_39), k1_tarski(B_39))!=k1_tarski(B_39))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.97/1.72  tff(c_452, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_440, c_30])).
% 2.97/1.72  tff(c_380, plain, (![A_102, B_103]: (r1_tarski(k1_tarski(A_102), B_103) | ~r2_hidden(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.72  tff(c_24, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(B_35, A_34)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.72  tff(c_392, plain, (![A_102, B_35]: (k1_tarski(A_102)=k1_xboole_0 | ~r2_hidden(A_102, k2_zfmisc_1(B_35, k1_tarski(A_102))))), inference(resolution, [status(thm)], [c_380, c_24])).
% 2.97/1.72  tff(c_523, plain, (![A_102, B_35]: (~r2_hidden(A_102, k2_zfmisc_1(B_35, k1_tarski(A_102))))), inference(negUnitSimplification, [status(thm)], [c_452, c_392])).
% 2.97/1.72  tff(c_194, plain, (![A_72, B_73]: (k3_xboole_0(k1_tarski(A_72), k2_tarski(A_72, B_73))=k1_tarski(A_72))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.97/1.72  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.97/1.72  tff(c_200, plain, (![A_72, B_73]: (k5_xboole_0(k1_tarski(A_72), k1_tarski(A_72))=k4_xboole_0(k1_tarski(A_72), k2_tarski(A_72, B_73)))), inference(superposition, [status(thm), theory('equality')], [c_194, c_2])).
% 2.97/1.72  tff(c_210, plain, (![A_74, B_75]: (k4_xboole_0(k1_tarski(A_74), k2_tarski(A_74, B_75))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_200])).
% 2.97/1.72  tff(c_217, plain, (![A_4]: (k4_xboole_0(k1_tarski(A_4), k1_tarski(A_4))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_210])).
% 2.97/1.72  tff(c_220, plain, (![B_39]: (k1_tarski(B_39)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_217, c_30])).
% 2.97/1.72  tff(c_167, plain, (![A_68, B_69]: (r1_tarski(k1_tarski(A_68), B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.97/1.72  tff(c_26, plain, (![A_34, B_35]: (~r1_tarski(A_34, k2_zfmisc_1(A_34, B_35)) | k1_xboole_0=A_34)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.97/1.72  tff(c_181, plain, (![A_68, B_35]: (k1_tarski(A_68)=k1_xboole_0 | ~r2_hidden(A_68, k2_zfmisc_1(k1_tarski(A_68), B_35)))), inference(resolution, [status(thm)], [c_167, c_26])).
% 2.97/1.72  tff(c_311, plain, (![A_68, B_35]: (~r2_hidden(A_68, k2_zfmisc_1(k1_tarski(A_68), B_35)))), inference(negUnitSimplification, [status(thm)], [c_220, c_181])).
% 2.97/1.72  tff(c_48, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.97/1.72  tff(c_60, plain, (![A_51, B_52]: (k1_mcart_1(k4_tarski(A_51, B_52))=A_51)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.97/1.72  tff(c_69, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_48, c_60])).
% 2.97/1.72  tff(c_85, plain, (![A_54, B_55]: (k2_mcart_1(k4_tarski(A_54, B_55))=B_55)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.97/1.72  tff(c_94, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_48, c_85])).
% 2.97/1.72  tff(c_46, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.97/1.72  tff(c_101, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_94, c_46])).
% 2.97/1.72  tff(c_102, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_101])).
% 2.97/1.72  tff(c_104, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_48])).
% 2.97/1.72  tff(c_229, plain, (![C_78, D_79]: (r2_hidden(k4_tarski(C_78, D_79), k2_zfmisc_1(k1_tarski(C_78), k1_tarski(D_79))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.97/1.72  tff(c_232, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_104, c_229])).
% 2.97/1.72  tff(c_313, plain, $false, inference(negUnitSimplification, [status(thm)], [c_311, c_232])).
% 2.97/1.72  tff(c_314, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_101])).
% 2.97/1.72  tff(c_326, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_314, c_48])).
% 2.97/1.72  tff(c_519, plain, (![C_120, D_121]: (r2_hidden(k4_tarski(C_120, D_121), k2_zfmisc_1(k1_tarski(C_120), k1_tarski(D_121))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.97/1.72  tff(c_522, plain, (r2_hidden('#skF_1', k2_zfmisc_1(k1_tarski('#skF_2'), k1_tarski('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_326, c_519])).
% 2.97/1.72  tff(c_525, plain, $false, inference(negUnitSimplification, [status(thm)], [c_523, c_522])).
% 2.97/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.97/1.72  
% 2.97/1.72  Inference rules
% 2.97/1.72  ----------------------
% 2.97/1.72  #Ref     : 0
% 2.97/1.72  #Sup     : 116
% 2.97/1.72  #Fact    : 0
% 2.97/1.72  #Define  : 0
% 2.97/1.72  #Split   : 1
% 2.97/1.72  #Chain   : 0
% 2.97/1.72  #Close   : 0
% 2.97/1.72  
% 2.97/1.72  Ordering : KBO
% 2.97/1.72  
% 2.97/1.72  Simplification rules
% 2.97/1.72  ----------------------
% 2.97/1.72  #Subsume      : 0
% 2.97/1.72  #Demod        : 26
% 2.97/1.72  #Tautology    : 96
% 2.97/1.72  #SimpNegUnit  : 9
% 2.97/1.72  #BackRed      : 8
% 2.97/1.72  
% 2.97/1.72  #Partial instantiations: 0
% 2.97/1.72  #Strategies tried      : 1
% 2.97/1.72  
% 2.97/1.72  Timing (in seconds)
% 2.97/1.72  ----------------------
% 2.97/1.73  Preprocessing        : 0.52
% 2.97/1.73  Parsing              : 0.27
% 2.97/1.73  CNF conversion       : 0.03
% 2.97/1.73  Main loop            : 0.38
% 2.97/1.73  Inferencing          : 0.15
% 2.97/1.73  Reduction            : 0.12
% 2.97/1.73  Demodulation         : 0.09
% 2.97/1.73  BG Simplification    : 0.03
% 2.97/1.73  Subsumption          : 0.04
% 2.97/1.73  Abstraction          : 0.03
% 2.97/1.73  MUC search           : 0.00
% 2.97/1.73  Cooper               : 0.00
% 2.97/1.73  Total                : 0.95
% 2.97/1.73  Index Insertion      : 0.00
% 2.97/1.73  Index Deletion       : 0.00
% 2.97/1.73  Index Matching       : 0.00
% 2.97/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------
