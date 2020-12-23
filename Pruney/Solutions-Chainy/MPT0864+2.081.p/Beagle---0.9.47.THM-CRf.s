%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:19 EST 2020

% Result     : Theorem 2.35s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 105 expanded)
%              Number of leaves         :   32 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   67 ( 130 expanded)
%              Number of equality atoms :   48 ( 108 expanded)
%              Maximal formula depth    :   15 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( r1_tarski(D,k1_enumset1(A,B,C))
    <=> ~ ( D != k1_xboole_0
          & D != k1_tarski(A)
          & D != k1_tarski(B)
          & D != k1_tarski(C)
          & D != k2_tarski(A,B)
          & D != k2_tarski(B,C)
          & D != k2_tarski(A,C)
          & D != k1_enumset1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_zfmisc_1)).

tff(f_95,negated_conjecture,(
    ~ ! [A] :
        ( ? [B,C] : A = k4_tarski(B,C)
       => ( A != k1_mcart_1(A)
          & A != k2_mcart_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_mcart_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_353,plain,(
    ! [A_123,B_124] : k1_enumset1(A_123,A_123,B_124) = k2_tarski(A_123,B_124) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [A_30,B_31,C_32] : r1_tarski(k1_tarski(A_30),k1_enumset1(A_30,B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_389,plain,(
    ! [A_130,B_131] : r1_tarski(k1_tarski(A_130),k2_tarski(A_130,B_131)) ),
    inference(superposition,[status(thm),theory(equality)],[c_353,c_38])).

tff(c_392,plain,(
    ! [A_5] : r1_tarski(k1_tarski(A_5),k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_389])).

tff(c_162,plain,(
    ! [A_66,B_67] : k1_enumset1(A_66,A_66,B_67) = k2_tarski(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [C_32,A_30,B_31] : r1_tarski(k1_tarski(C_32),k1_enumset1(A_30,B_31,C_32)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_183,plain,(
    ! [B_71,A_72] : r1_tarski(k1_tarski(B_71),k2_tarski(A_72,B_71)) ),
    inference(superposition,[status(thm),theory(equality)],[c_162,c_34])).

tff(c_186,plain,(
    ! [A_5] : r1_tarski(k1_tarski(A_5),k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_183])).

tff(c_52,plain,(
    k4_tarski('#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_57,plain,(
    ! [A_42,B_43] : k1_mcart_1(k4_tarski(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_66,plain,(
    k1_mcart_1('#skF_1') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_57])).

tff(c_74,plain,(
    ! [A_46,B_47] : k2_mcart_1(k4_tarski(A_46,B_47)) = B_47 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_83,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_74])).

tff(c_50,plain,
    ( k2_mcart_1('#skF_1') = '#skF_1'
    | k1_mcart_1('#skF_1') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_100,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_83,c_50])).

tff(c_101,plain,(
    '#skF_2' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_103,plain,(
    k4_tarski('#skF_1','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_52])).

tff(c_242,plain,(
    ! [A_92,B_93] : k2_xboole_0(k1_tarski(A_92),k1_tarski(B_93)) = k2_tarski(A_92,B_93) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),B_37) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_263,plain,(
    ! [A_94,B_95] : k2_tarski(A_94,B_95) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_44])).

tff(c_265,plain,(
    ! [A_5] : k1_tarski(A_5) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_263])).

tff(c_287,plain,(
    ! [A_101,B_102] : k2_zfmisc_1(k1_tarski(A_101),k1_tarski(B_102)) = k1_tarski(k4_tarski(A_101,B_102)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_22,plain,(
    ! [A_28,B_29] :
      ( ~ r1_tarski(A_28,k2_zfmisc_1(A_28,B_29))
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_296,plain,(
    ! [A_101,B_102] :
      ( ~ r1_tarski(k1_tarski(A_101),k1_tarski(k4_tarski(A_101,B_102)))
      | k1_tarski(A_101) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_22])).

tff(c_317,plain,(
    ! [A_108,B_109] : ~ r1_tarski(k1_tarski(A_108),k1_tarski(k4_tarski(A_108,B_109))) ),
    inference(negUnitSimplification,[status(thm)],[c_265,c_296])).

tff(c_320,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_317])).

tff(c_323,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_320])).

tff(c_324,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_327,plain,(
    k4_tarski('#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_324,c_52])).

tff(c_466,plain,(
    ! [A_150,B_151] : k2_xboole_0(k1_tarski(A_150),k1_tarski(B_151)) = k2_tarski(A_150,B_151) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_496,plain,(
    ! [A_155,B_156] : k2_tarski(A_155,B_156) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_44])).

tff(c_498,plain,(
    ! [A_5] : k1_tarski(A_5) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_496])).

tff(c_511,plain,(
    ! [A_159,B_160] : k2_zfmisc_1(k1_tarski(A_159),k1_tarski(B_160)) = k1_tarski(k4_tarski(A_159,B_160)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_20,plain,(
    ! [A_28,B_29] :
      ( ~ r1_tarski(A_28,k2_zfmisc_1(B_29,A_28))
      | k1_xboole_0 = A_28 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_517,plain,(
    ! [B_160,A_159] :
      ( ~ r1_tarski(k1_tarski(B_160),k1_tarski(k4_tarski(A_159,B_160)))
      | k1_tarski(B_160) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_511,c_20])).

tff(c_537,plain,(
    ! [B_164,A_165] : ~ r1_tarski(k1_tarski(B_164),k1_tarski(k4_tarski(A_165,B_164))) ),
    inference(negUnitSimplification,[status(thm)],[c_498,c_517])).

tff(c_540,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_537])).

tff(c_543,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_540])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:06:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.35/1.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.33  
% 2.35/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.35/1.33  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_mcart_1 > k1_tarski > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.35/1.33  
% 2.35/1.33  %Foreground sorts:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Background operators:
% 2.35/1.33  
% 2.35/1.33  
% 2.35/1.33  %Foreground operators:
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.35/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.35/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.35/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.35/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.35/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.35/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.35/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.35/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.35/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.35/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.35/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.35/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.35/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.35/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.35/1.33  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.35/1.33  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.35/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.35/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.35/1.33  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.35/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.35/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.35/1.33  
% 2.63/1.35  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.63/1.35  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.63/1.35  tff(f_76, axiom, (![A, B, C, D]: (r1_tarski(D, k1_enumset1(A, B, C)) <=> ~(((((((~(D = k1_xboole_0) & ~(D = k1_tarski(A))) & ~(D = k1_tarski(B))) & ~(D = k1_tarski(C))) & ~(D = k2_tarski(A, B))) & ~(D = k2_tarski(B, C))) & ~(D = k2_tarski(A, C))) & ~(D = k1_enumset1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_zfmisc_1)).
% 2.63/1.35  tff(f_95, negated_conjecture, ~(![A]: ((?[B, C]: (A = k4_tarski(B, C))) => (~(A = k1_mcart_1(A)) & ~(A = k2_mcart_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_mcart_1)).
% 2.63/1.35  tff(f_85, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.63/1.35  tff(f_29, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.63/1.35  tff(f_81, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.63/1.35  tff(f_78, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 2.63/1.35  tff(f_49, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 2.63/1.35  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.35  tff(c_353, plain, (![A_123, B_124]: (k1_enumset1(A_123, A_123, B_124)=k2_tarski(A_123, B_124))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.35  tff(c_38, plain, (![A_30, B_31, C_32]: (r1_tarski(k1_tarski(A_30), k1_enumset1(A_30, B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.35  tff(c_389, plain, (![A_130, B_131]: (r1_tarski(k1_tarski(A_130), k2_tarski(A_130, B_131)))), inference(superposition, [status(thm), theory('equality')], [c_353, c_38])).
% 2.63/1.35  tff(c_392, plain, (![A_5]: (r1_tarski(k1_tarski(A_5), k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_389])).
% 2.63/1.35  tff(c_162, plain, (![A_66, B_67]: (k1_enumset1(A_66, A_66, B_67)=k2_tarski(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.35  tff(c_34, plain, (![C_32, A_30, B_31]: (r1_tarski(k1_tarski(C_32), k1_enumset1(A_30, B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.35  tff(c_183, plain, (![B_71, A_72]: (r1_tarski(k1_tarski(B_71), k2_tarski(A_72, B_71)))), inference(superposition, [status(thm), theory('equality')], [c_162, c_34])).
% 2.63/1.35  tff(c_186, plain, (![A_5]: (r1_tarski(k1_tarski(A_5), k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_183])).
% 2.63/1.35  tff(c_52, plain, (k4_tarski('#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.63/1.35  tff(c_57, plain, (![A_42, B_43]: (k1_mcart_1(k4_tarski(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.63/1.35  tff(c_66, plain, (k1_mcart_1('#skF_1')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_52, c_57])).
% 2.63/1.35  tff(c_74, plain, (![A_46, B_47]: (k2_mcart_1(k4_tarski(A_46, B_47))=B_47)), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.63/1.35  tff(c_83, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_52, c_74])).
% 2.63/1.35  tff(c_50, plain, (k2_mcart_1('#skF_1')='#skF_1' | k1_mcart_1('#skF_1')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.63/1.35  tff(c_100, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_83, c_50])).
% 2.63/1.35  tff(c_101, plain, ('#skF_2'='#skF_1'), inference(splitLeft, [status(thm)], [c_100])).
% 2.63/1.35  tff(c_103, plain, (k4_tarski('#skF_1', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_52])).
% 2.63/1.35  tff(c_242, plain, (![A_92, B_93]: (k2_xboole_0(k1_tarski(A_92), k1_tarski(B_93))=k2_tarski(A_92, B_93))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.35  tff(c_44, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.63/1.35  tff(c_263, plain, (![A_94, B_95]: (k2_tarski(A_94, B_95)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_242, c_44])).
% 2.63/1.35  tff(c_265, plain, (![A_5]: (k1_tarski(A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_263])).
% 2.63/1.35  tff(c_287, plain, (![A_101, B_102]: (k2_zfmisc_1(k1_tarski(A_101), k1_tarski(B_102))=k1_tarski(k4_tarski(A_101, B_102)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.63/1.35  tff(c_22, plain, (![A_28, B_29]: (~r1_tarski(A_28, k2_zfmisc_1(A_28, B_29)) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.35  tff(c_296, plain, (![A_101, B_102]: (~r1_tarski(k1_tarski(A_101), k1_tarski(k4_tarski(A_101, B_102))) | k1_tarski(A_101)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_287, c_22])).
% 2.63/1.35  tff(c_317, plain, (![A_108, B_109]: (~r1_tarski(k1_tarski(A_108), k1_tarski(k4_tarski(A_108, B_109))))), inference(negUnitSimplification, [status(thm)], [c_265, c_296])).
% 2.63/1.35  tff(c_320, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_103, c_317])).
% 2.63/1.35  tff(c_323, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_186, c_320])).
% 2.63/1.35  tff(c_324, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_100])).
% 2.63/1.35  tff(c_327, plain, (k4_tarski('#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_324, c_52])).
% 2.63/1.35  tff(c_466, plain, (![A_150, B_151]: (k2_xboole_0(k1_tarski(A_150), k1_tarski(B_151))=k2_tarski(A_150, B_151))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.35  tff(c_496, plain, (![A_155, B_156]: (k2_tarski(A_155, B_156)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_466, c_44])).
% 2.63/1.35  tff(c_498, plain, (![A_5]: (k1_tarski(A_5)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_496])).
% 2.63/1.35  tff(c_511, plain, (![A_159, B_160]: (k2_zfmisc_1(k1_tarski(A_159), k1_tarski(B_160))=k1_tarski(k4_tarski(A_159, B_160)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.63/1.35  tff(c_20, plain, (![A_28, B_29]: (~r1_tarski(A_28, k2_zfmisc_1(B_29, A_28)) | k1_xboole_0=A_28)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.63/1.35  tff(c_517, plain, (![B_160, A_159]: (~r1_tarski(k1_tarski(B_160), k1_tarski(k4_tarski(A_159, B_160))) | k1_tarski(B_160)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_511, c_20])).
% 2.63/1.35  tff(c_537, plain, (![B_164, A_165]: (~r1_tarski(k1_tarski(B_164), k1_tarski(k4_tarski(A_165, B_164))))), inference(negUnitSimplification, [status(thm)], [c_498, c_517])).
% 2.63/1.35  tff(c_540, plain, (~r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_327, c_537])).
% 2.63/1.35  tff(c_543, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_392, c_540])).
% 2.63/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.35  
% 2.63/1.35  Inference rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Ref     : 0
% 2.63/1.35  #Sup     : 119
% 2.63/1.35  #Fact    : 0
% 2.63/1.35  #Define  : 0
% 2.63/1.35  #Split   : 1
% 2.63/1.35  #Chain   : 0
% 2.63/1.35  #Close   : 0
% 2.63/1.35  
% 2.63/1.35  Ordering : KBO
% 2.63/1.35  
% 2.63/1.35  Simplification rules
% 2.63/1.35  ----------------------
% 2.63/1.35  #Subsume      : 2
% 2.63/1.35  #Demod        : 52
% 2.63/1.35  #Tautology    : 88
% 2.63/1.35  #SimpNegUnit  : 4
% 2.63/1.35  #BackRed      : 6
% 2.63/1.35  
% 2.63/1.35  #Partial instantiations: 0
% 2.63/1.35  #Strategies tried      : 1
% 2.63/1.35  
% 2.63/1.35  Timing (in seconds)
% 2.63/1.35  ----------------------
% 2.63/1.35  Preprocessing        : 0.32
% 2.63/1.35  Parsing              : 0.17
% 2.63/1.35  CNF conversion       : 0.02
% 2.63/1.35  Main loop            : 0.26
% 2.63/1.35  Inferencing          : 0.10
% 2.63/1.35  Reduction            : 0.09
% 2.63/1.35  Demodulation         : 0.07
% 2.63/1.35  BG Simplification    : 0.02
% 2.63/1.35  Subsumption          : 0.04
% 2.63/1.35  Abstraction          : 0.02
% 2.63/1.35  MUC search           : 0.00
% 2.63/1.35  Cooper               : 0.00
% 2.63/1.35  Total                : 0.62
% 2.63/1.35  Index Insertion      : 0.00
% 2.63/1.35  Index Deletion       : 0.00
% 2.63/1.35  Index Matching       : 0.00
% 2.63/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
