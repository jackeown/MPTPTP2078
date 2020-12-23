%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:08 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   67 (  96 expanded)
%              Number of leaves         :   31 (  44 expanded)
%              Depth                    :   10
%              Number of atoms          :   60 ( 123 expanded)
%              Number of equality atoms :   58 ( 121 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_47,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t93_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_28,plain,(
    ! [B_34] : k2_zfmisc_1(k1_xboole_0,B_34) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_117,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_140,plain,(
    ! [B_53,A_54] :
      ( k1_xboole_0 = B_53
      | k1_xboole_0 = A_54
      | k2_zfmisc_1(A_54,B_53) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_143,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_140])).

tff(c_152,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_143])).

tff(c_30,plain,(
    ! [B_36] : k4_xboole_0(k1_tarski(B_36),k1_tarski(B_36)) != k1_tarski(B_36) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_165,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_30])).

tff(c_172,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_152,c_165])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_34,plain,(
    ! [A_37] : k3_tarski(k1_tarski(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_22,plain,(
    ! [A_32] : k2_enumset1(A_32,A_32,A_32,A_32) = k1_tarski(A_32) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [A_55,B_56,C_57] : k2_enumset1(A_55,A_55,B_56,C_57) = k1_enumset1(A_55,B_56,C_57) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_217,plain,(
    ! [A_60] : k1_enumset1(A_60,A_60,A_60) = k1_tarski(A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_174])).

tff(c_12,plain,(
    ! [A_10,B_11] : k1_enumset1(A_10,A_10,B_11) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_233,plain,(
    ! [A_61] : k2_tarski(A_61,A_61) = k1_tarski(A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_12])).

tff(c_36,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_239,plain,(
    ! [A_61] : k3_tarski(k1_tarski(A_61)) = k2_xboole_0(A_61,A_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_36])).

tff(c_244,plain,(
    ! [A_61] : k2_xboole_0(A_61,A_61) = A_61 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_239])).

tff(c_257,plain,(
    ! [A_63,B_64] : k5_xboole_0(k5_xboole_0(A_63,B_64),k2_xboole_0(A_63,B_64)) = k3_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_281,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,k2_xboole_0(A_7,A_7)) = k3_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_257])).

tff(c_286,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = k3_xboole_0(A_65,A_65) ),
    inference(demodulation,[status(thm),theory(equality)],[c_244,c_281])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_302,plain,(
    k3_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_4])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_328,plain,(
    k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_302,c_2])).

tff(c_331,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_328])).

tff(c_333,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_172,c_331])).

tff(c_334,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_349,plain,(
    ! [B_68,A_69] :
      ( k1_xboole_0 = B_68
      | k1_xboole_0 = A_69
      | k2_zfmisc_1(A_69,B_68) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_352,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_334,c_349])).

tff(c_361,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_352])).

tff(c_335,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_366,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_361,c_335])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_366])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n001.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:38:15 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  
% 2.09/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.26  %$ k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.26  
% 2.09/1.26  %Foreground sorts:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Background operators:
% 2.09/1.26  
% 2.09/1.26  
% 2.09/1.26  %Foreground operators:
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.26  
% 2.09/1.27  tff(f_53, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.09/1.27  tff(f_72, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.09/1.27  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.09/1.27  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.09/1.27  tff(f_60, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.09/1.27  tff(f_47, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 2.09/1.27  tff(f_39, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 2.09/1.27  tff(f_37, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.09/1.27  tff(f_62, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t93_zfmisc_1)).
% 2.09/1.27  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 2.09/1.27  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.09/1.27  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.09/1.27  tff(c_28, plain, (![B_34]: (k2_zfmisc_1(k1_xboole_0, B_34)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.27  tff(c_40, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.27  tff(c_38, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.09/1.27  tff(c_117, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 2.09/1.27  tff(c_140, plain, (![B_53, A_54]: (k1_xboole_0=B_53 | k1_xboole_0=A_54 | k2_zfmisc_1(A_54, B_53)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.27  tff(c_143, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_117, c_140])).
% 2.09/1.27  tff(c_152, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_143])).
% 2.09/1.27  tff(c_30, plain, (![B_36]: (k4_xboole_0(k1_tarski(B_36), k1_tarski(B_36))!=k1_tarski(B_36))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.27  tff(c_165, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_152, c_30])).
% 2.09/1.27  tff(c_172, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_152, c_152, c_165])).
% 2.09/1.27  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.27  tff(c_34, plain, (![A_37]: (k3_tarski(k1_tarski(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.09/1.27  tff(c_22, plain, (![A_32]: (k2_enumset1(A_32, A_32, A_32, A_32)=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.27  tff(c_174, plain, (![A_55, B_56, C_57]: (k2_enumset1(A_55, A_55, B_56, C_57)=k1_enumset1(A_55, B_56, C_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.27  tff(c_217, plain, (![A_60]: (k1_enumset1(A_60, A_60, A_60)=k1_tarski(A_60))), inference(superposition, [status(thm), theory('equality')], [c_22, c_174])).
% 2.09/1.27  tff(c_12, plain, (![A_10, B_11]: (k1_enumset1(A_10, A_10, B_11)=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.27  tff(c_233, plain, (![A_61]: (k2_tarski(A_61, A_61)=k1_tarski(A_61))), inference(superposition, [status(thm), theory('equality')], [c_217, c_12])).
% 2.09/1.27  tff(c_36, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.27  tff(c_239, plain, (![A_61]: (k3_tarski(k1_tarski(A_61))=k2_xboole_0(A_61, A_61))), inference(superposition, [status(thm), theory('equality')], [c_233, c_36])).
% 2.09/1.27  tff(c_244, plain, (![A_61]: (k2_xboole_0(A_61, A_61)=A_61)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_239])).
% 2.09/1.27  tff(c_257, plain, (![A_63, B_64]: (k5_xboole_0(k5_xboole_0(A_63, B_64), k2_xboole_0(A_63, B_64))=k3_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.27  tff(c_281, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, k2_xboole_0(A_7, A_7))=k3_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_8, c_257])).
% 2.09/1.27  tff(c_286, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=k3_xboole_0(A_65, A_65))), inference(demodulation, [status(thm), theory('equality')], [c_244, c_281])).
% 2.09/1.27  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.27  tff(c_302, plain, (k3_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_286, c_4])).
% 2.09/1.27  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.27  tff(c_328, plain, (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_302, c_2])).
% 2.09/1.27  tff(c_331, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_328])).
% 2.09/1.27  tff(c_333, plain, $false, inference(negUnitSimplification, [status(thm)], [c_172, c_331])).
% 2.09/1.27  tff(c_334, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.09/1.27  tff(c_349, plain, (![B_68, A_69]: (k1_xboole_0=B_68 | k1_xboole_0=A_69 | k2_zfmisc_1(A_69, B_68)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.09/1.27  tff(c_352, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_334, c_349])).
% 2.09/1.27  tff(c_361, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_352])).
% 2.09/1.27  tff(c_335, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 2.09/1.27  tff(c_366, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_361, c_335])).
% 2.09/1.27  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_366])).
% 2.09/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.27  
% 2.09/1.27  Inference rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Ref     : 0
% 2.09/1.27  #Sup     : 80
% 2.09/1.27  #Fact    : 0
% 2.09/1.27  #Define  : 0
% 2.09/1.27  #Split   : 1
% 2.09/1.27  #Chain   : 0
% 2.09/1.27  #Close   : 0
% 2.09/1.27  
% 2.09/1.27  Ordering : KBO
% 2.09/1.27  
% 2.09/1.27  Simplification rules
% 2.09/1.27  ----------------------
% 2.09/1.27  #Subsume      : 1
% 2.09/1.27  #Demod        : 16
% 2.09/1.27  #Tautology    : 57
% 2.09/1.27  #SimpNegUnit  : 3
% 2.09/1.27  #BackRed      : 3
% 2.09/1.27  
% 2.09/1.27  #Partial instantiations: 0
% 2.09/1.27  #Strategies tried      : 1
% 2.09/1.27  
% 2.09/1.27  Timing (in seconds)
% 2.09/1.27  ----------------------
% 2.09/1.28  Preprocessing        : 0.32
% 2.09/1.28  Parsing              : 0.17
% 2.09/1.28  CNF conversion       : 0.02
% 2.09/1.28  Main loop            : 0.19
% 2.09/1.28  Inferencing          : 0.07
% 2.09/1.28  Reduction            : 0.06
% 2.09/1.28  Demodulation         : 0.04
% 2.09/1.28  BG Simplification    : 0.02
% 2.09/1.28  Subsumption          : 0.03
% 2.09/1.28  Abstraction          : 0.01
% 2.09/1.28  MUC search           : 0.00
% 2.09/1.28  Cooper               : 0.00
% 2.09/1.28  Total                : 0.54
% 2.09/1.28  Index Insertion      : 0.00
% 2.09/1.28  Index Deletion       : 0.00
% 2.09/1.28  Index Matching       : 0.00
% 2.09/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
