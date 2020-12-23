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
% DateTime   : Thu Dec  3 09:48:59 EST 2020

% Result     : Theorem 2.57s
% Output     : CNFRefutation 2.57s
% Verified   : 
% Statistics : Number of formulae       :   62 (  80 expanded)
%              Number of leaves         :   29 (  38 expanded)
%              Depth                    :   13
%              Number of atoms          :   64 (  91 expanded)
%              Number of equality atoms :   51 (  71 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k2_xboole_0(k1_tarski(A),k2_tarski(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t42_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( A != B
        & A != C
        & k4_xboole_0(k1_enumset1(A,B,C),k1_tarski(A)) != k2_tarski(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t136_enumset1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(c_16,plain,(
    ! [A_11] : k3_xboole_0(A_11,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_18,plain,(
    ! [A_12] : k4_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_175,plain,(
    ! [A_55,B_56] : k4_xboole_0(A_55,k4_xboole_0(A_55,B_56)) = k3_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_193,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k3_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_175])).

tff(c_197,plain,(
    ! [A_12] : k4_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_193])).

tff(c_36,plain,(
    ! [B_29] : k4_xboole_0(k1_tarski(B_29),k1_tarski(B_29)) != k1_tarski(B_29) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_198,plain,(
    ! [B_29] : k1_tarski(B_29) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_197,c_36])).

tff(c_44,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_122,plain,(
    ! [A_40,B_41] :
      ( k4_xboole_0(A_40,B_41) = k1_xboole_0
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_44,c_122])).

tff(c_42,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_40,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_252,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k4_xboole_0(B_63,A_62)) = k2_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_261,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_252])).

tff(c_273,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_261])).

tff(c_267,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_1')) = k5_xboole_0(k2_tarski('#skF_2','#skF_3'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_252])).

tff(c_365,plain,(
    k2_xboole_0(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_1')) = k2_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_267])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_369,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) = k2_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_365,c_2])).

tff(c_30,plain,(
    ! [A_22,B_23,C_24] : k2_xboole_0(k1_tarski(A_22),k2_tarski(B_23,C_24)) = k1_enumset1(A_22,B_23,C_24) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_565,plain,(
    k1_enumset1('#skF_1','#skF_2','#skF_3') = k2_tarski('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_30])).

tff(c_699,plain,(
    ! [A_86,B_87,C_88] :
      ( k4_xboole_0(k1_enumset1(A_86,B_87,C_88),k1_tarski(A_86)) = k2_tarski(B_87,C_88)
      | C_88 = A_86
      | B_87 = A_86 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_725,plain,
    ( k4_xboole_0(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_1')) = k2_tarski('#skF_2','#skF_3')
    | '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_699])).

tff(c_734,plain,(
    k4_xboole_0(k2_tarski('#skF_2','#skF_3'),k1_tarski('#skF_1')) = k2_tarski('#skF_2','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_725])).

tff(c_147,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(A_51,B_52)
      | k4_xboole_0(A_51,B_52) != A_51 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_240,plain,(
    ! [B_60,A_61] :
      ( r1_xboole_0(B_60,A_61)
      | k4_xboole_0(A_61,B_60) != A_61 ) ),
    inference(resolution,[status(thm)],[c_147,c_10])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = A_15
      | ~ r1_xboole_0(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_250,plain,(
    ! [B_60,A_61] :
      ( k4_xboole_0(B_60,A_61) = B_60
      | k4_xboole_0(A_61,B_60) != A_61 ) ),
    inference(resolution,[status(thm)],[c_240,c_22])).

tff(c_788,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_734,c_250])).

tff(c_810,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_788])).

tff(c_812,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_198,c_810])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.21/0.34  % DateTime   : Tue Dec  1 18:58:42 EST 2020
% 0.21/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.57/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.44  
% 2.57/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.45  %$ r1_xboole_0 > r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.57/1.45  
% 2.57/1.45  %Foreground sorts:
% 2.57/1.45  
% 2.57/1.45  
% 2.57/1.45  %Background operators:
% 2.57/1.45  
% 2.57/1.45  
% 2.57/1.45  %Foreground operators:
% 2.57/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.57/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.57/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.57/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.57/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.57/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.57/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.57/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.57/1.45  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.57/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.57/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.57/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.57/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.57/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.57/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.57/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.57/1.45  
% 2.57/1.46  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.57/1.46  tff(f_45, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.57/1.46  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.57/1.46  tff(f_74, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.57/1.46  tff(f_84, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.57/1.46  tff(f_41, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.57/1.46  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.57/1.46  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.57/1.46  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.57/1.46  tff(f_65, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k2_xboole_0(k1_tarski(A), k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t42_enumset1)).
% 2.57/1.46  tff(f_63, axiom, (![A, B, C]: ~((~(A = B) & ~(A = C)) & ~(k4_xboole_0(k1_enumset1(A, B, C), k1_tarski(A)) = k2_tarski(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t136_enumset1)).
% 2.57/1.46  tff(f_51, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.57/1.46  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.57/1.46  tff(c_16, plain, (![A_11]: (k3_xboole_0(A_11, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.57/1.46  tff(c_18, plain, (![A_12]: (k4_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.57/1.46  tff(c_175, plain, (![A_55, B_56]: (k4_xboole_0(A_55, k4_xboole_0(A_55, B_56))=k3_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.57/1.46  tff(c_193, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k3_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_18, c_175])).
% 2.57/1.46  tff(c_197, plain, (![A_12]: (k4_xboole_0(A_12, A_12)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_193])).
% 2.57/1.46  tff(c_36, plain, (![B_29]: (k4_xboole_0(k1_tarski(B_29), k1_tarski(B_29))!=k1_tarski(B_29))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.57/1.46  tff(c_198, plain, (![B_29]: (k1_tarski(B_29)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_197, c_36])).
% 2.57/1.46  tff(c_44, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.57/1.46  tff(c_122, plain, (![A_40, B_41]: (k4_xboole_0(A_40, B_41)=k1_xboole_0 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.57/1.46  tff(c_126, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_44, c_122])).
% 2.57/1.46  tff(c_42, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.57/1.46  tff(c_40, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.57/1.46  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.57/1.46  tff(c_252, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k4_xboole_0(B_63, A_62))=k2_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.57/1.46  tff(c_261, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_197, c_252])).
% 2.57/1.46  tff(c_273, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_261])).
% 2.57/1.46  tff(c_267, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_1'))=k5_xboole_0(k2_tarski('#skF_2', '#skF_3'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_126, c_252])).
% 2.57/1.46  tff(c_365, plain, (k2_xboole_0(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_1'))=k2_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_267])).
% 2.57/1.46  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.57/1.46  tff(c_369, plain, (k2_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))=k2_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_365, c_2])).
% 2.57/1.46  tff(c_30, plain, (![A_22, B_23, C_24]: (k2_xboole_0(k1_tarski(A_22), k2_tarski(B_23, C_24))=k1_enumset1(A_22, B_23, C_24))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.57/1.46  tff(c_565, plain, (k1_enumset1('#skF_1', '#skF_2', '#skF_3')=k2_tarski('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_369, c_30])).
% 2.57/1.46  tff(c_699, plain, (![A_86, B_87, C_88]: (k4_xboole_0(k1_enumset1(A_86, B_87, C_88), k1_tarski(A_86))=k2_tarski(B_87, C_88) | C_88=A_86 | B_87=A_86)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.57/1.46  tff(c_725, plain, (k4_xboole_0(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_1'))=k2_tarski('#skF_2', '#skF_3') | '#skF_3'='#skF_1' | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_565, c_699])).
% 2.57/1.46  tff(c_734, plain, (k4_xboole_0(k2_tarski('#skF_2', '#skF_3'), k1_tarski('#skF_1'))=k2_tarski('#skF_2', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_725])).
% 2.57/1.46  tff(c_147, plain, (![A_51, B_52]: (r1_xboole_0(A_51, B_52) | k4_xboole_0(A_51, B_52)!=A_51)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.46  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.57/1.46  tff(c_240, plain, (![B_60, A_61]: (r1_xboole_0(B_60, A_61) | k4_xboole_0(A_61, B_60)!=A_61)), inference(resolution, [status(thm)], [c_147, c_10])).
% 2.57/1.46  tff(c_22, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=A_15 | ~r1_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.57/1.46  tff(c_250, plain, (![B_60, A_61]: (k4_xboole_0(B_60, A_61)=B_60 | k4_xboole_0(A_61, B_60)!=A_61)), inference(resolution, [status(thm)], [c_240, c_22])).
% 2.57/1.46  tff(c_788, plain, (k4_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_734, c_250])).
% 2.57/1.46  tff(c_810, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_126, c_788])).
% 2.57/1.46  tff(c_812, plain, $false, inference(negUnitSimplification, [status(thm)], [c_198, c_810])).
% 2.57/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.57/1.46  
% 2.57/1.46  Inference rules
% 2.57/1.46  ----------------------
% 2.57/1.46  #Ref     : 0
% 2.57/1.46  #Sup     : 190
% 2.57/1.46  #Fact    : 0
% 2.57/1.46  #Define  : 0
% 2.57/1.46  #Split   : 0
% 2.57/1.46  #Chain   : 0
% 2.57/1.46  #Close   : 0
% 2.57/1.46  
% 2.57/1.46  Ordering : KBO
% 2.57/1.46  
% 2.57/1.46  Simplification rules
% 2.57/1.46  ----------------------
% 2.57/1.46  #Subsume      : 13
% 2.57/1.46  #Demod        : 44
% 2.57/1.46  #Tautology    : 119
% 2.57/1.46  #SimpNegUnit  : 9
% 2.57/1.46  #BackRed      : 3
% 2.57/1.46  
% 2.57/1.46  #Partial instantiations: 0
% 2.57/1.46  #Strategies tried      : 1
% 2.57/1.46  
% 2.57/1.46  Timing (in seconds)
% 2.57/1.46  ----------------------
% 2.57/1.46  Preprocessing        : 0.32
% 2.57/1.46  Parsing              : 0.18
% 2.57/1.46  CNF conversion       : 0.02
% 2.57/1.46  Main loop            : 0.29
% 2.57/1.46  Inferencing          : 0.11
% 2.57/1.46  Reduction            : 0.10
% 2.57/1.46  Demodulation         : 0.07
% 2.57/1.46  BG Simplification    : 0.02
% 2.57/1.46  Subsumption          : 0.05
% 2.57/1.46  Abstraction          : 0.01
% 2.57/1.46  MUC search           : 0.00
% 2.57/1.46  Cooper               : 0.00
% 2.57/1.46  Total                : 0.64
% 2.57/1.46  Index Insertion      : 0.00
% 2.57/1.46  Index Deletion       : 0.00
% 2.57/1.46  Index Matching       : 0.00
% 2.57/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
