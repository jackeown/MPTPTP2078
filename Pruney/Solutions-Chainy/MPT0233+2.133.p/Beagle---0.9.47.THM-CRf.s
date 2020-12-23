%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:38 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 215 expanded)
%              Number of leaves         :   19 (  79 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 450 expanded)
%              Number of equality atoms :   57 ( 296 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_28,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_30,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_37,plain,(
    ! [A_22] : k2_tarski(A_22,A_22) = k1_tarski(A_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [B_14,C_15] : r1_tarski(k1_xboole_0,k2_tarski(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,k1_tarski(A_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_37,c_24])).

tff(c_32,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_148,plain,(
    ! [B_51,C_52,A_53] :
      ( k2_tarski(B_51,C_52) = A_53
      | k1_tarski(C_52) = A_53
      | k1_tarski(B_51) = A_53
      | k1_xboole_0 = A_53
      | ~ r1_tarski(A_53,k2_tarski(B_51,C_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_168,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_148])).

tff(c_190,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_22,plain,(
    ! [B_14,C_15] : r1_tarski(k1_tarski(B_14),k2_tarski(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_68,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_82,plain,(
    ! [B_14,C_15] :
      ( k2_tarski(B_14,C_15) = k1_tarski(B_14)
      | ~ r1_tarski(k2_tarski(B_14,C_15),k1_tarski(B_14)) ) ),
    inference(resolution,[status(thm)],[c_22,c_68])).

tff(c_200,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_1')
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_82])).

tff(c_222,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_190,c_200])).

tff(c_8,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_105,plain,(
    ! [C_38,A_39,B_40] :
      ( C_38 = A_39
      | B_40 = A_39
      | ~ r1_tarski(k1_tarski(A_39),k2_tarski(B_40,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_114,plain,(
    ! [A_39,A_3] :
      ( A_39 = A_3
      | A_39 = A_3
      | ~ r1_tarski(k1_tarski(A_39),k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_105])).

tff(c_241,plain,(
    ! [A_3] :
      ( A_3 = '#skF_1'
      | A_3 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_114])).

tff(c_274,plain,(
    ! [A_56] : A_56 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_241])).

tff(c_355,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_274,c_30])).

tff(c_356,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_358,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_356])).

tff(c_81,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_68])).

tff(c_147,plain,(
    ~ r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_359,plain,(
    ~ r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_147])).

tff(c_363,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_359])).

tff(c_364,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_356])).

tff(c_366,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_364])).

tff(c_390,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_22])).

tff(c_409,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_390,c_114])).

tff(c_416,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_409])).

tff(c_417,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_364])).

tff(c_443,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_417,c_22])).

tff(c_480,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_443,c_114])).

tff(c_487,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_480])).

tff(c_488,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_540,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_22])).

tff(c_26,plain,(
    ! [C_18,A_16,B_17] :
      ( C_18 = A_16
      | B_17 = A_16
      | ~ r1_tarski(k1_tarski(A_16),k2_tarski(B_17,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_559,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_540,c_26])).

tff(c_565,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_559])).

tff(c_20,plain,(
    ! [C_15,B_14] : r1_tarski(k1_tarski(C_15),k2_tarski(B_14,C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_543,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_20])).

tff(c_730,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_543])).

tff(c_736,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_730,c_26])).

tff(c_742,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_736])).

tff(c_568,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_488])).

tff(c_767,plain,(
    k2_tarski('#skF_1','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_742,c_8,c_742,c_568])).

tff(c_787,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_767,c_22])).

tff(c_805,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_787,c_114])).

tff(c_811,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_805])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:49:56 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  
% 2.84/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.40  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.84/1.40  
% 2.84/1.40  %Foreground sorts:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Background operators:
% 2.84/1.40  
% 2.84/1.40  
% 2.84/1.40  %Foreground operators:
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.84/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.84/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.84/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.40  
% 2.84/1.41  tff(f_73, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.84/1.41  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.84/1.41  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.84/1.41  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 2.84/1.41  tff(f_63, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.84/1.41  tff(c_28, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.41  tff(c_30, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.41  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.41  tff(c_37, plain, (![A_22]: (k2_tarski(A_22, A_22)=k1_tarski(A_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.41  tff(c_24, plain, (![B_14, C_15]: (r1_tarski(k1_xboole_0, k2_tarski(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.41  tff(c_42, plain, (![A_22]: (r1_tarski(k1_xboole_0, k1_tarski(A_22)))), inference(superposition, [status(thm), theory('equality')], [c_37, c_24])).
% 2.84/1.41  tff(c_32, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.84/1.41  tff(c_148, plain, (![B_51, C_52, A_53]: (k2_tarski(B_51, C_52)=A_53 | k1_tarski(C_52)=A_53 | k1_tarski(B_51)=A_53 | k1_xboole_0=A_53 | ~r1_tarski(A_53, k2_tarski(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.41  tff(c_168, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_148])).
% 2.84/1.41  tff(c_190, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_168])).
% 2.84/1.41  tff(c_22, plain, (![B_14, C_15]: (r1_tarski(k1_tarski(B_14), k2_tarski(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.41  tff(c_68, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.84/1.41  tff(c_82, plain, (![B_14, C_15]: (k2_tarski(B_14, C_15)=k1_tarski(B_14) | ~r1_tarski(k2_tarski(B_14, C_15), k1_tarski(B_14)))), inference(resolution, [status(thm)], [c_22, c_68])).
% 2.84/1.41  tff(c_200, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_1') | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_190, c_82])).
% 2.84/1.41  tff(c_222, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_42, c_190, c_200])).
% 2.84/1.41  tff(c_8, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.84/1.41  tff(c_105, plain, (![C_38, A_39, B_40]: (C_38=A_39 | B_40=A_39 | ~r1_tarski(k1_tarski(A_39), k2_tarski(B_40, C_38)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.84/1.41  tff(c_114, plain, (![A_39, A_3]: (A_39=A_3 | A_39=A_3 | ~r1_tarski(k1_tarski(A_39), k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_105])).
% 2.84/1.41  tff(c_241, plain, (![A_3]: (A_3='#skF_1' | A_3='#skF_1' | ~r1_tarski(k1_xboole_0, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_222, c_114])).
% 2.84/1.41  tff(c_274, plain, (![A_56]: (A_56='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_241])).
% 2.84/1.41  tff(c_355, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_274, c_30])).
% 2.84/1.41  tff(c_356, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_168])).
% 2.84/1.41  tff(c_358, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_356])).
% 2.84/1.41  tff(c_81, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2') | ~r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_68])).
% 2.84/1.41  tff(c_147, plain, (~r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_81])).
% 2.84/1.41  tff(c_359, plain, (~r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_358, c_147])).
% 2.84/1.41  tff(c_363, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_359])).
% 2.84/1.41  tff(c_364, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_356])).
% 2.84/1.41  tff(c_366, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_364])).
% 2.84/1.41  tff(c_390, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_366, c_22])).
% 2.84/1.41  tff(c_409, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_390, c_114])).
% 2.84/1.41  tff(c_416, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_409])).
% 2.84/1.41  tff(c_417, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_364])).
% 2.84/1.41  tff(c_443, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_417, c_22])).
% 2.84/1.41  tff(c_480, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_443, c_114])).
% 2.84/1.41  tff(c_487, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_480])).
% 2.84/1.41  tff(c_488, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_81])).
% 2.84/1.41  tff(c_540, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_22])).
% 2.84/1.41  tff(c_26, plain, (![C_18, A_16, B_17]: (C_18=A_16 | B_17=A_16 | ~r1_tarski(k1_tarski(A_16), k2_tarski(B_17, C_18)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.84/1.41  tff(c_559, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_540, c_26])).
% 2.84/1.41  tff(c_565, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_30, c_559])).
% 2.84/1.41  tff(c_20, plain, (![C_15, B_14]: (r1_tarski(k1_tarski(C_15), k2_tarski(B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.84/1.41  tff(c_543, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_488, c_20])).
% 2.84/1.41  tff(c_730, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_565, c_543])).
% 2.84/1.41  tff(c_736, plain, ('#skF_3'='#skF_4' | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_730, c_26])).
% 2.84/1.41  tff(c_742, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_736])).
% 2.84/1.41  tff(c_568, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_565, c_488])).
% 2.84/1.41  tff(c_767, plain, (k2_tarski('#skF_1', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_742, c_8, c_742, c_568])).
% 2.84/1.41  tff(c_787, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_767, c_22])).
% 2.84/1.41  tff(c_805, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_787, c_114])).
% 2.84/1.41  tff(c_811, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_805])).
% 2.84/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.84/1.41  
% 2.84/1.41  Inference rules
% 2.84/1.41  ----------------------
% 2.84/1.41  #Ref     : 0
% 2.84/1.41  #Sup     : 221
% 2.84/1.41  #Fact    : 0
% 2.84/1.41  #Define  : 0
% 2.84/1.41  #Split   : 5
% 2.84/1.41  #Chain   : 0
% 2.84/1.41  #Close   : 0
% 2.84/1.42  
% 2.84/1.42  Ordering : KBO
% 2.84/1.42  
% 2.84/1.42  Simplification rules
% 2.84/1.42  ----------------------
% 2.84/1.42  #Subsume      : 18
% 2.84/1.42  #Demod        : 115
% 2.84/1.42  #Tautology    : 78
% 2.84/1.42  #SimpNegUnit  : 6
% 2.84/1.42  #BackRed      : 24
% 2.84/1.42  
% 2.84/1.42  #Partial instantiations: 49
% 2.84/1.42  #Strategies tried      : 1
% 2.84/1.42  
% 2.84/1.42  Timing (in seconds)
% 2.84/1.42  ----------------------
% 2.84/1.42  Preprocessing        : 0.31
% 2.84/1.42  Parsing              : 0.16
% 2.84/1.42  CNF conversion       : 0.02
% 2.84/1.42  Main loop            : 0.36
% 2.84/1.42  Inferencing          : 0.13
% 2.84/1.42  Reduction            : 0.11
% 2.84/1.42  Demodulation         : 0.08
% 2.84/1.42  BG Simplification    : 0.02
% 2.84/1.42  Subsumption          : 0.07
% 2.84/1.42  Abstraction          : 0.02
% 2.84/1.42  MUC search           : 0.00
% 2.84/1.42  Cooper               : 0.00
% 2.84/1.42  Total                : 0.70
% 2.84/1.42  Index Insertion      : 0.00
% 2.84/1.42  Index Deletion       : 0.00
% 2.84/1.42  Index Matching       : 0.00
% 2.84/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
