%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:26 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.04s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 178 expanded)
%              Number of leaves         :   20 (  66 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 383 expanded)
%              Number of equality atoms :   61 ( 288 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_24,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_19] : k2_tarski(A_19,A_19) = k1_tarski(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ! [B_12,C_13] : r1_tarski(k1_xboole_0,k2_tarski(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_35,plain,(
    ! [A_19] : r1_tarski(k1_xboole_0,k1_tarski(A_19)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_249,plain,(
    ! [B_52,C_53,A_54] :
      ( k2_tarski(B_52,C_53) = A_54
      | k1_tarski(C_53) = A_54
      | k1_tarski(B_52) = A_54
      | k1_xboole_0 = A_54
      | ~ r1_tarski(A_54,k2_tarski(B_52,C_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_270,plain,
    ( k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_249])).

tff(c_289,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_270])).

tff(c_18,plain,(
    ! [B_12,C_13] : r1_tarski(k1_tarski(B_12),k2_tarski(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_103,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_129,plain,(
    ! [B_12,C_13] : k2_xboole_0(k1_tarski(B_12),k2_tarski(B_12,C_13)) = k2_tarski(B_12,C_13) ),
    inference(resolution,[status(thm)],[c_18,c_103])).

tff(c_312,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k2_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_289,c_129])).

tff(c_336,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_312])).

tff(c_370,plain,(
    k2_xboole_0(k1_xboole_0,k1_tarski('#skF_1')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_336])).

tff(c_130,plain,(
    ! [A_19] : k2_xboole_0(k1_xboole_0,k1_tarski(A_19)) = k1_tarski(A_19) ),
    inference(resolution,[status(thm)],[c_35,c_103])).

tff(c_396,plain,(
    k1_tarski('#skF_1') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_130])).

tff(c_212,plain,(
    ! [C_45,A_46,B_47] :
      ( C_45 = A_46
      | B_47 = A_46
      | ~ r1_tarski(k1_tarski(A_46),k2_tarski(B_47,C_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_221,plain,(
    ! [A_5,A_46] :
      ( A_5 = A_46
      | A_5 = A_46
      | ~ r1_tarski(k1_tarski(A_46),k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_212])).

tff(c_415,plain,(
    ! [A_5] :
      ( A_5 = '#skF_1'
      | A_5 = '#skF_1'
      | ~ r1_tarski(k1_xboole_0,k1_tarski(A_5)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_396,c_221])).

tff(c_481,plain,(
    ! [A_58] : A_58 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_415])).

tff(c_612,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_26])).

tff(c_613,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_270])).

tff(c_615,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_613])).

tff(c_16,plain,(
    ! [C_13,B_12] : r1_tarski(k1_tarski(C_13),k2_tarski(B_12,C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_650,plain,(
    r1_tarski(k1_tarski('#skF_4'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_16])).

tff(c_22,plain,(
    ! [C_16,A_14,B_15] :
      ( C_16 = A_14
      | B_15 = A_14
      | ~ r1_tarski(k1_tarski(A_14),k2_tarski(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_673,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_650,c_22])).

tff(c_680,plain,(
    '#skF_2' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_673])).

tff(c_653,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_615,c_18])).

tff(c_687,plain,
    ( '#skF_2' = '#skF_3'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_653,c_22])).

tff(c_694,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_687])).

tff(c_705,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_694])).

tff(c_698,plain,(
    k2_tarski('#skF_3','#skF_4') = k2_tarski('#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_615])).

tff(c_711,plain,(
    k2_tarski('#skF_1','#skF_4') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_705,c_698])).

tff(c_746,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_711,c_18])).

tff(c_767,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_746,c_221])).

tff(c_775,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_767])).

tff(c_776,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_613])).

tff(c_778,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_776])).

tff(c_818,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_778,c_18])).

tff(c_838,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_818,c_221])).

tff(c_846,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_26,c_838])).

tff(c_847,plain,(
    k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_776])).

tff(c_888,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_847,c_18])).

tff(c_909,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_888,c_221])).

tff(c_917,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_24,c_909])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.49  
% 3.04/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.50  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.04/1.50  
% 3.04/1.50  %Foreground sorts:
% 3.04/1.50  
% 3.04/1.50  
% 3.04/1.50  %Background operators:
% 3.04/1.50  
% 3.04/1.50  
% 3.04/1.50  %Foreground operators:
% 3.04/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.04/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.04/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.04/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.04/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.04/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.04/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.04/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.04/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.04/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.04/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.04/1.50  tff('#skF_4', type, '#skF_4': $i).
% 3.04/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.04/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.04/1.50  
% 3.04/1.51  tff(f_71, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.04/1.51  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.04/1.51  tff(f_52, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.04/1.51  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.04/1.51  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.04/1.51  tff(f_61, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.04/1.51  tff(c_24, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.51  tff(c_26, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.51  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.51  tff(c_30, plain, (![A_19]: (k2_tarski(A_19, A_19)=k1_tarski(A_19))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.04/1.51  tff(c_20, plain, (![B_12, C_13]: (r1_tarski(k1_xboole_0, k2_tarski(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.04/1.51  tff(c_35, plain, (![A_19]: (r1_tarski(k1_xboole_0, k1_tarski(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_20])).
% 3.04/1.51  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.04/1.51  tff(c_28, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.04/1.51  tff(c_249, plain, (![B_52, C_53, A_54]: (k2_tarski(B_52, C_53)=A_54 | k1_tarski(C_53)=A_54 | k1_tarski(B_52)=A_54 | k1_xboole_0=A_54 | ~r1_tarski(A_54, k2_tarski(B_52, C_53)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.04/1.51  tff(c_270, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_249])).
% 3.04/1.51  tff(c_289, plain, (k2_tarski('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_270])).
% 3.04/1.51  tff(c_18, plain, (![B_12, C_13]: (r1_tarski(k1_tarski(B_12), k2_tarski(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.04/1.51  tff(c_103, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.04/1.51  tff(c_129, plain, (![B_12, C_13]: (k2_xboole_0(k1_tarski(B_12), k2_tarski(B_12, C_13))=k2_tarski(B_12, C_13))), inference(resolution, [status(thm)], [c_18, c_103])).
% 3.04/1.51  tff(c_312, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k2_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_289, c_129])).
% 3.04/1.51  tff(c_336, plain, (k2_xboole_0(k1_tarski('#skF_1'), k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_289, c_312])).
% 3.04/1.51  tff(c_370, plain, (k2_xboole_0(k1_xboole_0, k1_tarski('#skF_1'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2, c_336])).
% 3.04/1.51  tff(c_130, plain, (![A_19]: (k2_xboole_0(k1_xboole_0, k1_tarski(A_19))=k1_tarski(A_19))), inference(resolution, [status(thm)], [c_35, c_103])).
% 3.04/1.51  tff(c_396, plain, (k1_tarski('#skF_1')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_370, c_130])).
% 3.04/1.51  tff(c_212, plain, (![C_45, A_46, B_47]: (C_45=A_46 | B_47=A_46 | ~r1_tarski(k1_tarski(A_46), k2_tarski(B_47, C_45)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.51  tff(c_221, plain, (![A_5, A_46]: (A_5=A_46 | A_5=A_46 | ~r1_tarski(k1_tarski(A_46), k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_212])).
% 3.04/1.51  tff(c_415, plain, (![A_5]: (A_5='#skF_1' | A_5='#skF_1' | ~r1_tarski(k1_xboole_0, k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_396, c_221])).
% 3.04/1.51  tff(c_481, plain, (![A_58]: (A_58='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_35, c_415])).
% 3.04/1.51  tff(c_612, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_481, c_26])).
% 3.04/1.51  tff(c_613, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_270])).
% 3.04/1.51  tff(c_615, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_613])).
% 3.04/1.51  tff(c_16, plain, (![C_13, B_12]: (r1_tarski(k1_tarski(C_13), k2_tarski(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.04/1.51  tff(c_650, plain, (r1_tarski(k1_tarski('#skF_4'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_16])).
% 3.04/1.51  tff(c_22, plain, (![C_16, A_14, B_15]: (C_16=A_14 | B_15=A_14 | ~r1_tarski(k1_tarski(A_14), k2_tarski(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.04/1.51  tff(c_673, plain, ('#skF_2'='#skF_4' | '#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_650, c_22])).
% 3.04/1.51  tff(c_680, plain, ('#skF_2'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_24, c_673])).
% 3.04/1.51  tff(c_653, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_615, c_18])).
% 3.04/1.51  tff(c_687, plain, ('#skF_2'='#skF_3' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_653, c_22])).
% 3.04/1.51  tff(c_694, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_26, c_687])).
% 3.04/1.51  tff(c_705, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_680, c_694])).
% 3.04/1.51  tff(c_698, plain, (k2_tarski('#skF_3', '#skF_4')=k2_tarski('#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_680, c_615])).
% 3.04/1.51  tff(c_711, plain, (k2_tarski('#skF_1', '#skF_4')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_705, c_698])).
% 3.04/1.51  tff(c_746, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_711, c_18])).
% 3.04/1.51  tff(c_767, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_746, c_221])).
% 3.04/1.51  tff(c_775, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_767])).
% 3.04/1.51  tff(c_776, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_613])).
% 3.04/1.51  tff(c_778, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_776])).
% 3.04/1.51  tff(c_818, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_778, c_18])).
% 3.04/1.51  tff(c_838, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_818, c_221])).
% 3.04/1.51  tff(c_846, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_26, c_838])).
% 3.04/1.51  tff(c_847, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_776])).
% 3.04/1.51  tff(c_888, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_847, c_18])).
% 3.04/1.51  tff(c_909, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_888, c_221])).
% 3.04/1.51  tff(c_917, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_24, c_909])).
% 3.04/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.04/1.51  
% 3.04/1.51  Inference rules
% 3.04/1.51  ----------------------
% 3.04/1.51  #Ref     : 0
% 3.04/1.51  #Sup     : 249
% 3.04/1.51  #Fact    : 0
% 3.04/1.51  #Define  : 0
% 3.04/1.51  #Split   : 3
% 3.04/1.51  #Chain   : 0
% 3.04/1.51  #Close   : 0
% 3.04/1.51  
% 3.04/1.51  Ordering : KBO
% 3.04/1.51  
% 3.04/1.51  Simplification rules
% 3.04/1.51  ----------------------
% 3.04/1.51  #Subsume      : 17
% 3.04/1.51  #Demod        : 160
% 3.04/1.51  #Tautology    : 129
% 3.04/1.51  #SimpNegUnit  : 5
% 3.04/1.51  #BackRed      : 21
% 3.04/1.51  
% 3.04/1.51  #Partial instantiations: 31
% 3.04/1.51  #Strategies tried      : 1
% 3.04/1.51  
% 3.04/1.51  Timing (in seconds)
% 3.04/1.51  ----------------------
% 3.04/1.51  Preprocessing        : 0.31
% 3.04/1.51  Parsing              : 0.16
% 3.04/1.51  CNF conversion       : 0.02
% 3.04/1.51  Main loop            : 0.39
% 3.04/1.51  Inferencing          : 0.14
% 3.04/1.51  Reduction            : 0.14
% 3.04/1.52  Demodulation         : 0.11
% 3.04/1.52  BG Simplification    : 0.02
% 3.04/1.52  Subsumption          : 0.07
% 3.04/1.52  Abstraction          : 0.02
% 3.04/1.52  MUC search           : 0.00
% 3.04/1.52  Cooper               : 0.00
% 3.04/1.52  Total                : 0.73
% 3.04/1.52  Index Insertion      : 0.00
% 3.04/1.52  Index Deletion       : 0.00
% 3.04/1.52  Index Matching       : 0.00
% 3.04/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
