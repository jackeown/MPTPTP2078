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
% DateTime   : Thu Dec  3 09:50:22 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 101 expanded)
%              Number of leaves         :   20 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   80 ( 225 expanded)
%              Number of equality atoms :   51 ( 190 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_24,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_41,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_30,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_48,plain,(
    ! [A_25,B_26] : r1_tarski(A_25,k2_xboole_0(A_25,B_26)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_48])).

tff(c_105,plain,(
    ! [B_38,A_39] :
      ( k1_tarski(B_38) = A_39
      | k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k1_tarski(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_111,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_51,c_105])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_41,c_111])).

tff(c_124,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_146,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(A_43,B_44)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_152,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_146])).

tff(c_187,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(A_51,k2_xboole_0(C_52,B_53))
      | ~ r1_tarski(A_51,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_190,plain,(
    ! [A_51] :
      ( r1_tarski(A_51,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_51,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_187])).

tff(c_125,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_16,plain,(
    ! [B_19,A_18] :
      ( k1_tarski(B_19) = A_18
      | k1_xboole_0 = A_18
      | ~ r1_tarski(A_18,k1_tarski(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_196,plain,(
    ! [B_55,A_56] :
      ( k1_tarski(B_55) = A_56
      | A_56 = '#skF_2'
      | ~ r1_tarski(A_56,k1_tarski(B_55)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_16])).

tff(c_212,plain,(
    ! [A_57] :
      ( k1_tarski('#skF_1') = A_57
      | A_57 = '#skF_2'
      | ~ r1_tarski(A_57,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_190,c_196])).

tff(c_216,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_152,c_212])).

tff(c_219,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_216])).

tff(c_233,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_219,c_30])).

tff(c_235,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_233])).

tff(c_237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_124,c_235])).

tff(c_238,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_239,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_273,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_239,c_28])).

tff(c_248,plain,(
    ! [A_61,B_62] : r1_tarski(A_61,k2_xboole_0(A_61,B_62)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_251,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_248])).

tff(c_253,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_30])).

tff(c_312,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,k2_xboole_0(C_71,B_72))
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_315,plain,(
    ! [A_70] :
      ( r1_tarski(A_70,'#skF_2')
      | ~ r1_tarski(A_70,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_312])).

tff(c_329,plain,(
    ! [B_77,A_78] :
      ( k1_tarski(B_77) = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,k1_tarski(B_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_336,plain,(
    ! [A_78] :
      ( k1_tarski('#skF_1') = A_78
      | k1_xboole_0 = A_78
      | ~ r1_tarski(A_78,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_329])).

tff(c_345,plain,(
    ! [A_79] :
      ( A_79 = '#skF_2'
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_336])).

tff(c_365,plain,(
    ! [A_80] :
      ( A_80 = '#skF_2'
      | k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_315,c_345])).

tff(c_369,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_251,c_365])).

tff(c_373,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_238,c_273,c_369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:58:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.23  
% 1.89/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.89/1.23  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.23  
% 1.89/1.23  %Foreground sorts:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Background operators:
% 1.89/1.23  
% 1.89/1.23  
% 1.89/1.23  %Foreground operators:
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.23  
% 2.11/1.24  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.11/1.24  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.11/1.24  tff(f_47, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.11/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.11/1.24  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.11/1.24  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.24  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 2.11/1.24  tff(c_24, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.24  tff(c_41, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.11/1.24  tff(c_30, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.24  tff(c_48, plain, (![A_25, B_26]: (r1_tarski(A_25, k2_xboole_0(A_25, B_26)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.24  tff(c_51, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_48])).
% 2.11/1.24  tff(c_105, plain, (![B_38, A_39]: (k1_tarski(B_38)=A_39 | k1_xboole_0=A_39 | ~r1_tarski(A_39, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.24  tff(c_111, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_51, c_105])).
% 2.11/1.24  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_41, c_111])).
% 2.11/1.24  tff(c_124, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_26])).
% 2.11/1.24  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.24  tff(c_146, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(A_43, B_44)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.24  tff(c_152, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_146])).
% 2.11/1.24  tff(c_187, plain, (![A_51, C_52, B_53]: (r1_tarski(A_51, k2_xboole_0(C_52, B_53)) | ~r1_tarski(A_51, B_53))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.24  tff(c_190, plain, (![A_51]: (r1_tarski(A_51, k1_tarski('#skF_1')) | ~r1_tarski(A_51, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_30, c_187])).
% 2.11/1.24  tff(c_125, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 2.11/1.24  tff(c_16, plain, (![B_19, A_18]: (k1_tarski(B_19)=A_18 | k1_xboole_0=A_18 | ~r1_tarski(A_18, k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.24  tff(c_196, plain, (![B_55, A_56]: (k1_tarski(B_55)=A_56 | A_56='#skF_2' | ~r1_tarski(A_56, k1_tarski(B_55)))), inference(demodulation, [status(thm), theory('equality')], [c_125, c_16])).
% 2.11/1.24  tff(c_212, plain, (![A_57]: (k1_tarski('#skF_1')=A_57 | A_57='#skF_2' | ~r1_tarski(A_57, '#skF_3'))), inference(resolution, [status(thm)], [c_190, c_196])).
% 2.11/1.24  tff(c_216, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_152, c_212])).
% 2.11/1.24  tff(c_219, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_124, c_216])).
% 2.11/1.24  tff(c_233, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_219, c_30])).
% 2.11/1.24  tff(c_235, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_233])).
% 2.11/1.24  tff(c_237, plain, $false, inference(negUnitSimplification, [status(thm)], [c_124, c_235])).
% 2.11/1.24  tff(c_238, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.11/1.24  tff(c_239, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.11/1.24  tff(c_28, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.11/1.24  tff(c_273, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_239, c_28])).
% 2.11/1.24  tff(c_248, plain, (![A_61, B_62]: (r1_tarski(A_61, k2_xboole_0(A_61, B_62)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.24  tff(c_251, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_248])).
% 2.11/1.24  tff(c_253, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_239, c_30])).
% 2.11/1.24  tff(c_312, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, k2_xboole_0(C_71, B_72)) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.24  tff(c_315, plain, (![A_70]: (r1_tarski(A_70, '#skF_2') | ~r1_tarski(A_70, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_253, c_312])).
% 2.11/1.24  tff(c_329, plain, (![B_77, A_78]: (k1_tarski(B_77)=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, k1_tarski(B_77)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.11/1.24  tff(c_336, plain, (![A_78]: (k1_tarski('#skF_1')=A_78 | k1_xboole_0=A_78 | ~r1_tarski(A_78, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_239, c_329])).
% 2.11/1.24  tff(c_345, plain, (![A_79]: (A_79='#skF_2' | k1_xboole_0=A_79 | ~r1_tarski(A_79, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_336])).
% 2.11/1.24  tff(c_365, plain, (![A_80]: (A_80='#skF_2' | k1_xboole_0=A_80 | ~r1_tarski(A_80, '#skF_3'))), inference(resolution, [status(thm)], [c_315, c_345])).
% 2.11/1.24  tff(c_369, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_251, c_365])).
% 2.11/1.24  tff(c_373, plain, $false, inference(negUnitSimplification, [status(thm)], [c_238, c_273, c_369])).
% 2.11/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.24  
% 2.11/1.24  Inference rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Ref     : 0
% 2.11/1.24  #Sup     : 74
% 2.11/1.24  #Fact    : 0
% 2.11/1.24  #Define  : 0
% 2.11/1.24  #Split   : 3
% 2.11/1.24  #Chain   : 0
% 2.11/1.24  #Close   : 0
% 2.11/1.24  
% 2.11/1.24  Ordering : KBO
% 2.11/1.24  
% 2.11/1.24  Simplification rules
% 2.11/1.24  ----------------------
% 2.11/1.24  #Subsume      : 2
% 2.11/1.24  #Demod        : 22
% 2.11/1.24  #Tautology    : 56
% 2.11/1.24  #SimpNegUnit  : 6
% 2.11/1.24  #BackRed      : 7
% 2.11/1.24  
% 2.11/1.24  #Partial instantiations: 0
% 2.11/1.24  #Strategies tried      : 1
% 2.11/1.24  
% 2.11/1.24  Timing (in seconds)
% 2.11/1.24  ----------------------
% 2.11/1.25  Preprocessing        : 0.29
% 2.11/1.25  Parsing              : 0.15
% 2.11/1.25  CNF conversion       : 0.02
% 2.11/1.25  Main loop            : 0.19
% 2.11/1.25  Inferencing          : 0.07
% 2.11/1.25  Reduction            : 0.06
% 2.11/1.25  Demodulation         : 0.04
% 2.11/1.25  BG Simplification    : 0.01
% 2.11/1.25  Subsumption          : 0.03
% 2.11/1.25  Abstraction          : 0.01
% 2.11/1.25  MUC search           : 0.00
% 2.11/1.25  Cooper               : 0.00
% 2.11/1.25  Total                : 0.51
% 2.11/1.25  Index Insertion      : 0.00
% 2.11/1.25  Index Deletion       : 0.00
% 2.11/1.25  Index Matching       : 0.00
% 2.11/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
