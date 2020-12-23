%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:51 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   54 ( 114 expanded)
%              Number of leaves         :   30 (  52 expanded)
%              Depth                    :    8
%              Number of atoms          :   47 ( 140 expanded)
%              Number of equality atoms :   32 (  95 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_42,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( A != B
     => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] : k3_tarski(k2_tarski(k1_tarski(A),k1_tarski(B))) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_40,plain,(
    ! [A_39] : k3_tarski(k1_tarski(A_39)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_22,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_71,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    ! [A_12] : k3_tarski(k1_tarski(A_12)) = k2_xboole_0(A_12,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_71])).

tff(c_83,plain,(
    ! [A_12] : k2_xboole_0(A_12,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_80])).

tff(c_38,plain,(
    ! [A_37,B_38] :
      ( k5_xboole_0(k1_tarski(A_37),k1_tarski(B_38)) = k2_tarski(A_37,B_38)
      | B_38 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_34,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_102,plain,(
    ! [A_54,B_55] :
      ( k4_xboole_0(A_54,B_55) = A_54
      | ~ r1_xboole_0(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_138,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(k1_tarski(A_63),B_64) = k1_tarski(A_63)
      | r2_hidden(A_63,B_64) ) ),
    inference(resolution,[status(thm)],[c_34,c_102])).

tff(c_8,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    ! [B_73,A_74] :
      ( k5_xboole_0(B_73,k1_tarski(A_74)) = k2_xboole_0(B_73,k1_tarski(A_74))
      | r2_hidden(A_74,B_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_8])).

tff(c_230,plain,(
    ! [A_88,B_89] :
      ( k2_xboole_0(k1_tarski(A_88),k1_tarski(B_89)) = k2_tarski(A_88,B_89)
      | r2_hidden(B_89,k1_tarski(A_88))
      | B_89 = A_88 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_169])).

tff(c_36,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    k3_tarski(k2_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) != k2_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_43,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k2_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_42])).

tff(c_249,plain,
    ( r2_hidden('#skF_4',k1_tarski('#skF_3'))
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_230,c_43])).

tff(c_264,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_265,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_4')) != k2_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_264,c_43])).

tff(c_268,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_83,c_22,c_265])).

tff(c_270,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_269,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_10,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_273,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_269,c_10])).

tff(c_277,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_270,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:55:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  
% 1.99/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.24  %$ r2_hidden > r1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.99/1.24  
% 1.99/1.24  %Foreground sorts:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Background operators:
% 1.99/1.24  
% 1.99/1.24  
% 1.99/1.24  %Foreground operators:
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.99/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.99/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.99/1.24  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.24  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.24  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.99/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.24  
% 1.99/1.25  tff(f_66, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 1.99/1.25  tff(f_42, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.25  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.99/1.25  tff(f_64, axiom, (![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.99/1.25  tff(f_57, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.99/1.25  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.99/1.25  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.99/1.25  tff(f_69, negated_conjecture, ~(![A, B]: (k3_tarski(k2_tarski(k1_tarski(A), k1_tarski(B))) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_zfmisc_1)).
% 1.99/1.25  tff(f_40, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.25  tff(c_40, plain, (![A_39]: (k3_tarski(k1_tarski(A_39))=A_39)), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.99/1.25  tff(c_22, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.25  tff(c_71, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.25  tff(c_80, plain, (![A_12]: (k3_tarski(k1_tarski(A_12))=k2_xboole_0(A_12, A_12))), inference(superposition, [status(thm), theory('equality')], [c_22, c_71])).
% 1.99/1.25  tff(c_83, plain, (![A_12]: (k2_xboole_0(A_12, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_80])).
% 1.99/1.25  tff(c_38, plain, (![A_37, B_38]: (k5_xboole_0(k1_tarski(A_37), k1_tarski(B_38))=k2_tarski(A_37, B_38) | B_38=A_37)), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.99/1.25  tff(c_34, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.99/1.25  tff(c_102, plain, (![A_54, B_55]: (k4_xboole_0(A_54, B_55)=A_54 | ~r1_xboole_0(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.99/1.25  tff(c_138, plain, (![A_63, B_64]: (k4_xboole_0(k1_tarski(A_63), B_64)=k1_tarski(A_63) | r2_hidden(A_63, B_64))), inference(resolution, [status(thm)], [c_34, c_102])).
% 1.99/1.25  tff(c_8, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.99/1.25  tff(c_169, plain, (![B_73, A_74]: (k5_xboole_0(B_73, k1_tarski(A_74))=k2_xboole_0(B_73, k1_tarski(A_74)) | r2_hidden(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_138, c_8])).
% 1.99/1.25  tff(c_230, plain, (![A_88, B_89]: (k2_xboole_0(k1_tarski(A_88), k1_tarski(B_89))=k2_tarski(A_88, B_89) | r2_hidden(B_89, k1_tarski(A_88)) | B_89=A_88)), inference(superposition, [status(thm), theory('equality')], [c_38, c_169])).
% 1.99/1.25  tff(c_36, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.99/1.25  tff(c_42, plain, (k3_tarski(k2_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4')))!=k2_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.99/1.25  tff(c_43, plain, (k2_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k2_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_42])).
% 1.99/1.25  tff(c_249, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3')) | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_230, c_43])).
% 1.99/1.25  tff(c_264, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_249])).
% 1.99/1.25  tff(c_265, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_4'))!=k2_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_264, c_43])).
% 1.99/1.25  tff(c_268, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_83, c_22, c_265])).
% 1.99/1.25  tff(c_270, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_249])).
% 1.99/1.25  tff(c_269, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(splitRight, [status(thm)], [c_249])).
% 1.99/1.25  tff(c_10, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.99/1.25  tff(c_273, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_269, c_10])).
% 1.99/1.25  tff(c_277, plain, $false, inference(negUnitSimplification, [status(thm)], [c_270, c_273])).
% 1.99/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.25  
% 1.99/1.25  Inference rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Ref     : 0
% 1.99/1.25  #Sup     : 48
% 1.99/1.25  #Fact    : 0
% 1.99/1.25  #Define  : 0
% 1.99/1.25  #Split   : 1
% 1.99/1.25  #Chain   : 0
% 1.99/1.25  #Close   : 0
% 1.99/1.25  
% 1.99/1.25  Ordering : KBO
% 1.99/1.25  
% 1.99/1.25  Simplification rules
% 1.99/1.25  ----------------------
% 1.99/1.25  #Subsume      : 0
% 1.99/1.25  #Demod        : 12
% 1.99/1.25  #Tautology    : 39
% 1.99/1.25  #SimpNegUnit  : 1
% 1.99/1.25  #BackRed      : 1
% 1.99/1.25  
% 1.99/1.25  #Partial instantiations: 0
% 1.99/1.25  #Strategies tried      : 1
% 1.99/1.25  
% 1.99/1.25  Timing (in seconds)
% 1.99/1.25  ----------------------
% 1.99/1.25  Preprocessing        : 0.31
% 1.99/1.25  Parsing              : 0.16
% 1.99/1.25  CNF conversion       : 0.02
% 1.99/1.25  Main loop            : 0.18
% 1.99/1.25  Inferencing          : 0.07
% 1.99/1.25  Reduction            : 0.05
% 1.99/1.26  Demodulation         : 0.04
% 1.99/1.26  BG Simplification    : 0.02
% 1.99/1.26  Subsumption          : 0.03
% 1.99/1.26  Abstraction          : 0.01
% 1.99/1.26  MUC search           : 0.00
% 1.99/1.26  Cooper               : 0.00
% 1.99/1.26  Total                : 0.52
% 1.99/1.26  Index Insertion      : 0.00
% 1.99/1.26  Index Deletion       : 0.00
% 1.99/1.26  Index Matching       : 0.00
% 1.99/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
