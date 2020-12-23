%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:19 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   53 (  83 expanded)
%              Number of leaves         :   17 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   73 ( 192 expanded)
%              Number of equality atoms :   44 ( 160 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_24,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_22,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_43,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_28,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_39,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_42,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_39])).

tff(c_265,plain,(
    ! [B_31,A_32] :
      ( k1_tarski(B_31) = A_32
      | k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k1_tarski(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_271,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_42,c_265])).

tff(c_284,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_43,c_271])).

tff(c_285,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_286,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_26,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_303,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_286,c_26])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_288,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_28])).

tff(c_353,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_tarski(A_37,k2_xboole_0(C_38,B_39))
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_367,plain,(
    ! [A_40] :
      ( r1_tarski(A_40,'#skF_2')
      | ~ r1_tarski(A_40,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_288,c_353])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,B_7) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_372,plain,(
    ! [A_41] :
      ( k2_xboole_0(A_41,'#skF_2') = '#skF_2'
      | ~ r1_tarski(A_41,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_367,c_10])).

tff(c_381,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_372])).

tff(c_14,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_390,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_14])).

tff(c_423,plain,(
    ! [B_44,A_45] :
      ( k1_tarski(B_44) = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,k1_tarski(B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_426,plain,(
    ! [A_45] :
      ( k1_tarski('#skF_1') = A_45
      | k1_xboole_0 = A_45
      | ~ r1_tarski(A_45,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_423])).

tff(c_453,plain,(
    ! [A_47] :
      ( A_47 = '#skF_2'
      | k1_xboole_0 = A_47
      | ~ r1_tarski(A_47,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_426])).

tff(c_456,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_390,c_453])).

tff(c_471,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_303,c_456])).

tff(c_472,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_473,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_478,plain,(
    ! [A_8] : r1_tarski('#skF_2',A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_473,c_12])).

tff(c_491,plain,(
    ! [A_51,B_52] :
      ( k2_xboole_0(A_51,B_52) = B_52
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_502,plain,(
    ! [A_8] : k2_xboole_0('#skF_2',A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_478,c_491])).

tff(c_504,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_28])).

tff(c_506,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_472,c_504])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:13:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.26  
% 2.01/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.26  %$ r1_tarski > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.26  
% 2.01/1.26  %Foreground sorts:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Background operators:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Foreground operators:
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.26  
% 2.01/1.28  tff(f_68, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.01/1.28  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.01/1.28  tff(f_49, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.01/1.28  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.01/1.28  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.01/1.28  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.01/1.28  tff(f_41, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.01/1.28  tff(c_24, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.01/1.28  tff(c_34, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_24])).
% 2.01/1.28  tff(c_22, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.01/1.28  tff(c_43, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 2.01/1.28  tff(c_28, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.01/1.28  tff(c_39, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.28  tff(c_42, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_39])).
% 2.01/1.28  tff(c_265, plain, (![B_31, A_32]: (k1_tarski(B_31)=A_32 | k1_xboole_0=A_32 | ~r1_tarski(A_32, k1_tarski(B_31)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.28  tff(c_271, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_42, c_265])).
% 2.01/1.28  tff(c_284, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_43, c_271])).
% 2.01/1.28  tff(c_285, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.01/1.28  tff(c_286, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 2.01/1.28  tff(c_26, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.01/1.28  tff(c_303, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_286, c_26])).
% 2.01/1.28  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.01/1.28  tff(c_288, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_286, c_28])).
% 2.01/1.28  tff(c_353, plain, (![A_37, C_38, B_39]: (r1_tarski(A_37, k2_xboole_0(C_38, B_39)) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.01/1.28  tff(c_367, plain, (![A_40]: (r1_tarski(A_40, '#skF_2') | ~r1_tarski(A_40, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_288, c_353])).
% 2.01/1.28  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, B_7)=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.28  tff(c_372, plain, (![A_41]: (k2_xboole_0(A_41, '#skF_2')='#skF_2' | ~r1_tarski(A_41, '#skF_3'))), inference(resolution, [status(thm)], [c_367, c_10])).
% 2.01/1.28  tff(c_381, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_6, c_372])).
% 2.01/1.28  tff(c_14, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.01/1.28  tff(c_390, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_381, c_14])).
% 2.01/1.28  tff(c_423, plain, (![B_44, A_45]: (k1_tarski(B_44)=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, k1_tarski(B_44)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.01/1.28  tff(c_426, plain, (![A_45]: (k1_tarski('#skF_1')=A_45 | k1_xboole_0=A_45 | ~r1_tarski(A_45, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_286, c_423])).
% 2.01/1.28  tff(c_453, plain, (![A_47]: (A_47='#skF_2' | k1_xboole_0=A_47 | ~r1_tarski(A_47, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_426])).
% 2.01/1.28  tff(c_456, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_390, c_453])).
% 2.01/1.28  tff(c_471, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_303, c_456])).
% 2.01/1.28  tff(c_472, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_24])).
% 2.01/1.28  tff(c_473, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_24])).
% 2.01/1.28  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.01/1.28  tff(c_478, plain, (![A_8]: (r1_tarski('#skF_2', A_8))), inference(demodulation, [status(thm), theory('equality')], [c_473, c_12])).
% 2.01/1.28  tff(c_491, plain, (![A_51, B_52]: (k2_xboole_0(A_51, B_52)=B_52 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.28  tff(c_502, plain, (![A_8]: (k2_xboole_0('#skF_2', A_8)=A_8)), inference(resolution, [status(thm)], [c_478, c_491])).
% 2.01/1.28  tff(c_504, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_502, c_28])).
% 2.01/1.28  tff(c_506, plain, $false, inference(negUnitSimplification, [status(thm)], [c_472, c_504])).
% 2.01/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.28  
% 2.01/1.28  Inference rules
% 2.01/1.28  ----------------------
% 2.01/1.28  #Ref     : 0
% 2.01/1.28  #Sup     : 110
% 2.01/1.28  #Fact    : 0
% 2.01/1.28  #Define  : 0
% 2.01/1.28  #Split   : 3
% 2.01/1.28  #Chain   : 0
% 2.01/1.28  #Close   : 0
% 2.01/1.28  
% 2.01/1.28  Ordering : KBO
% 2.01/1.28  
% 2.01/1.28  Simplification rules
% 2.01/1.28  ----------------------
% 2.01/1.28  #Subsume      : 3
% 2.01/1.28  #Demod        : 42
% 2.01/1.28  #Tautology    : 75
% 2.01/1.28  #SimpNegUnit  : 5
% 2.01/1.28  #BackRed      : 4
% 2.01/1.28  
% 2.01/1.28  #Partial instantiations: 0
% 2.01/1.28  #Strategies tried      : 1
% 2.01/1.28  
% 2.01/1.28  Timing (in seconds)
% 2.01/1.28  ----------------------
% 2.01/1.28  Preprocessing        : 0.26
% 2.01/1.28  Parsing              : 0.13
% 2.01/1.28  CNF conversion       : 0.02
% 2.01/1.28  Main loop            : 0.22
% 2.01/1.28  Inferencing          : 0.08
% 2.01/1.28  Reduction            : 0.07
% 2.01/1.28  Demodulation         : 0.05
% 2.01/1.28  BG Simplification    : 0.01
% 2.01/1.28  Subsumption          : 0.04
% 2.01/1.28  Abstraction          : 0.01
% 2.01/1.28  MUC search           : 0.00
% 2.01/1.28  Cooper               : 0.00
% 2.01/1.28  Total                : 0.51
% 2.01/1.28  Index Insertion      : 0.00
% 2.01/1.28  Index Deletion       : 0.00
% 2.01/1.28  Index Matching       : 0.00
% 2.01/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
