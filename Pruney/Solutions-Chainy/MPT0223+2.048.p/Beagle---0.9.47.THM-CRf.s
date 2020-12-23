%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:22 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   55 ( 116 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   61 ( 172 expanded)
%              Number of equality atoms :   25 (  81 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_79,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_66,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_119,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(k1_tarski(A_57),B_58)
      | r2_hidden(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_241,plain,(
    ! [A_77,B_78] :
      ( k3_xboole_0(k1_tarski(A_77),B_78) = k1_xboole_0
      | r2_hidden(A_77,B_78) ) ),
    inference(resolution,[status(thm)],[c_119,c_2])).

tff(c_68,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_250,plain,
    ( k1_tarski('#skF_6') = k1_xboole_0
    | r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_68])).

tff(c_279,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_250])).

tff(c_46,plain,(
    ! [C_26,A_22] :
      ( C_26 = A_22
      | ~ r2_hidden(C_26,k1_tarski(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_282,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_279,c_46])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_282])).

tff(c_287,plain,(
    k1_tarski('#skF_6') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_289,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_287,c_68])).

tff(c_64,plain,(
    ! [A_33,B_34] :
      ( r1_xboole_0(k1_tarski(A_33),B_34)
      | r2_hidden(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_329,plain,(
    ! [B_83] :
      ( r1_xboole_0(k1_xboole_0,B_83)
      | r2_hidden('#skF_6',B_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_64])).

tff(c_288,plain,(
    ~ r2_hidden('#skF_6',k1_tarski('#skF_7')) ),
    inference(splitRight,[status(thm)],[c_250])).

tff(c_343,plain,(
    r1_xboole_0(k1_xboole_0,k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_329,c_288])).

tff(c_18,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_356,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_7')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_343,c_18])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_375,plain,(
    k3_xboole_0(k1_xboole_0,k1_tarski('#skF_7')) = k4_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_356,c_16])).

tff(c_386,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_289,c_375])).

tff(c_48,plain,(
    ! [C_26] : r2_hidden(C_26,k1_tarski(C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_302,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_48])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_xboole_0(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != A_13 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_269,plain,(
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,B_80)
      | ~ r2_hidden(C_81,A_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1224,plain,(
    ! [C_120,B_121,A_122] :
      ( ~ r2_hidden(C_120,B_121)
      | ~ r2_hidden(C_120,A_122)
      | k4_xboole_0(A_122,B_121) != A_122 ) ),
    inference(resolution,[status(thm)],[c_20,c_269])).

tff(c_1264,plain,(
    ! [A_123] :
      ( ~ r2_hidden('#skF_6',A_123)
      | k4_xboole_0(A_123,k1_xboole_0) != A_123 ) ),
    inference(resolution,[status(thm)],[c_302,c_1224])).

tff(c_1276,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_302,c_1264])).

tff(c_1307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_1276])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:09:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.54  
% 3.06/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.54  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_2 > #skF_6 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.06/1.54  
% 3.06/1.54  %Foreground sorts:
% 3.06/1.54  
% 3.06/1.54  
% 3.06/1.54  %Background operators:
% 3.06/1.54  
% 3.06/1.54  
% 3.06/1.54  %Foreground operators:
% 3.06/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.06/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.54  tff('#skF_7', type, '#skF_7': $i).
% 3.06/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.06/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.06/1.54  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.06/1.54  tff('#skF_6', type, '#skF_6': $i).
% 3.06/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.06/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.06/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.06/1.54  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.06/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.54  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.06/1.54  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.06/1.54  
% 3.06/1.55  tff(f_95, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.06/1.55  tff(f_90, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.06/1.55  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 3.06/1.55  tff(f_79, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.06/1.55  tff(f_57, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.06/1.55  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.06/1.55  tff(f_47, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.06/1.55  tff(c_66, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.06/1.55  tff(c_119, plain, (![A_57, B_58]: (r1_xboole_0(k1_tarski(A_57), B_58) | r2_hidden(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.06/1.55  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.55  tff(c_241, plain, (![A_77, B_78]: (k3_xboole_0(k1_tarski(A_77), B_78)=k1_xboole_0 | r2_hidden(A_77, B_78))), inference(resolution, [status(thm)], [c_119, c_2])).
% 3.06/1.55  tff(c_68, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_95])).
% 3.06/1.55  tff(c_250, plain, (k1_tarski('#skF_6')=k1_xboole_0 | r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_241, c_68])).
% 3.06/1.55  tff(c_279, plain, (r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_250])).
% 3.06/1.55  tff(c_46, plain, (![C_26, A_22]: (C_26=A_22 | ~r2_hidden(C_26, k1_tarski(A_22)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.06/1.55  tff(c_282, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_279, c_46])).
% 3.06/1.55  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_282])).
% 3.06/1.55  tff(c_287, plain, (k1_tarski('#skF_6')=k1_xboole_0), inference(splitRight, [status(thm)], [c_250])).
% 3.06/1.55  tff(c_289, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_287, c_287, c_68])).
% 3.06/1.55  tff(c_64, plain, (![A_33, B_34]: (r1_xboole_0(k1_tarski(A_33), B_34) | r2_hidden(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.06/1.55  tff(c_329, plain, (![B_83]: (r1_xboole_0(k1_xboole_0, B_83) | r2_hidden('#skF_6', B_83))), inference(superposition, [status(thm), theory('equality')], [c_287, c_64])).
% 3.06/1.55  tff(c_288, plain, (~r2_hidden('#skF_6', k1_tarski('#skF_7'))), inference(splitRight, [status(thm)], [c_250])).
% 3.06/1.55  tff(c_343, plain, (r1_xboole_0(k1_xboole_0, k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_329, c_288])).
% 3.06/1.55  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.06/1.55  tff(c_356, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_7'))=k1_xboole_0), inference(resolution, [status(thm)], [c_343, c_18])).
% 3.06/1.55  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.06/1.55  tff(c_375, plain, (k3_xboole_0(k1_xboole_0, k1_tarski('#skF_7'))=k4_xboole_0(k1_xboole_0, k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_356, c_16])).
% 3.06/1.55  tff(c_386, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_289, c_375])).
% 3.06/1.55  tff(c_48, plain, (![C_26]: (r2_hidden(C_26, k1_tarski(C_26)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.06/1.55  tff(c_302, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_287, c_48])).
% 3.06/1.55  tff(c_20, plain, (![A_13, B_14]: (r1_xboole_0(A_13, B_14) | k4_xboole_0(A_13, B_14)!=A_13)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.06/1.55  tff(c_269, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, B_80) | ~r2_hidden(C_81, A_79))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.06/1.55  tff(c_1224, plain, (![C_120, B_121, A_122]: (~r2_hidden(C_120, B_121) | ~r2_hidden(C_120, A_122) | k4_xboole_0(A_122, B_121)!=A_122)), inference(resolution, [status(thm)], [c_20, c_269])).
% 3.06/1.55  tff(c_1264, plain, (![A_123]: (~r2_hidden('#skF_6', A_123) | k4_xboole_0(A_123, k1_xboole_0)!=A_123)), inference(resolution, [status(thm)], [c_302, c_1224])).
% 3.06/1.55  tff(c_1276, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_302, c_1264])).
% 3.06/1.55  tff(c_1307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_386, c_1276])).
% 3.06/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.55  
% 3.06/1.55  Inference rules
% 3.06/1.55  ----------------------
% 3.06/1.55  #Ref     : 0
% 3.06/1.55  #Sup     : 289
% 3.06/1.55  #Fact    : 0
% 3.06/1.55  #Define  : 0
% 3.06/1.55  #Split   : 2
% 3.06/1.55  #Chain   : 0
% 3.06/1.55  #Close   : 0
% 3.06/1.55  
% 3.06/1.55  Ordering : KBO
% 3.06/1.55  
% 3.06/1.55  Simplification rules
% 3.06/1.55  ----------------------
% 3.06/1.55  #Subsume      : 21
% 3.06/1.55  #Demod        : 91
% 3.06/1.55  #Tautology    : 144
% 3.06/1.55  #SimpNegUnit  : 6
% 3.06/1.55  #BackRed      : 1
% 3.06/1.55  
% 3.06/1.55  #Partial instantiations: 0
% 3.06/1.55  #Strategies tried      : 1
% 3.06/1.55  
% 3.06/1.55  Timing (in seconds)
% 3.06/1.55  ----------------------
% 3.06/1.56  Preprocessing        : 0.33
% 3.06/1.56  Parsing              : 0.17
% 3.06/1.56  CNF conversion       : 0.02
% 3.06/1.56  Main loop            : 0.38
% 3.06/1.56  Inferencing          : 0.14
% 3.06/1.56  Reduction            : 0.12
% 3.06/1.56  Demodulation         : 0.08
% 3.06/1.56  BG Simplification    : 0.02
% 3.06/1.56  Subsumption          : 0.07
% 3.06/1.56  Abstraction          : 0.02
% 3.06/1.56  MUC search           : 0.00
% 3.06/1.56  Cooper               : 0.00
% 3.06/1.56  Total                : 0.74
% 3.06/1.56  Index Insertion      : 0.00
% 3.06/1.56  Index Deletion       : 0.00
% 3.06/1.56  Index Matching       : 0.00
% 3.06/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
