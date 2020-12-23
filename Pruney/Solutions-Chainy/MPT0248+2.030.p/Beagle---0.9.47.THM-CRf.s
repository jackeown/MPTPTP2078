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
% DateTime   : Thu Dec  3 09:50:08 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   19 (  39 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 214 expanded)
%              Number of equality atoms :   45 ( 185 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_68,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_62,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_16,plain,(
    ! [B_14] : r1_tarski(k1_tarski(B_14),k1_tarski(B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_215,plain,(
    ! [A_39,C_40,B_41] :
      ( r1_tarski(A_39,C_40)
      | ~ r1_tarski(k2_xboole_0(A_39,B_41),C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_277,plain,(
    ! [C_45] :
      ( r1_tarski('#skF_2',C_45)
      | ~ r1_tarski(k1_tarski('#skF_1'),C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_215])).

tff(c_292,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_277])).

tff(c_388,plain,(
    ! [B_57,A_58] :
      ( k1_tarski(B_57) = A_58
      | k1_xboole_0 = A_58
      | ~ r1_tarski(A_58,k1_tarski(B_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_394,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_292,c_388])).

tff(c_405,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_62,c_394])).

tff(c_406,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_407,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_6,plain,(
    ! [A_6] : k2_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_409,plain,(
    ! [A_6] : k2_xboole_0(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_407,c_6])).

tff(c_434,plain,(
    ! [B_65,A_66] : k2_xboole_0(B_65,A_66) = k2_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_457,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_434,c_38])).

tff(c_489,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_409,c_457])).

tff(c_491,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_406,c_489])).

tff(c_492,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_493,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_529,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_493,c_36])).

tff(c_510,plain,(
    ! [B_69] : r1_tarski(k1_tarski(B_69),k1_tarski(B_69)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_513,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_510])).

tff(c_517,plain,(
    r1_tarski('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_513])).

tff(c_550,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_495,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_38])).

tff(c_565,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_550,c_495])).

tff(c_708,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,C_87)
      | ~ r1_tarski(k2_xboole_0(A_86,B_88),C_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_774,plain,(
    ! [C_91] :
      ( r1_tarski('#skF_3',C_91)
      | ~ r1_tarski('#skF_2',C_91) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_565,c_708])).

tff(c_786,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_517,c_774])).

tff(c_853,plain,(
    ! [B_103,A_104] :
      ( k1_tarski(B_103) = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,k1_tarski(B_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_859,plain,(
    ! [A_104] :
      ( k1_tarski('#skF_1') = A_104
      | k1_xboole_0 = A_104
      | ~ r1_tarski(A_104,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_853])).

tff(c_868,plain,(
    ! [A_105] :
      ( A_105 = '#skF_2'
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_493,c_859])).

tff(c_871,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_786,c_868])).

tff(c_881,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_492,c_529,c_871])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:30 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.39  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  
% 2.72/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.40  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.72/1.40  
% 2.72/1.40  %Foreground sorts:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Background operators:
% 2.72/1.40  
% 2.72/1.40  
% 2.72/1.40  %Foreground operators:
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.72/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.72/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.40  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.72/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.40  
% 2.72/1.42  tff(f_81, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.72/1.42  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.72/1.42  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.72/1.42  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.72/1.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.72/1.42  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.72/1.42  tff(c_68, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.72/1.42  tff(c_32, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.72/1.42  tff(c_62, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.72/1.42  tff(c_16, plain, (![B_14]: (r1_tarski(k1_tarski(B_14), k1_tarski(B_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.42  tff(c_38, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.72/1.42  tff(c_215, plain, (![A_39, C_40, B_41]: (r1_tarski(A_39, C_40) | ~r1_tarski(k2_xboole_0(A_39, B_41), C_40))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.42  tff(c_277, plain, (![C_45]: (r1_tarski('#skF_2', C_45) | ~r1_tarski(k1_tarski('#skF_1'), C_45))), inference(superposition, [status(thm), theory('equality')], [c_38, c_215])).
% 2.72/1.42  tff(c_292, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_277])).
% 2.72/1.42  tff(c_388, plain, (![B_57, A_58]: (k1_tarski(B_57)=A_58 | k1_xboole_0=A_58 | ~r1_tarski(A_58, k1_tarski(B_57)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.42  tff(c_394, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_292, c_388])).
% 2.72/1.42  tff(c_405, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_62, c_394])).
% 2.72/1.42  tff(c_406, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.72/1.42  tff(c_407, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.72/1.42  tff(c_6, plain, (![A_6]: (k2_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.42  tff(c_409, plain, (![A_6]: (k2_xboole_0(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_407, c_6])).
% 2.72/1.42  tff(c_434, plain, (![B_65, A_66]: (k2_xboole_0(B_65, A_66)=k2_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.42  tff(c_457, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_434, c_38])).
% 2.72/1.42  tff(c_489, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_409, c_457])).
% 2.72/1.42  tff(c_491, plain, $false, inference(negUnitSimplification, [status(thm)], [c_406, c_489])).
% 2.72/1.42  tff(c_492, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.72/1.42  tff(c_493, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.72/1.42  tff(c_36, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.72/1.42  tff(c_529, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_493, c_36])).
% 2.72/1.42  tff(c_510, plain, (![B_69]: (r1_tarski(k1_tarski(B_69), k1_tarski(B_69)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.42  tff(c_513, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_510])).
% 2.72/1.42  tff(c_517, plain, (r1_tarski('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_493, c_513])).
% 2.72/1.42  tff(c_550, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.72/1.42  tff(c_495, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_493, c_38])).
% 2.72/1.42  tff(c_565, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_550, c_495])).
% 2.72/1.42  tff(c_708, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, C_87) | ~r1_tarski(k2_xboole_0(A_86, B_88), C_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.42  tff(c_774, plain, (![C_91]: (r1_tarski('#skF_3', C_91) | ~r1_tarski('#skF_2', C_91))), inference(superposition, [status(thm), theory('equality')], [c_565, c_708])).
% 2.72/1.42  tff(c_786, plain, (r1_tarski('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_517, c_774])).
% 2.72/1.42  tff(c_853, plain, (![B_103, A_104]: (k1_tarski(B_103)=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, k1_tarski(B_103)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.72/1.42  tff(c_859, plain, (![A_104]: (k1_tarski('#skF_1')=A_104 | k1_xboole_0=A_104 | ~r1_tarski(A_104, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_853])).
% 2.72/1.42  tff(c_868, plain, (![A_105]: (A_105='#skF_2' | k1_xboole_0=A_105 | ~r1_tarski(A_105, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_493, c_859])).
% 2.72/1.42  tff(c_871, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_786, c_868])).
% 2.72/1.42  tff(c_881, plain, $false, inference(negUnitSimplification, [status(thm)], [c_492, c_529, c_871])).
% 2.72/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.72/1.42  
% 2.72/1.42  Inference rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Ref     : 0
% 2.72/1.42  #Sup     : 208
% 2.72/1.42  #Fact    : 0
% 2.72/1.42  #Define  : 0
% 2.72/1.42  #Split   : 3
% 2.72/1.42  #Chain   : 0
% 2.72/1.42  #Close   : 0
% 2.72/1.42  
% 2.72/1.42  Ordering : KBO
% 2.72/1.42  
% 2.72/1.42  Simplification rules
% 2.72/1.42  ----------------------
% 2.72/1.42  #Subsume      : 21
% 2.72/1.42  #Demod        : 84
% 2.72/1.42  #Tautology    : 138
% 2.72/1.42  #SimpNegUnit  : 3
% 2.72/1.42  #BackRed      : 4
% 2.72/1.42  
% 2.72/1.42  #Partial instantiations: 0
% 2.72/1.42  #Strategies tried      : 1
% 2.72/1.42  
% 2.72/1.42  Timing (in seconds)
% 2.72/1.42  ----------------------
% 2.72/1.43  Preprocessing        : 0.31
% 2.72/1.43  Parsing              : 0.16
% 2.72/1.43  CNF conversion       : 0.02
% 2.72/1.43  Main loop            : 0.34
% 2.72/1.43  Inferencing          : 0.13
% 2.72/1.43  Reduction            : 0.12
% 2.72/1.43  Demodulation         : 0.09
% 2.72/1.43  BG Simplification    : 0.02
% 2.72/1.43  Subsumption          : 0.05
% 2.72/1.43  Abstraction          : 0.01
% 2.72/1.43  MUC search           : 0.00
% 2.72/1.43  Cooper               : 0.00
% 2.72/1.43  Total                : 0.69
% 2.72/1.43  Index Insertion      : 0.00
% 2.72/1.43  Index Deletion       : 0.00
% 2.72/1.43  Index Matching       : 0.00
% 2.72/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
