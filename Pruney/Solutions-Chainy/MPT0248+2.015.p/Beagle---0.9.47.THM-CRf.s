%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:06 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.41s
% Verified   : 
% Statistics : Number of formulae       :   56 (  92 expanded)
%              Number of leaves         :   19 (  38 expanded)
%              Depth                    :    7
%              Number of atoms          :   64 ( 188 expanded)
%              Number of equality atoms :   52 ( 173 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_22,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_20,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_26,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(A_2,k2_xboole_0(A_2,B_3)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_4])).

tff(c_172,plain,(
    ! [B_29,A_30] :
      ( k1_tarski(B_29) = A_30
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,k1_tarski(B_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_175,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_172])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_175])).

tff(c_187,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_188,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_189,plain,(
    ! [A_1] : k2_xboole_0(A_1,'#skF_2') = A_1 ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_2])).

tff(c_6,plain,(
    ! [B_5,A_4] : k2_tarski(B_5,A_4) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_268,plain,(
    ! [A_38,B_39] : k3_tarski(k2_tarski(A_38,B_39)) = k2_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_311,plain,(
    ! [B_42,A_43] : k3_tarski(k2_tarski(B_42,A_43)) = k2_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_268])).

tff(c_18,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_337,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_18])).

tff(c_352,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_26])).

tff(c_398,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_189,c_352])).

tff(c_400,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_398])).

tff(c_401,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_402,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_24,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_464,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_402,c_24])).

tff(c_465,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_531,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_465])).

tff(c_557,plain,(
    ! [B_57,A_58] : k2_xboole_0(B_57,A_58) = k2_xboole_0(A_58,B_57) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_18])).

tff(c_421,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_26])).

tff(c_572,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_557,c_421])).

tff(c_625,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_572,c_4])).

tff(c_669,plain,(
    ! [B_60,A_61] :
      ( k1_tarski(B_60) = A_61
      | k1_xboole_0 = A_61
      | ~ r1_tarski(A_61,k1_tarski(B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_672,plain,(
    ! [A_61] :
      ( k1_tarski('#skF_1') = A_61
      | k1_xboole_0 = A_61
      | ~ r1_tarski(A_61,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_669])).

tff(c_735,plain,(
    ! [A_65] :
      ( A_65 = '#skF_2'
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_402,c_672])).

tff(c_742,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_625,c_735])).

tff(c_754,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_401,c_464,c_742])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:53 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.32  
% 2.01/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.32  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.01/1.32  
% 2.01/1.32  %Foreground sorts:
% 2.01/1.32  
% 2.01/1.32  
% 2.01/1.32  %Background operators:
% 2.01/1.32  
% 2.01/1.32  
% 2.01/1.32  %Foreground operators:
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.01/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.32  
% 2.41/1.34  tff(f_62, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.41/1.34  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.41/1.34  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.41/1.34  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.41/1.34  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.41/1.34  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.41/1.34  tff(c_22, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.34  tff(c_44, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_22])).
% 2.41/1.34  tff(c_20, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.34  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_20])).
% 2.41/1.34  tff(c_26, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.34  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(A_2, k2_xboole_0(A_2, B_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.41/1.34  tff(c_48, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_26, c_4])).
% 2.41/1.34  tff(c_172, plain, (![B_29, A_30]: (k1_tarski(B_29)=A_30 | k1_xboole_0=A_30 | ~r1_tarski(A_30, k1_tarski(B_29)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.34  tff(c_175, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_48, c_172])).
% 2.41/1.34  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_175])).
% 2.41/1.34  tff(c_187, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 2.41/1.34  tff(c_188, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_22])).
% 2.41/1.34  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.41/1.34  tff(c_189, plain, (![A_1]: (k2_xboole_0(A_1, '#skF_2')=A_1)), inference(demodulation, [status(thm), theory('equality')], [c_188, c_2])).
% 2.41/1.34  tff(c_6, plain, (![B_5, A_4]: (k2_tarski(B_5, A_4)=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.41/1.34  tff(c_268, plain, (![A_38, B_39]: (k3_tarski(k2_tarski(A_38, B_39))=k2_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.34  tff(c_311, plain, (![B_42, A_43]: (k3_tarski(k2_tarski(B_42, A_43))=k2_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_6, c_268])).
% 2.41/1.34  tff(c_18, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.34  tff(c_337, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_311, c_18])).
% 2.41/1.34  tff(c_352, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_337, c_26])).
% 2.41/1.34  tff(c_398, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_189, c_352])).
% 2.41/1.34  tff(c_400, plain, $false, inference(negUnitSimplification, [status(thm)], [c_187, c_398])).
% 2.41/1.34  tff(c_401, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_20])).
% 2.41/1.34  tff(c_402, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_20])).
% 2.41/1.34  tff(c_24, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.41/1.34  tff(c_464, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_402, c_24])).
% 2.41/1.34  tff(c_465, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.41/1.34  tff(c_531, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_6, c_465])).
% 2.41/1.34  tff(c_557, plain, (![B_57, A_58]: (k2_xboole_0(B_57, A_58)=k2_xboole_0(A_58, B_57))), inference(superposition, [status(thm), theory('equality')], [c_531, c_18])).
% 2.41/1.34  tff(c_421, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_402, c_26])).
% 2.41/1.34  tff(c_572, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_557, c_421])).
% 2.41/1.34  tff(c_625, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_572, c_4])).
% 2.41/1.34  tff(c_669, plain, (![B_60, A_61]: (k1_tarski(B_60)=A_61 | k1_xboole_0=A_61 | ~r1_tarski(A_61, k1_tarski(B_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.41/1.34  tff(c_672, plain, (![A_61]: (k1_tarski('#skF_1')=A_61 | k1_xboole_0=A_61 | ~r1_tarski(A_61, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_402, c_669])).
% 2.41/1.34  tff(c_735, plain, (![A_65]: (A_65='#skF_2' | k1_xboole_0=A_65 | ~r1_tarski(A_65, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_402, c_672])).
% 2.41/1.34  tff(c_742, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_625, c_735])).
% 2.41/1.34  tff(c_754, plain, $false, inference(negUnitSimplification, [status(thm)], [c_401, c_464, c_742])).
% 2.41/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.41/1.34  
% 2.41/1.34  Inference rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Ref     : 0
% 2.41/1.34  #Sup     : 181
% 2.41/1.34  #Fact    : 0
% 2.41/1.34  #Define  : 0
% 2.41/1.34  #Split   : 3
% 2.41/1.34  #Chain   : 0
% 2.41/1.34  #Close   : 0
% 2.41/1.34  
% 2.41/1.34  Ordering : KBO
% 2.41/1.34  
% 2.41/1.34  Simplification rules
% 2.41/1.34  ----------------------
% 2.41/1.34  #Subsume      : 6
% 2.41/1.34  #Demod        : 45
% 2.41/1.34  #Tautology    : 135
% 2.41/1.34  #SimpNegUnit  : 4
% 2.41/1.34  #BackRed      : 2
% 2.41/1.34  
% 2.41/1.34  #Partial instantiations: 0
% 2.41/1.34  #Strategies tried      : 1
% 2.41/1.34  
% 2.41/1.34  Timing (in seconds)
% 2.41/1.34  ----------------------
% 2.41/1.34  Preprocessing        : 0.29
% 2.41/1.34  Parsing              : 0.15
% 2.41/1.34  CNF conversion       : 0.02
% 2.41/1.34  Main loop            : 0.27
% 2.41/1.34  Inferencing          : 0.11
% 2.41/1.34  Reduction            : 0.09
% 2.41/1.34  Demodulation         : 0.07
% 2.41/1.34  BG Simplification    : 0.01
% 2.41/1.34  Subsumption          : 0.04
% 2.41/1.34  Abstraction          : 0.01
% 2.41/1.34  MUC search           : 0.00
% 2.41/1.34  Cooper               : 0.00
% 2.41/1.34  Total                : 0.59
% 2.41/1.34  Index Insertion      : 0.00
% 2.41/1.34  Index Deletion       : 0.00
% 2.41/1.34  Index Matching       : 0.00
% 2.41/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
