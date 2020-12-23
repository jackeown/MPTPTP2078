%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:05 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.63s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 126 expanded)
%              Number of leaves         :   26 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 238 expanded)
%              Number of equality atoms :   62 ( 212 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_40,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_45,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6])).

tff(c_284,plain,(
    ! [B_64,A_65] :
      ( k1_tarski(B_64) = A_65
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_tarski(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_294,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_45,c_284])).

tff(c_304,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_40,c_294])).

tff(c_305,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_324,plain,(
    ! [A_69,B_70] : k2_xboole_0(A_69,k3_xboole_0(A_69,B_70)) = A_69 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_330,plain,(
    ! [A_69] : r1_tarski(A_69,A_69) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_6])).

tff(c_380,plain,(
    ! [A_76,B_77] :
      ( k2_xboole_0(A_76,B_77) = B_77
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_390,plain,(
    ! [A_69] : k2_xboole_0(A_69,A_69) = A_69 ),
    inference(resolution,[status(thm)],[c_330,c_380])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_406,plain,(
    ! [A_79,B_80] : k3_tarski(k2_tarski(A_79,B_80)) = k2_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_447,plain,(
    ! [A_83,B_84] : k3_tarski(k2_tarski(A_83,B_84)) = k2_xboole_0(B_84,A_83) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_406])).

tff(c_30,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_474,plain,(
    ! [B_85,A_86] : k2_xboole_0(B_85,A_86) = k2_xboole_0(A_86,B_85) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_30])).

tff(c_489,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_474,c_38])).

tff(c_528,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_489,c_6])).

tff(c_306,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_24,plain,(
    ! [B_38,A_37] :
      ( k1_tarski(B_38) = A_37
      | k1_xboole_0 = A_37
      | ~ r1_tarski(A_37,k1_tarski(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_599,plain,(
    ! [B_94,A_95] :
      ( k1_tarski(B_94) = A_95
      | A_95 = '#skF_2'
      | ~ r1_tarski(A_95,k1_tarski(B_94)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_306,c_24])).

tff(c_606,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_528,c_599])).

tff(c_617,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_606])).

tff(c_623,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_489])).

tff(c_629,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_623])).

tff(c_631,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_629])).

tff(c_632,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_633,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_670,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_633,c_36])).

tff(c_640,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_38])).

tff(c_766,plain,(
    ! [A_110,B_111] : k3_tarski(k2_tarski(A_110,B_111)) = k2_xboole_0(A_110,B_111) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_834,plain,(
    ! [B_116,A_117] : k3_tarski(k2_tarski(B_116,A_117)) = k2_xboole_0(A_117,B_116) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_766])).

tff(c_861,plain,(
    ! [B_118,A_119] : k2_xboole_0(B_118,A_119) = k2_xboole_0(A_119,B_118) ),
    inference(superposition,[status(thm),theory(equality)],[c_834,c_30])).

tff(c_915,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_861])).

tff(c_935,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_915,c_6])).

tff(c_818,plain,(
    ! [B_114,A_115] :
      ( k1_tarski(B_114) = A_115
      | k1_xboole_0 = A_115
      | ~ r1_tarski(A_115,k1_tarski(B_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_825,plain,(
    ! [A_115] :
      ( k1_tarski('#skF_1') = A_115
      | k1_xboole_0 = A_115
      | ~ r1_tarski(A_115,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_818])).

tff(c_1055,plain,(
    ! [A_133] :
      ( A_133 = '#skF_2'
      | k1_xboole_0 = A_133
      | ~ r1_tarski(A_133,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_825])).

tff(c_1062,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_935,c_1055])).

tff(c_1074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_632,c_670,c_1062])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:46:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  
% 2.63/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.42  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.63/1.42  
% 2.63/1.42  %Foreground sorts:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Background operators:
% 2.63/1.42  
% 2.63/1.42  
% 2.63/1.42  %Foreground operators:
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.42  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.42  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.42  tff('#skF_2', type, '#skF_2': $i).
% 2.63/1.42  tff('#skF_3', type, '#skF_3': $i).
% 2.63/1.42  tff('#skF_1', type, '#skF_1': $i).
% 2.63/1.42  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.63/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.42  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.42  
% 2.63/1.44  tff(f_76, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.63/1.44  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.63/1.44  tff(f_55, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.63/1.44  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.63/1.44  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.63/1.44  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.63/1.44  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.63/1.44  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.44  tff(c_49, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_34])).
% 2.63/1.44  tff(c_32, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.44  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.63/1.44  tff(c_38, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.44  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.63/1.44  tff(c_45, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6])).
% 2.63/1.44  tff(c_284, plain, (![B_64, A_65]: (k1_tarski(B_64)=A_65 | k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_tarski(B_64)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.44  tff(c_294, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_45, c_284])).
% 2.63/1.44  tff(c_304, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_40, c_294])).
% 2.63/1.44  tff(c_305, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 2.63/1.44  tff(c_324, plain, (![A_69, B_70]: (k2_xboole_0(A_69, k3_xboole_0(A_69, B_70))=A_69)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.63/1.44  tff(c_330, plain, (![A_69]: (r1_tarski(A_69, A_69))), inference(superposition, [status(thm), theory('equality')], [c_324, c_6])).
% 2.63/1.44  tff(c_380, plain, (![A_76, B_77]: (k2_xboole_0(A_76, B_77)=B_77 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.63/1.44  tff(c_390, plain, (![A_69]: (k2_xboole_0(A_69, A_69)=A_69)), inference(resolution, [status(thm)], [c_330, c_380])).
% 2.63/1.44  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.63/1.44  tff(c_406, plain, (![A_79, B_80]: (k3_tarski(k2_tarski(A_79, B_80))=k2_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.44  tff(c_447, plain, (![A_83, B_84]: (k3_tarski(k2_tarski(A_83, B_84))=k2_xboole_0(B_84, A_83))), inference(superposition, [status(thm), theory('equality')], [c_8, c_406])).
% 2.63/1.44  tff(c_30, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.44  tff(c_474, plain, (![B_85, A_86]: (k2_xboole_0(B_85, A_86)=k2_xboole_0(A_86, B_85))), inference(superposition, [status(thm), theory('equality')], [c_447, c_30])).
% 2.63/1.44  tff(c_489, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_474, c_38])).
% 2.63/1.44  tff(c_528, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_489, c_6])).
% 2.63/1.44  tff(c_306, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 2.63/1.44  tff(c_24, plain, (![B_38, A_37]: (k1_tarski(B_38)=A_37 | k1_xboole_0=A_37 | ~r1_tarski(A_37, k1_tarski(B_38)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.44  tff(c_599, plain, (![B_94, A_95]: (k1_tarski(B_94)=A_95 | A_95='#skF_2' | ~r1_tarski(A_95, k1_tarski(B_94)))), inference(demodulation, [status(thm), theory('equality')], [c_306, c_24])).
% 2.63/1.44  tff(c_606, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_528, c_599])).
% 2.63/1.44  tff(c_617, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_305, c_606])).
% 2.63/1.44  tff(c_623, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_617, c_489])).
% 2.63/1.44  tff(c_629, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_390, c_623])).
% 2.63/1.44  tff(c_631, plain, $false, inference(negUnitSimplification, [status(thm)], [c_305, c_629])).
% 2.63/1.44  tff(c_632, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.63/1.44  tff(c_633, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.63/1.44  tff(c_36, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.63/1.44  tff(c_670, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_633, c_633, c_36])).
% 2.63/1.44  tff(c_640, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_633, c_38])).
% 2.63/1.44  tff(c_766, plain, (![A_110, B_111]: (k3_tarski(k2_tarski(A_110, B_111))=k2_xboole_0(A_110, B_111))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.63/1.44  tff(c_834, plain, (![B_116, A_117]: (k3_tarski(k2_tarski(B_116, A_117))=k2_xboole_0(A_117, B_116))), inference(superposition, [status(thm), theory('equality')], [c_8, c_766])).
% 2.63/1.44  tff(c_861, plain, (![B_118, A_119]: (k2_xboole_0(B_118, A_119)=k2_xboole_0(A_119, B_118))), inference(superposition, [status(thm), theory('equality')], [c_834, c_30])).
% 2.63/1.44  tff(c_915, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_640, c_861])).
% 2.63/1.44  tff(c_935, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_915, c_6])).
% 2.63/1.44  tff(c_818, plain, (![B_114, A_115]: (k1_tarski(B_114)=A_115 | k1_xboole_0=A_115 | ~r1_tarski(A_115, k1_tarski(B_114)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.63/1.44  tff(c_825, plain, (![A_115]: (k1_tarski('#skF_1')=A_115 | k1_xboole_0=A_115 | ~r1_tarski(A_115, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_633, c_818])).
% 2.63/1.44  tff(c_1055, plain, (![A_133]: (A_133='#skF_2' | k1_xboole_0=A_133 | ~r1_tarski(A_133, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_633, c_825])).
% 2.63/1.44  tff(c_1062, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_935, c_1055])).
% 2.63/1.44  tff(c_1074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_632, c_670, c_1062])).
% 2.63/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.44  
% 2.63/1.44  Inference rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Ref     : 0
% 2.63/1.44  #Sup     : 254
% 2.63/1.44  #Fact    : 0
% 2.63/1.44  #Define  : 0
% 2.63/1.44  #Split   : 3
% 2.63/1.44  #Chain   : 0
% 2.63/1.44  #Close   : 0
% 2.63/1.44  
% 2.63/1.44  Ordering : KBO
% 2.63/1.44  
% 2.63/1.44  Simplification rules
% 2.63/1.44  ----------------------
% 2.63/1.44  #Subsume      : 4
% 2.63/1.44  #Demod        : 85
% 2.63/1.44  #Tautology    : 194
% 2.63/1.44  #SimpNegUnit  : 4
% 2.63/1.44  #BackRed      : 8
% 2.63/1.44  
% 2.63/1.44  #Partial instantiations: 0
% 2.63/1.44  #Strategies tried      : 1
% 2.63/1.44  
% 2.63/1.44  Timing (in seconds)
% 2.63/1.44  ----------------------
% 2.63/1.44  Preprocessing        : 0.33
% 2.63/1.44  Parsing              : 0.17
% 2.63/1.44  CNF conversion       : 0.02
% 2.63/1.44  Main loop            : 0.34
% 2.63/1.44  Inferencing          : 0.13
% 2.63/1.44  Reduction            : 0.12
% 2.63/1.44  Demodulation         : 0.09
% 2.63/1.44  BG Simplification    : 0.02
% 2.63/1.44  Subsumption          : 0.05
% 2.63/1.44  Abstraction          : 0.02
% 2.63/1.44  MUC search           : 0.00
% 2.63/1.44  Cooper               : 0.00
% 2.63/1.44  Total                : 0.71
% 2.63/1.44  Index Insertion      : 0.00
% 2.63/1.44  Index Deletion       : 0.00
% 2.63/1.44  Index Matching       : 0.00
% 2.63/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
