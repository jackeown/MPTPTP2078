%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:05 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 119 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   74 ( 230 expanded)
%              Number of equality atoms :   59 ( 209 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_53,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_47,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(A_3,k2_xboole_0(A_3,B_4)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_58,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_4])).

tff(c_262,plain,(
    ! [B_62,A_63] :
      ( k1_tarski(B_62) = A_63
      | k1_xboole_0 = A_63
      | ~ r1_tarski(A_63,k1_tarski(B_62)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_268,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_58,c_262])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_47,c_268])).

tff(c_281,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_341,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_382,plain,(
    ! [B_75,A_76] : k3_tarski(k2_tarski(B_75,A_76)) = k2_xboole_0(A_76,B_75) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_341])).

tff(c_28,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_409,plain,(
    ! [B_77,A_78] : k2_xboole_0(B_77,A_78) = k2_xboole_0(A_78,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_28])).

tff(c_424,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_36])).

tff(c_463,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_424,c_4])).

tff(c_282,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_22,plain,(
    ! [B_36,A_35] :
      ( k1_tarski(B_36) = A_35
      | k1_xboole_0 = A_35
      | ~ r1_tarski(A_35,k1_tarski(B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_369,plain,(
    ! [B_36,A_35] :
      ( k1_tarski(B_36) = A_35
      | A_35 = '#skF_2'
      | ~ r1_tarski(A_35,k1_tarski(B_36)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_282,c_22])).

tff(c_469,plain,
    ( k1_tarski('#skF_1') = '#skF_3'
    | '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_463,c_369])).

tff(c_472,plain,(
    '#skF_2' = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_469])).

tff(c_473,plain,(
    k2_xboole_0('#skF_3','#skF_3') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_472,c_424])).

tff(c_479,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_473])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_281,c_479])).

tff(c_482,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_483,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_561,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_483,c_34])).

tff(c_562,plain,(
    ! [A_86,B_87] : k3_tarski(k2_tarski(A_86,B_87)) = k2_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_606,plain,(
    ! [B_91,A_92] : k3_tarski(k2_tarski(B_91,A_92)) = k2_xboole_0(A_92,B_91) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_562])).

tff(c_633,plain,(
    ! [B_93,A_94] : k2_xboole_0(B_93,A_94) = k2_xboole_0(A_94,B_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_606,c_28])).

tff(c_499,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_36])).

tff(c_654,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_633,c_499])).

tff(c_696,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_654,c_4])).

tff(c_726,plain,(
    ! [B_100,A_101] :
      ( k1_tarski(B_100) = A_101
      | k1_xboole_0 = A_101
      | ~ r1_tarski(A_101,k1_tarski(B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_733,plain,(
    ! [A_101] :
      ( k1_tarski('#skF_1') = A_101
      | k1_xboole_0 = A_101
      | ~ r1_tarski(A_101,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_483,c_726])).

tff(c_742,plain,(
    ! [A_102] :
      ( A_102 = '#skF_2'
      | k1_xboole_0 = A_102
      | ~ r1_tarski(A_102,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_483,c_733])).

tff(c_745,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_696,c_742])).

tff(c_756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_482,c_561,c_745])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:15:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.36  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.36  
% 2.47/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.37  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.47/1.37  
% 2.47/1.37  %Foreground sorts:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Background operators:
% 2.47/1.37  
% 2.47/1.37  
% 2.47/1.37  %Foreground operators:
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.47/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.37  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.37  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.37  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.47/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.37  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.47/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.47/1.37  
% 2.47/1.38  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 2.47/1.38  tff(f_29, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.47/1.38  tff(f_51, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.47/1.38  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.47/1.38  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.47/1.38  tff(f_53, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.47/1.38  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.38  tff(c_62, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 2.47/1.38  tff(c_30, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.38  tff(c_47, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 2.47/1.38  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.38  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, k2_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.38  tff(c_58, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_4])).
% 2.47/1.38  tff(c_262, plain, (![B_62, A_63]: (k1_tarski(B_62)=A_63 | k1_xboole_0=A_63 | ~r1_tarski(A_63, k1_tarski(B_62)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.38  tff(c_268, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_58, c_262])).
% 2.47/1.38  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_47, c_268])).
% 2.47/1.38  tff(c_281, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 2.47/1.38  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.47/1.38  tff(c_6, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.38  tff(c_341, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.38  tff(c_382, plain, (![B_75, A_76]: (k3_tarski(k2_tarski(B_75, A_76))=k2_xboole_0(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_6, c_341])).
% 2.47/1.38  tff(c_28, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.38  tff(c_409, plain, (![B_77, A_78]: (k2_xboole_0(B_77, A_78)=k2_xboole_0(A_78, B_77))), inference(superposition, [status(thm), theory('equality')], [c_382, c_28])).
% 2.47/1.38  tff(c_424, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_409, c_36])).
% 2.47/1.38  tff(c_463, plain, (r1_tarski('#skF_3', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_424, c_4])).
% 2.47/1.38  tff(c_282, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 2.47/1.38  tff(c_22, plain, (![B_36, A_35]: (k1_tarski(B_36)=A_35 | k1_xboole_0=A_35 | ~r1_tarski(A_35, k1_tarski(B_36)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.38  tff(c_369, plain, (![B_36, A_35]: (k1_tarski(B_36)=A_35 | A_35='#skF_2' | ~r1_tarski(A_35, k1_tarski(B_36)))), inference(demodulation, [status(thm), theory('equality')], [c_282, c_22])).
% 2.47/1.38  tff(c_469, plain, (k1_tarski('#skF_1')='#skF_3' | '#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_463, c_369])).
% 2.47/1.38  tff(c_472, plain, ('#skF_2'='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_281, c_469])).
% 2.47/1.38  tff(c_473, plain, (k2_xboole_0('#skF_3', '#skF_3')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_472, c_424])).
% 2.47/1.38  tff(c_479, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_473])).
% 2.47/1.38  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_281, c_479])).
% 2.47/1.38  tff(c_482, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 2.47/1.38  tff(c_483, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 2.47/1.38  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.47/1.38  tff(c_561, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_483, c_483, c_34])).
% 2.47/1.38  tff(c_562, plain, (![A_86, B_87]: (k3_tarski(k2_tarski(A_86, B_87))=k2_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.38  tff(c_606, plain, (![B_91, A_92]: (k3_tarski(k2_tarski(B_91, A_92))=k2_xboole_0(A_92, B_91))), inference(superposition, [status(thm), theory('equality')], [c_6, c_562])).
% 2.47/1.38  tff(c_633, plain, (![B_93, A_94]: (k2_xboole_0(B_93, A_94)=k2_xboole_0(A_94, B_93))), inference(superposition, [status(thm), theory('equality')], [c_606, c_28])).
% 2.47/1.38  tff(c_499, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_483, c_36])).
% 2.47/1.38  tff(c_654, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_633, c_499])).
% 2.47/1.38  tff(c_696, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_654, c_4])).
% 2.47/1.38  tff(c_726, plain, (![B_100, A_101]: (k1_tarski(B_100)=A_101 | k1_xboole_0=A_101 | ~r1_tarski(A_101, k1_tarski(B_100)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.47/1.38  tff(c_733, plain, (![A_101]: (k1_tarski('#skF_1')=A_101 | k1_xboole_0=A_101 | ~r1_tarski(A_101, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_483, c_726])).
% 2.47/1.38  tff(c_742, plain, (![A_102]: (A_102='#skF_2' | k1_xboole_0=A_102 | ~r1_tarski(A_102, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_483, c_733])).
% 2.47/1.38  tff(c_745, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_696, c_742])).
% 2.47/1.38  tff(c_756, plain, $false, inference(negUnitSimplification, [status(thm)], [c_482, c_561, c_745])).
% 2.47/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.38  
% 2.47/1.38  Inference rules
% 2.47/1.38  ----------------------
% 2.47/1.38  #Ref     : 0
% 2.47/1.38  #Sup     : 176
% 2.47/1.38  #Fact    : 0
% 2.47/1.38  #Define  : 0
% 2.47/1.38  #Split   : 3
% 2.47/1.38  #Chain   : 0
% 2.47/1.38  #Close   : 0
% 2.47/1.38  
% 2.47/1.38  Ordering : KBO
% 2.47/1.38  
% 2.47/1.38  Simplification rules
% 2.47/1.38  ----------------------
% 2.47/1.38  #Subsume      : 4
% 2.47/1.38  #Demod        : 57
% 2.47/1.38  #Tautology    : 139
% 2.47/1.38  #SimpNegUnit  : 4
% 2.47/1.38  #BackRed      : 7
% 2.47/1.38  
% 2.47/1.38  #Partial instantiations: 0
% 2.47/1.38  #Strategies tried      : 1
% 2.47/1.38  
% 2.47/1.38  Timing (in seconds)
% 2.47/1.38  ----------------------
% 2.47/1.38  Preprocessing        : 0.32
% 2.47/1.38  Parsing              : 0.17
% 2.47/1.38  CNF conversion       : 0.02
% 2.47/1.38  Main loop            : 0.30
% 2.47/1.38  Inferencing          : 0.11
% 2.47/1.38  Reduction            : 0.10
% 2.47/1.38  Demodulation         : 0.08
% 2.47/1.38  BG Simplification    : 0.02
% 2.47/1.38  Subsumption          : 0.05
% 2.47/1.38  Abstraction          : 0.01
% 2.47/1.38  MUC search           : 0.00
% 2.47/1.38  Cooper               : 0.00
% 2.47/1.38  Total                : 0.65
% 2.47/1.38  Index Insertion      : 0.00
% 2.47/1.39  Index Deletion       : 0.00
% 2.47/1.39  Index Matching       : 0.00
% 2.47/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
