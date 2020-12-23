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
% DateTime   : Thu Dec  3 09:50:04 EST 2020

% Result     : Theorem 3.09s
% Output     : CNFRefutation 3.17s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 110 expanded)
%              Number of leaves         :   23 (  45 expanded)
%              Depth                    :    7
%              Number of atoms          :   78 ( 219 expanded)
%              Number of equality atoms :   57 ( 192 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_32,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_36,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_323,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(k2_xboole_0(A_40,B_42),C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_350,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(A_43,B_44)) ),
    inference(resolution,[status(thm)],[c_6,c_323])).

tff(c_375,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_350])).

tff(c_535,plain,(
    ! [B_55,A_56] :
      ( k1_tarski(B_55) = A_56
      | k1_xboole_0 = A_56
      | ~ r1_tarski(A_56,k1_tarski(B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_541,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_375,c_535])).

tff(c_554,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_50,c_541])).

tff(c_555,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_556,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_10,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_557,plain,(
    ! [A_6] : k4_xboole_0(A_6,'#skF_2') = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_556,c_10])).

tff(c_650,plain,(
    ! [A_66,B_67] : k4_xboole_0(k2_xboole_0(A_66,B_67),B_67) = k4_xboole_0(A_66,B_67) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_657,plain,(
    ! [A_66] : k4_xboole_0(A_66,'#skF_2') = k2_xboole_0(A_66,'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_557])).

tff(c_672,plain,(
    ! [A_66] : k2_xboole_0(A_66,'#skF_2') = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_657])).

tff(c_14,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_615,plain,(
    ! [A_63,B_64] : k3_tarski(k2_tarski(A_63,B_64)) = k2_xboole_0(A_63,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_703,plain,(
    ! [B_71,A_72] : k3_tarski(k2_tarski(B_71,A_72)) = k2_xboole_0(A_72,B_71) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_615])).

tff(c_28,plain,(
    ! [A_19,B_20] : k3_tarski(k2_tarski(A_19,B_20)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_729,plain,(
    ! [B_73,A_74] : k2_xboole_0(B_73,A_74) = k2_xboole_0(A_74,B_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_703,c_28])).

tff(c_758,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_36])).

tff(c_790,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_672,c_758])).

tff(c_792,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_790])).

tff(c_793,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_794,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_818,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_794,c_34])).

tff(c_801,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_36])).

tff(c_861,plain,(
    ! [A_80,B_81] : k3_tarski(k2_tarski(A_80,B_81)) = k2_xboole_0(A_80,B_81) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_946,plain,(
    ! [B_86,A_87] : k3_tarski(k2_tarski(B_86,A_87)) = k2_xboole_0(A_87,B_86) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_861])).

tff(c_976,plain,(
    ! [B_88,A_89] : k2_xboole_0(B_88,A_89) = k2_xboole_0(A_89,B_88) ),
    inference(superposition,[status(thm),theory(equality)],[c_946,c_28])).

tff(c_1029,plain,(
    k2_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_976])).

tff(c_1131,plain,(
    ! [A_94,C_95,B_96] :
      ( r1_tarski(A_94,C_95)
      | ~ r1_tarski(k2_xboole_0(A_94,B_96),C_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1161,plain,(
    ! [A_97,B_98] : r1_tarski(A_97,k2_xboole_0(A_97,B_98)) ),
    inference(resolution,[status(thm)],[c_6,c_1131])).

tff(c_1170,plain,(
    r1_tarski('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1029,c_1161])).

tff(c_1282,plain,(
    ! [B_104,A_105] :
      ( k1_tarski(B_104) = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,k1_tarski(B_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1289,plain,(
    ! [A_105] :
      ( k1_tarski('#skF_1') = A_105
      | k1_xboole_0 = A_105
      | ~ r1_tarski(A_105,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_794,c_1282])).

tff(c_1343,plain,(
    ! [A_108] :
      ( A_108 = '#skF_2'
      | k1_xboole_0 = A_108
      | ~ r1_tarski(A_108,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_794,c_1289])).

tff(c_1350,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1170,c_1343])).

tff(c_1362,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_793,c_818,c_1350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:22:19 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.09/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.51  
% 3.09/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.09/1.51  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.09/1.51  
% 3.09/1.51  %Foreground sorts:
% 3.09/1.51  
% 3.09/1.51  
% 3.09/1.51  %Background operators:
% 3.09/1.51  
% 3.09/1.51  
% 3.09/1.51  %Foreground operators:
% 3.09/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.09/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.09/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.09/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.09/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.09/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.09/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.09/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.09/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.09/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.09/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.09/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.09/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.09/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.09/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.09/1.51  
% 3.17/1.53  tff(f_74, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.17/1.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.17/1.53  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 3.17/1.53  tff(f_53, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.17/1.53  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.17/1.53  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.17/1.53  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.17/1.53  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 3.17/1.53  tff(c_32, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.17/1.53  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_32])).
% 3.17/1.53  tff(c_30, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.17/1.53  tff(c_50, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_30])).
% 3.17/1.53  tff(c_36, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.17/1.53  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.17/1.53  tff(c_323, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(k2_xboole_0(A_40, B_42), C_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.53  tff(c_350, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(A_43, B_44)))), inference(resolution, [status(thm)], [c_6, c_323])).
% 3.17/1.53  tff(c_375, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_350])).
% 3.17/1.53  tff(c_535, plain, (![B_55, A_56]: (k1_tarski(B_55)=A_56 | k1_xboole_0=A_56 | ~r1_tarski(A_56, k1_tarski(B_55)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.17/1.53  tff(c_541, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_375, c_535])).
% 3.17/1.53  tff(c_554, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_50, c_541])).
% 3.17/1.53  tff(c_555, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_32])).
% 3.17/1.53  tff(c_556, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_32])).
% 3.17/1.53  tff(c_10, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.17/1.53  tff(c_557, plain, (![A_6]: (k4_xboole_0(A_6, '#skF_2')=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_556, c_10])).
% 3.17/1.53  tff(c_650, plain, (![A_66, B_67]: (k4_xboole_0(k2_xboole_0(A_66, B_67), B_67)=k4_xboole_0(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.17/1.53  tff(c_657, plain, (![A_66]: (k4_xboole_0(A_66, '#skF_2')=k2_xboole_0(A_66, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_650, c_557])).
% 3.17/1.53  tff(c_672, plain, (![A_66]: (k2_xboole_0(A_66, '#skF_2')=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_557, c_657])).
% 3.17/1.53  tff(c_14, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.17/1.53  tff(c_615, plain, (![A_63, B_64]: (k3_tarski(k2_tarski(A_63, B_64))=k2_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.53  tff(c_703, plain, (![B_71, A_72]: (k3_tarski(k2_tarski(B_71, A_72))=k2_xboole_0(A_72, B_71))), inference(superposition, [status(thm), theory('equality')], [c_14, c_615])).
% 3.17/1.53  tff(c_28, plain, (![A_19, B_20]: (k3_tarski(k2_tarski(A_19, B_20))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.53  tff(c_729, plain, (![B_73, A_74]: (k2_xboole_0(B_73, A_74)=k2_xboole_0(A_74, B_73))), inference(superposition, [status(thm), theory('equality')], [c_703, c_28])).
% 3.17/1.53  tff(c_758, plain, (k2_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_729, c_36])).
% 3.17/1.53  tff(c_790, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_672, c_758])).
% 3.17/1.53  tff(c_792, plain, $false, inference(negUnitSimplification, [status(thm)], [c_555, c_790])).
% 3.17/1.53  tff(c_793, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_30])).
% 3.17/1.53  tff(c_794, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_30])).
% 3.17/1.53  tff(c_34, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.17/1.53  tff(c_818, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_794, c_794, c_34])).
% 3.17/1.53  tff(c_801, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_794, c_36])).
% 3.17/1.53  tff(c_861, plain, (![A_80, B_81]: (k3_tarski(k2_tarski(A_80, B_81))=k2_xboole_0(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.17/1.53  tff(c_946, plain, (![B_86, A_87]: (k3_tarski(k2_tarski(B_86, A_87))=k2_xboole_0(A_87, B_86))), inference(superposition, [status(thm), theory('equality')], [c_14, c_861])).
% 3.17/1.53  tff(c_976, plain, (![B_88, A_89]: (k2_xboole_0(B_88, A_89)=k2_xboole_0(A_89, B_88))), inference(superposition, [status(thm), theory('equality')], [c_946, c_28])).
% 3.17/1.53  tff(c_1029, plain, (k2_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_801, c_976])).
% 3.17/1.53  tff(c_1131, plain, (![A_94, C_95, B_96]: (r1_tarski(A_94, C_95) | ~r1_tarski(k2_xboole_0(A_94, B_96), C_95))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.17/1.53  tff(c_1161, plain, (![A_97, B_98]: (r1_tarski(A_97, k2_xboole_0(A_97, B_98)))), inference(resolution, [status(thm)], [c_6, c_1131])).
% 3.17/1.53  tff(c_1170, plain, (r1_tarski('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1029, c_1161])).
% 3.17/1.53  tff(c_1282, plain, (![B_104, A_105]: (k1_tarski(B_104)=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, k1_tarski(B_104)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.17/1.53  tff(c_1289, plain, (![A_105]: (k1_tarski('#skF_1')=A_105 | k1_xboole_0=A_105 | ~r1_tarski(A_105, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_794, c_1282])).
% 3.17/1.53  tff(c_1343, plain, (![A_108]: (A_108='#skF_2' | k1_xboole_0=A_108 | ~r1_tarski(A_108, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_794, c_1289])).
% 3.17/1.53  tff(c_1350, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1170, c_1343])).
% 3.17/1.53  tff(c_1362, plain, $false, inference(negUnitSimplification, [status(thm)], [c_793, c_818, c_1350])).
% 3.17/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.17/1.53  
% 3.17/1.53  Inference rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Ref     : 0
% 3.17/1.53  #Sup     : 327
% 3.17/1.53  #Fact    : 0
% 3.17/1.53  #Define  : 0
% 3.17/1.53  #Split   : 3
% 3.17/1.53  #Chain   : 0
% 3.17/1.53  #Close   : 0
% 3.17/1.53  
% 3.17/1.53  Ordering : KBO
% 3.17/1.53  
% 3.17/1.53  Simplification rules
% 3.17/1.53  ----------------------
% 3.17/1.53  #Subsume      : 7
% 3.17/1.53  #Demod        : 89
% 3.17/1.53  #Tautology    : 214
% 3.17/1.53  #SimpNegUnit  : 7
% 3.17/1.53  #BackRed      : 2
% 3.17/1.53  
% 3.17/1.53  #Partial instantiations: 0
% 3.17/1.53  #Strategies tried      : 1
% 3.17/1.53  
% 3.17/1.53  Timing (in seconds)
% 3.17/1.53  ----------------------
% 3.20/1.53  Preprocessing        : 0.32
% 3.20/1.53  Parsing              : 0.17
% 3.20/1.53  CNF conversion       : 0.02
% 3.20/1.53  Main loop            : 0.44
% 3.20/1.53  Inferencing          : 0.16
% 3.20/1.53  Reduction            : 0.15
% 3.20/1.53  Demodulation         : 0.12
% 3.20/1.53  BG Simplification    : 0.02
% 3.20/1.53  Subsumption          : 0.07
% 3.20/1.53  Abstraction          : 0.02
% 3.20/1.53  MUC search           : 0.00
% 3.20/1.53  Cooper               : 0.00
% 3.20/1.53  Total                : 0.79
% 3.20/1.53  Index Insertion      : 0.00
% 3.20/1.53  Index Deletion       : 0.00
% 3.20/1.53  Index Matching       : 0.00
% 3.20/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
