%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:32 EST 2020

% Result     : Theorem 12.73s
% Output     : CNFRefutation 12.73s
% Verified   : 
% Statistics : Number of formulae       :   66 (  97 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 139 expanded)
%              Number of equality atoms :   32 (  51 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,B)
          & r1_xboole_0(A,C) )
       => r1_tarski(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_47,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_60,plain,(
    ! [A_28,B_29] :
      ( r1_tarski(A_28,B_29)
      | k4_xboole_0(A_28,B_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_64,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_60,c_24])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_99,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_114,plain,(
    ! [A_5,B_6] : k4_xboole_0(k4_xboole_0(A_5,B_6),A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_99])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_44,plain,(
    ! [B_25,A_26] :
      ( r1_xboole_0(B_25,A_26)
      | ~ r1_xboole_0(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_14] : r1_xboole_0(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_261,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_xboole_0(A_43,C_44)
      | ~ r1_xboole_0(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_337,plain,(
    ! [A_50,A_51] :
      ( r1_xboole_0(A_50,A_51)
      | ~ r1_tarski(A_50,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_49,c_261])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(A_18,B_19) = A_18
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_671,plain,(
    ! [A_67,A_68] :
      ( k4_xboole_0(A_67,A_68) = A_67
      | ~ r1_tarski(A_67,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_337,c_20])).

tff(c_677,plain,(
    ! [A_3,A_68] :
      ( k4_xboole_0(A_3,A_68) = A_3
      | k4_xboole_0(A_3,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_671])).

tff(c_687,plain,(
    ! [A_3,A_68] :
      ( k4_xboole_0(A_3,A_68) = A_3
      | k1_xboole_0 != A_3 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_677])).

tff(c_39,plain,(
    ! [A_22,B_23] : r1_tarski(k4_xboole_0(A_22,B_23),A_22) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_42,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_39])).

tff(c_113,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_99])).

tff(c_816,plain,(
    ! [B_71,A_72,C_73] :
      ( r1_xboole_0(B_71,k4_xboole_0(A_72,C_73))
      | ~ r1_xboole_0(A_72,k4_xboole_0(B_71,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_849,plain,(
    ! [A_7,A_72] :
      ( r1_xboole_0(A_7,k4_xboole_0(A_72,A_7))
      | ~ r1_xboole_0(A_72,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_816])).

tff(c_957,plain,(
    ! [A_76,A_77] : r1_xboole_0(A_76,k4_xboole_0(A_77,A_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_849])).

tff(c_2031,plain,(
    ! [A_101,A_102] : k4_xboole_0(A_101,k4_xboole_0(A_102,A_101)) = A_101 ),
    inference(resolution,[status(thm)],[c_957,c_20])).

tff(c_2689,plain,(
    ! [A_68] : k4_xboole_0(A_68,k1_xboole_0) = A_68 ),
    inference(superposition,[status(thm),theory(equality)],[c_687,c_2031])).

tff(c_423,plain,(
    ! [A_57,B_58,C_59] : k4_xboole_0(k4_xboole_0(A_57,B_58),C_59) = k4_xboole_0(A_57,k2_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_31604,plain,(
    ! [A_490,B_491] : k4_xboole_0(A_490,k2_xboole_0(B_491,k4_xboole_0(A_490,B_491))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_423,c_113])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_69,plain,(
    ! [A_32,B_33] :
      ( k4_xboole_0(A_32,B_33) = A_32
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_90,plain,(
    k4_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_26,c_69])).

tff(c_481,plain,(
    ! [C_59] : k4_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_59)) = k4_xboole_0('#skF_1',C_59) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_423])).

tff(c_28,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_3400,plain,(
    ! [B_125,A_126,C_127] :
      ( r1_xboole_0(B_125,k4_xboole_0(A_126,C_127))
      | k4_xboole_0(A_126,k4_xboole_0(B_125,C_127)) != A_126 ) ),
    inference(resolution,[status(thm)],[c_22,c_816])).

tff(c_14,plain,(
    ! [A_11,C_13,B_12] :
      ( r1_xboole_0(A_11,C_13)
      | ~ r1_xboole_0(B_12,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_21961,plain,(
    ! [A_388,A_389,C_390,B_391] :
      ( r1_xboole_0(A_388,k4_xboole_0(A_389,C_390))
      | ~ r1_tarski(A_388,B_391)
      | k4_xboole_0(A_389,k4_xboole_0(B_391,C_390)) != A_389 ) ),
    inference(resolution,[status(thm)],[c_3400,c_14])).

tff(c_22039,plain,(
    ! [A_392,C_393] :
      ( r1_xboole_0('#skF_1',k4_xboole_0(A_392,C_393))
      | k4_xboole_0(A_392,k4_xboole_0('#skF_2',C_393)) != A_392 ) ),
    inference(resolution,[status(thm)],[c_28,c_21961])).

tff(c_22153,plain,(
    ! [C_59] :
      ( r1_xboole_0('#skF_1',k4_xboole_0('#skF_1',C_59))
      | k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',k2_xboole_0('#skF_3',C_59))) != '#skF_1' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_481,c_22039])).

tff(c_31638,plain,
    ( r1_xboole_0('#skF_1',k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')))
    | k4_xboole_0('#skF_1',k1_xboole_0) != '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_31604,c_22153])).

tff(c_32287,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2689,c_31638])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_32506,plain,(
    r1_xboole_0(k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_32287,c_2])).

tff(c_32641,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')),'#skF_1') = k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32506,c_20])).

tff(c_32676,plain,(
    k4_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_32641])).

tff(c_32678,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_32676])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:50:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.73/6.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/6.05  
% 12.73/6.05  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/6.05  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.73/6.05  
% 12.73/6.05  %Foreground sorts:
% 12.73/6.05  
% 12.73/6.05  
% 12.73/6.05  %Background operators:
% 12.73/6.05  
% 12.73/6.05  
% 12.73/6.05  %Foreground operators:
% 12.73/6.05  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.73/6.05  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.73/6.05  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.73/6.05  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.73/6.05  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 12.73/6.05  tff('#skF_2', type, '#skF_2': $i).
% 12.73/6.05  tff('#skF_3', type, '#skF_3': $i).
% 12.73/6.05  tff('#skF_1', type, '#skF_1': $i).
% 12.73/6.05  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.73/6.05  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.73/6.05  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.73/6.05  
% 12.73/6.06  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 12.73/6.06  tff(f_62, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(A, C)) => r1_tarski(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_xboole_1)).
% 12.73/6.06  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 12.73/6.06  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 12.73/6.06  tff(f_47, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 12.73/6.06  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 12.73/6.06  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 12.73/6.06  tff(f_55, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 12.73/6.06  tff(f_51, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_xboole_1)).
% 12.73/6.06  tff(f_39, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 12.73/6.06  tff(c_60, plain, (![A_28, B_29]: (r1_tarski(A_28, B_29) | k4_xboole_0(A_28, B_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.73/6.06  tff(c_24, plain, (~r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.73/6.06  tff(c_64, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_60, c_24])).
% 12.73/6.06  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.73/6.06  tff(c_99, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.73/6.06  tff(c_114, plain, (![A_5, B_6]: (k4_xboole_0(k4_xboole_0(A_5, B_6), A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_99])).
% 12.73/6.06  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.73/6.06  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.73/6.06  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.73/6.06  tff(c_44, plain, (![B_25, A_26]: (r1_xboole_0(B_25, A_26) | ~r1_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.73/6.06  tff(c_49, plain, (![A_14]: (r1_xboole_0(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_16, c_44])).
% 12.73/6.06  tff(c_261, plain, (![A_43, C_44, B_45]: (r1_xboole_0(A_43, C_44) | ~r1_xboole_0(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.73/6.06  tff(c_337, plain, (![A_50, A_51]: (r1_xboole_0(A_50, A_51) | ~r1_tarski(A_50, k1_xboole_0))), inference(resolution, [status(thm)], [c_49, c_261])).
% 12.73/6.06  tff(c_20, plain, (![A_18, B_19]: (k4_xboole_0(A_18, B_19)=A_18 | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.73/6.06  tff(c_671, plain, (![A_67, A_68]: (k4_xboole_0(A_67, A_68)=A_67 | ~r1_tarski(A_67, k1_xboole_0))), inference(resolution, [status(thm)], [c_337, c_20])).
% 12.73/6.06  tff(c_677, plain, (![A_3, A_68]: (k4_xboole_0(A_3, A_68)=A_3 | k4_xboole_0(A_3, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_671])).
% 12.73/6.06  tff(c_687, plain, (![A_3, A_68]: (k4_xboole_0(A_3, A_68)=A_3 | k1_xboole_0!=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_677])).
% 12.73/6.06  tff(c_39, plain, (![A_22, B_23]: (r1_tarski(k4_xboole_0(A_22, B_23), A_22))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.73/6.06  tff(c_42, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_39])).
% 12.73/6.06  tff(c_113, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_99])).
% 12.73/6.06  tff(c_816, plain, (![B_71, A_72, C_73]: (r1_xboole_0(B_71, k4_xboole_0(A_72, C_73)) | ~r1_xboole_0(A_72, k4_xboole_0(B_71, C_73)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 12.73/6.06  tff(c_849, plain, (![A_7, A_72]: (r1_xboole_0(A_7, k4_xboole_0(A_72, A_7)) | ~r1_xboole_0(A_72, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_113, c_816])).
% 12.73/6.06  tff(c_957, plain, (![A_76, A_77]: (r1_xboole_0(A_76, k4_xboole_0(A_77, A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_849])).
% 12.73/6.06  tff(c_2031, plain, (![A_101, A_102]: (k4_xboole_0(A_101, k4_xboole_0(A_102, A_101))=A_101)), inference(resolution, [status(thm)], [c_957, c_20])).
% 12.73/6.06  tff(c_2689, plain, (![A_68]: (k4_xboole_0(A_68, k1_xboole_0)=A_68)), inference(superposition, [status(thm), theory('equality')], [c_687, c_2031])).
% 12.73/6.06  tff(c_423, plain, (![A_57, B_58, C_59]: (k4_xboole_0(k4_xboole_0(A_57, B_58), C_59)=k4_xboole_0(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.73/6.06  tff(c_31604, plain, (![A_490, B_491]: (k4_xboole_0(A_490, k2_xboole_0(B_491, k4_xboole_0(A_490, B_491)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_423, c_113])).
% 12.73/6.06  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.73/6.06  tff(c_69, plain, (![A_32, B_33]: (k4_xboole_0(A_32, B_33)=A_32 | ~r1_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.73/6.06  tff(c_90, plain, (k4_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_26, c_69])).
% 12.73/6.06  tff(c_481, plain, (![C_59]: (k4_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_59))=k4_xboole_0('#skF_1', C_59))), inference(superposition, [status(thm), theory('equality')], [c_90, c_423])).
% 12.73/6.06  tff(c_28, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 12.73/6.06  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.73/6.06  tff(c_3400, plain, (![B_125, A_126, C_127]: (r1_xboole_0(B_125, k4_xboole_0(A_126, C_127)) | k4_xboole_0(A_126, k4_xboole_0(B_125, C_127))!=A_126)), inference(resolution, [status(thm)], [c_22, c_816])).
% 12.73/6.06  tff(c_14, plain, (![A_11, C_13, B_12]: (r1_xboole_0(A_11, C_13) | ~r1_xboole_0(B_12, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 12.73/6.06  tff(c_21961, plain, (![A_388, A_389, C_390, B_391]: (r1_xboole_0(A_388, k4_xboole_0(A_389, C_390)) | ~r1_tarski(A_388, B_391) | k4_xboole_0(A_389, k4_xboole_0(B_391, C_390))!=A_389)), inference(resolution, [status(thm)], [c_3400, c_14])).
% 12.73/6.06  tff(c_22039, plain, (![A_392, C_393]: (r1_xboole_0('#skF_1', k4_xboole_0(A_392, C_393)) | k4_xboole_0(A_392, k4_xboole_0('#skF_2', C_393))!=A_392)), inference(resolution, [status(thm)], [c_28, c_21961])).
% 12.73/6.06  tff(c_22153, plain, (![C_59]: (r1_xboole_0('#skF_1', k4_xboole_0('#skF_1', C_59)) | k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', k2_xboole_0('#skF_3', C_59)))!='#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_481, c_22039])).
% 12.73/6.06  tff(c_31638, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))) | k4_xboole_0('#skF_1', k1_xboole_0)!='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_31604, c_22153])).
% 12.73/6.06  tff(c_32287, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2689, c_31638])).
% 12.73/6.06  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.73/6.06  tff(c_32506, plain, (r1_xboole_0(k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), '#skF_1')), inference(resolution, [status(thm)], [c_32287, c_2])).
% 12.73/6.06  tff(c_32641, plain, (k4_xboole_0(k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3')), '#skF_1')=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32506, c_20])).
% 12.73/6.06  tff(c_32676, plain, (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_114, c_32641])).
% 12.73/6.06  tff(c_32678, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_32676])).
% 12.73/6.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.73/6.06  
% 12.73/6.06  Inference rules
% 12.73/6.06  ----------------------
% 12.73/6.06  #Ref     : 0
% 12.73/6.06  #Sup     : 8126
% 12.73/6.06  #Fact    : 0
% 12.73/6.06  #Define  : 0
% 12.73/6.06  #Split   : 2
% 12.73/6.06  #Chain   : 0
% 12.73/6.06  #Close   : 0
% 12.73/6.06  
% 12.73/6.06  Ordering : KBO
% 12.73/6.06  
% 12.73/6.06  Simplification rules
% 12.73/6.06  ----------------------
% 12.73/6.06  #Subsume      : 1496
% 12.73/6.06  #Demod        : 6435
% 12.73/6.06  #Tautology    : 4092
% 12.73/6.06  #SimpNegUnit  : 136
% 12.73/6.06  #BackRed      : 1
% 12.73/6.06  
% 12.73/6.06  #Partial instantiations: 0
% 12.73/6.06  #Strategies tried      : 1
% 12.73/6.06  
% 12.73/6.06  Timing (in seconds)
% 12.73/6.06  ----------------------
% 12.73/6.07  Preprocessing        : 0.28
% 12.73/6.07  Parsing              : 0.16
% 12.73/6.07  CNF conversion       : 0.02
% 12.73/6.07  Main loop            : 5.01
% 12.73/6.07  Inferencing          : 0.83
% 12.73/6.07  Reduction            : 2.73
% 12.73/6.07  Demodulation         : 2.33
% 12.73/6.07  BG Simplification    : 0.09
% 12.73/6.07  Subsumption          : 1.13
% 12.73/6.07  Abstraction          : 0.13
% 12.73/6.07  MUC search           : 0.00
% 12.73/6.07  Cooper               : 0.00
% 12.73/6.07  Total                : 5.32
% 12.73/6.07  Index Insertion      : 0.00
% 12.73/6.07  Index Deletion       : 0.00
% 12.73/6.07  Index Matching       : 0.00
% 12.73/6.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
