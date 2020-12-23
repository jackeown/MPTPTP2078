%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:50 EST 2020

% Result     : Theorem 2.60s
% Output     : CNFRefutation 2.60s
% Verified   : 
% Statistics : Number of formulae       :   54 (  68 expanded)
%              Number of leaves         :   22 (  31 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  70 expanded)
%              Number of equality atoms :   27 (  36 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k2_xboole_0(B,C)) = k2_xboole_0(k3_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_24,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_29,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_202,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_216,plain,(
    k3_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_29,c_202])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_39,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_42,plain,(
    ! [A_7] : r1_tarski(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_39])).

tff(c_130,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = k1_xboole_0
      | ~ r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_145,plain,(
    ! [A_7] : k4_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_42,c_130])).

tff(c_313,plain,(
    ! [A_50,B_51] : k2_xboole_0(A_50,k4_xboole_0(B_51,A_50)) = k2_xboole_0(A_50,B_51) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_349,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = k2_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_145,c_313])).

tff(c_359,plain,(
    ! [A_52] : k2_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_349])).

tff(c_401,plain,(
    ! [B_2] : k2_xboole_0(k1_xboole_0,B_2) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_359])).

tff(c_26,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_300,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = k1_xboole_0
      | ~ r1_xboole_0(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_308,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_300])).

tff(c_587,plain,(
    ! [A_57,B_58,C_59] : k2_xboole_0(k3_xboole_0(A_57,B_58),k3_xboole_0(A_57,C_59)) = k3_xboole_0(A_57,k2_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_630,plain,(
    ! [C_59] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_59)) = k2_xboole_0(k1_xboole_0,k3_xboole_0('#skF_1',C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_587])).

tff(c_696,plain,(
    ! [C_60] : k3_xboole_0('#skF_1',k2_xboole_0('#skF_3',C_60)) = k3_xboole_0('#skF_1',C_60) ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_630])).

tff(c_730,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_216,c_696])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [B_24,A_25] : k2_xboole_0(B_24,A_25) = k2_xboole_0(A_25,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_25,B_24] : r1_tarski(A_25,k2_xboole_0(B_24,A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_22])).

tff(c_215,plain,(
    ! [A_25,B_24] : k3_xboole_0(A_25,k2_xboole_0(B_24,A_25)) = A_25 ),
    inference(resolution,[status(thm)],[c_59,c_202])).

tff(c_974,plain,(
    ! [A_67,B_68,C_69] : r1_tarski(k3_xboole_0(A_67,B_68),k3_xboole_0(A_67,k2_xboole_0(B_68,C_69))) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_22])).

tff(c_1082,plain,(
    ! [A_70,B_71] : r1_tarski(k3_xboole_0(A_70,B_71),A_70) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_974])).

tff(c_1134,plain,(
    ! [B_72,A_73] : r1_tarski(k3_xboole_0(B_72,A_73),A_73) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1082])).

tff(c_1143,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_730,c_1134])).

tff(c_1177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1143])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:59:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.60/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  
% 2.60/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.36  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.60/1.36  
% 2.60/1.36  %Foreground sorts:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Background operators:
% 2.60/1.36  
% 2.60/1.36  
% 2.60/1.36  %Foreground operators:
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.60/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.60/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.60/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.60/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.60/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.60/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.60/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.60/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.60/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.60/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.60/1.36  
% 2.60/1.37  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.60/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.60/1.37  tff(f_45, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.60/1.37  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.60/1.37  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.60/1.37  tff(f_39, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.60/1.37  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.60/1.37  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.60/1.37  tff(f_41, axiom, (![A, B, C]: (k3_xboole_0(A, k2_xboole_0(B, C)) = k2_xboole_0(k3_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_xboole_1)).
% 2.60/1.37  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.60/1.37  tff(c_24, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.37  tff(c_28, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.37  tff(c_29, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 2.60/1.37  tff(c_202, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.60/1.37  tff(c_216, plain, (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_29, c_202])).
% 2.60/1.37  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.60/1.37  tff(c_39, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.37  tff(c_42, plain, (![A_7]: (r1_tarski(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_39])).
% 2.60/1.37  tff(c_130, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=k1_xboole_0 | ~r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.60/1.37  tff(c_145, plain, (![A_7]: (k4_xboole_0(A_7, A_7)=k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_130])).
% 2.60/1.37  tff(c_313, plain, (![A_50, B_51]: (k2_xboole_0(A_50, k4_xboole_0(B_51, A_50))=k2_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.60/1.37  tff(c_349, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=k2_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_145, c_313])).
% 2.60/1.37  tff(c_359, plain, (![A_52]: (k2_xboole_0(A_52, k1_xboole_0)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_349])).
% 2.60/1.37  tff(c_401, plain, (![B_2]: (k2_xboole_0(k1_xboole_0, B_2)=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_359])).
% 2.60/1.37  tff(c_26, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.60/1.37  tff(c_300, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=k1_xboole_0 | ~r1_xboole_0(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.60/1.37  tff(c_308, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_300])).
% 2.60/1.37  tff(c_587, plain, (![A_57, B_58, C_59]: (k2_xboole_0(k3_xboole_0(A_57, B_58), k3_xboole_0(A_57, C_59))=k3_xboole_0(A_57, k2_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.60/1.37  tff(c_630, plain, (![C_59]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_59))=k2_xboole_0(k1_xboole_0, k3_xboole_0('#skF_1', C_59)))), inference(superposition, [status(thm), theory('equality')], [c_308, c_587])).
% 2.60/1.37  tff(c_696, plain, (![C_60]: (k3_xboole_0('#skF_1', k2_xboole_0('#skF_3', C_60))=k3_xboole_0('#skF_1', C_60))), inference(demodulation, [status(thm), theory('equality')], [c_401, c_630])).
% 2.60/1.37  tff(c_730, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_216, c_696])).
% 2.60/1.37  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.60/1.37  tff(c_44, plain, (![B_24, A_25]: (k2_xboole_0(B_24, A_25)=k2_xboole_0(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.60/1.37  tff(c_22, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.60/1.37  tff(c_59, plain, (![A_25, B_24]: (r1_tarski(A_25, k2_xboole_0(B_24, A_25)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_22])).
% 2.60/1.37  tff(c_215, plain, (![A_25, B_24]: (k3_xboole_0(A_25, k2_xboole_0(B_24, A_25))=A_25)), inference(resolution, [status(thm)], [c_59, c_202])).
% 2.60/1.37  tff(c_974, plain, (![A_67, B_68, C_69]: (r1_tarski(k3_xboole_0(A_67, B_68), k3_xboole_0(A_67, k2_xboole_0(B_68, C_69))))), inference(superposition, [status(thm), theory('equality')], [c_587, c_22])).
% 2.60/1.37  tff(c_1082, plain, (![A_70, B_71]: (r1_tarski(k3_xboole_0(A_70, B_71), A_70))), inference(superposition, [status(thm), theory('equality')], [c_215, c_974])).
% 2.60/1.37  tff(c_1134, plain, (![B_72, A_73]: (r1_tarski(k3_xboole_0(B_72, A_73), A_73))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1082])).
% 2.60/1.37  tff(c_1143, plain, (r1_tarski('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_730, c_1134])).
% 2.60/1.37  tff(c_1177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1143])).
% 2.60/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.60/1.37  
% 2.60/1.37  Inference rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Ref     : 0
% 2.60/1.37  #Sup     : 287
% 2.60/1.37  #Fact    : 0
% 2.60/1.37  #Define  : 0
% 2.60/1.37  #Split   : 0
% 2.60/1.37  #Chain   : 0
% 2.60/1.37  #Close   : 0
% 2.60/1.37  
% 2.60/1.37  Ordering : KBO
% 2.60/1.37  
% 2.60/1.37  Simplification rules
% 2.60/1.37  ----------------------
% 2.60/1.37  #Subsume      : 0
% 2.60/1.37  #Demod        : 144
% 2.60/1.37  #Tautology    : 192
% 2.60/1.37  #SimpNegUnit  : 1
% 2.60/1.37  #BackRed      : 0
% 2.60/1.37  
% 2.60/1.37  #Partial instantiations: 0
% 2.60/1.37  #Strategies tried      : 1
% 2.60/1.37  
% 2.60/1.37  Timing (in seconds)
% 2.60/1.37  ----------------------
% 2.60/1.38  Preprocessing        : 0.27
% 2.60/1.38  Parsing              : 0.15
% 2.60/1.38  CNF conversion       : 0.02
% 2.60/1.38  Main loop            : 0.36
% 2.60/1.38  Inferencing          : 0.12
% 2.60/1.38  Reduction            : 0.15
% 2.60/1.38  Demodulation         : 0.12
% 2.60/1.38  BG Simplification    : 0.02
% 2.60/1.38  Subsumption          : 0.05
% 2.60/1.38  Abstraction          : 0.02
% 2.60/1.38  MUC search           : 0.00
% 2.60/1.38  Cooper               : 0.00
% 2.60/1.38  Total                : 0.66
% 2.60/1.38  Index Insertion      : 0.00
% 2.60/1.38  Index Deletion       : 0.00
% 2.60/1.38  Index Matching       : 0.00
% 2.60/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
