%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:10 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.49s
% Verified   : 
% Statistics : Number of formulae       :   56 ( 189 expanded)
%              Number of leaves         :   20 (  74 expanded)
%              Depth                    :   15
%              Number of atoms          :   51 ( 221 expanded)
%              Number of equality atoms :   35 ( 138 expanded)
%              Maximal formula depth    :    8 (   3 average)
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

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_tarski(A,C)
          & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_45,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_64,plain,(
    ! [A_24,B_25] :
      ( r1_xboole_0(A_24,B_25)
      | k3_xboole_0(A_24,B_25) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_72,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_24])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] : k3_xboole_0(k3_xboole_0(A_3,B_4),C_5) = k3_xboole_0(A_3,k3_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ! [A_15] : r1_xboole_0(A_15,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_36,plain,(
    ! [A_20,B_21] :
      ( k3_xboole_0(A_20,B_21) = k1_xboole_0
      | ~ r1_xboole_0(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_44,plain,(
    ! [A_15] : k3_xboole_0(A_15,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_36])).

tff(c_213,plain,(
    ! [A_34,B_35] : k4_xboole_0(A_34,k4_xboole_0(A_34,B_35)) = k3_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_242,plain,(
    ! [A_10] : k4_xboole_0(A_10,A_10) = k3_xboole_0(A_10,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_213])).

tff(c_250,plain,(
    ! [A_36] : k4_xboole_0(A_36,A_36) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_242])).

tff(c_14,plain,(
    ! [A_11,B_12] : k4_xboole_0(A_11,k4_xboole_0(A_11,B_12)) = k3_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_255,plain,(
    ! [A_36] : k4_xboole_0(A_36,k1_xboole_0) = k3_xboole_0(A_36,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_14])).

tff(c_276,plain,(
    ! [A_36] : k3_xboole_0(A_36,A_36) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_255])).

tff(c_8,plain,(
    ! [A_6,B_7] : r1_tarski(k3_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_73,plain,(
    ! [A_26,B_27] :
      ( k3_xboole_0(A_26,B_27) = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_431,plain,(
    ! [A_43,B_44] : k3_xboole_0(k3_xboole_0(A_43,B_44),A_43) = k3_xboole_0(A_43,B_44) ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_84,plain,(
    ! [A_6,B_7] : k3_xboole_0(k3_xboole_0(A_6,B_7),A_6) = k3_xboole_0(A_6,B_7) ),
    inference(resolution,[status(thm)],[c_8,c_73])).

tff(c_434,plain,(
    ! [A_43,B_44] : k3_xboole_0(k3_xboole_0(A_43,B_44),k3_xboole_0(A_43,B_44)) = k3_xboole_0(k3_xboole_0(A_43,B_44),A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_84])).

tff(c_486,plain,(
    ! [A_43,B_44] : k3_xboole_0(A_43,k3_xboole_0(B_44,A_43)) = k3_xboole_0(A_43,B_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_276,c_434])).

tff(c_20,plain,(
    r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_43,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_36])).

tff(c_534,plain,(
    ! [A_46,B_47] : k3_xboole_0(A_46,k3_xboole_0(B_47,A_46)) = k3_xboole_0(A_46,B_47) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_276,c_434])).

tff(c_607,plain,(
    k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),k1_xboole_0) = k3_xboole_0(k3_xboole_0('#skF_2','#skF_3'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_43,c_534])).

tff(c_630,plain,(
    k3_xboole_0('#skF_2',k3_xboole_0('#skF_3','#skF_1')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_44,c_607])).

tff(c_635,plain,(
    k3_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k1_xboole_0) = k3_xboole_0(k3_xboole_0('#skF_3','#skF_1'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_630,c_486])).

tff(c_650,plain,(
    k3_xboole_0('#skF_3',k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_44,c_635])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_73])).

tff(c_372,plain,(
    ! [A_40,B_41,C_42] : k3_xboole_0(k3_xboole_0(A_40,B_41),C_42) = k3_xboole_0(A_40,k3_xboole_0(B_41,C_42)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_411,plain,(
    ! [C_42] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_3',C_42)) = k3_xboole_0('#skF_1',C_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_372])).

tff(c_661,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k3_xboole_0('#skF_1',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_650,c_411])).

tff(c_677,plain,(
    k3_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_661])).

tff(c_685,plain,(
    k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k3_xboole_0(k3_xboole_0('#skF_1','#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_486])).

tff(c_700,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_486,c_6,c_44,c_685])).

tff(c_702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_700])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n004.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:44:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  
% 2.14/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.30  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.14/1.30  
% 2.14/1.30  %Foreground sorts:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Background operators:
% 2.14/1.30  
% 2.14/1.30  
% 2.14/1.30  %Foreground operators:
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.14/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.14/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.14/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.14/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.30  
% 2.49/1.31  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.49/1.31  tff(f_54, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.49/1.31  tff(f_31, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 2.49/1.31  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.49/1.31  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.49/1.31  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.49/1.31  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.49/1.31  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.49/1.31  tff(c_64, plain, (![A_24, B_25]: (r1_xboole_0(A_24, B_25) | k3_xboole_0(A_24, B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.31  tff(c_24, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.49/1.31  tff(c_72, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_64, c_24])).
% 2.49/1.31  tff(c_6, plain, (![A_3, B_4, C_5]: (k3_xboole_0(k3_xboole_0(A_3, B_4), C_5)=k3_xboole_0(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.31  tff(c_12, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.49/1.31  tff(c_18, plain, (![A_15]: (r1_xboole_0(A_15, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.49/1.31  tff(c_36, plain, (![A_20, B_21]: (k3_xboole_0(A_20, B_21)=k1_xboole_0 | ~r1_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.49/1.31  tff(c_44, plain, (![A_15]: (k3_xboole_0(A_15, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_36])).
% 2.49/1.31  tff(c_213, plain, (![A_34, B_35]: (k4_xboole_0(A_34, k4_xboole_0(A_34, B_35))=k3_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.31  tff(c_242, plain, (![A_10]: (k4_xboole_0(A_10, A_10)=k3_xboole_0(A_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_213])).
% 2.49/1.31  tff(c_250, plain, (![A_36]: (k4_xboole_0(A_36, A_36)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_44, c_242])).
% 2.49/1.31  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, k4_xboole_0(A_11, B_12))=k3_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.49/1.31  tff(c_255, plain, (![A_36]: (k4_xboole_0(A_36, k1_xboole_0)=k3_xboole_0(A_36, A_36))), inference(superposition, [status(thm), theory('equality')], [c_250, c_14])).
% 2.49/1.31  tff(c_276, plain, (![A_36]: (k3_xboole_0(A_36, A_36)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_255])).
% 2.49/1.31  tff(c_8, plain, (![A_6, B_7]: (r1_tarski(k3_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.49/1.31  tff(c_73, plain, (![A_26, B_27]: (k3_xboole_0(A_26, B_27)=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.49/1.31  tff(c_431, plain, (![A_43, B_44]: (k3_xboole_0(k3_xboole_0(A_43, B_44), A_43)=k3_xboole_0(A_43, B_44))), inference(resolution, [status(thm)], [c_8, c_73])).
% 2.49/1.31  tff(c_84, plain, (![A_6, B_7]: (k3_xboole_0(k3_xboole_0(A_6, B_7), A_6)=k3_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_8, c_73])).
% 2.49/1.31  tff(c_434, plain, (![A_43, B_44]: (k3_xboole_0(k3_xboole_0(A_43, B_44), k3_xboole_0(A_43, B_44))=k3_xboole_0(k3_xboole_0(A_43, B_44), A_43))), inference(superposition, [status(thm), theory('equality')], [c_431, c_84])).
% 2.49/1.31  tff(c_486, plain, (![A_43, B_44]: (k3_xboole_0(A_43, k3_xboole_0(B_44, A_43))=k3_xboole_0(A_43, B_44))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_276, c_434])).
% 2.49/1.31  tff(c_20, plain, (r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.49/1.31  tff(c_43, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_36])).
% 2.49/1.31  tff(c_534, plain, (![A_46, B_47]: (k3_xboole_0(A_46, k3_xboole_0(B_47, A_46))=k3_xboole_0(A_46, B_47))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_276, c_434])).
% 2.49/1.31  tff(c_607, plain, (k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), k1_xboole_0)=k3_xboole_0(k3_xboole_0('#skF_2', '#skF_3'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_43, c_534])).
% 2.49/1.31  tff(c_630, plain, (k3_xboole_0('#skF_2', k3_xboole_0('#skF_3', '#skF_1'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_44, c_607])).
% 2.49/1.31  tff(c_635, plain, (k3_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k1_xboole_0)=k3_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_630, c_486])).
% 2.49/1.31  tff(c_650, plain, (k3_xboole_0('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_44, c_635])).
% 2.49/1.31  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.49/1.31  tff(c_85, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_73])).
% 2.49/1.31  tff(c_372, plain, (![A_40, B_41, C_42]: (k3_xboole_0(k3_xboole_0(A_40, B_41), C_42)=k3_xboole_0(A_40, k3_xboole_0(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.49/1.31  tff(c_411, plain, (![C_42]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_3', C_42))=k3_xboole_0('#skF_1', C_42))), inference(superposition, [status(thm), theory('equality')], [c_85, c_372])).
% 2.49/1.31  tff(c_661, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_650, c_411])).
% 2.49/1.31  tff(c_677, plain, (k3_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_44, c_661])).
% 2.49/1.31  tff(c_685, plain, (k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k3_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_677, c_486])).
% 2.49/1.31  tff(c_700, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_486, c_6, c_44, c_685])).
% 2.49/1.31  tff(c_702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_700])).
% 2.49/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.31  
% 2.49/1.31  Inference rules
% 2.49/1.31  ----------------------
% 2.49/1.31  #Ref     : 0
% 2.49/1.31  #Sup     : 174
% 2.49/1.31  #Fact    : 0
% 2.49/1.31  #Define  : 0
% 2.49/1.31  #Split   : 0
% 2.49/1.31  #Chain   : 0
% 2.49/1.31  #Close   : 0
% 2.49/1.31  
% 2.49/1.31  Ordering : KBO
% 2.49/1.31  
% 2.49/1.31  Simplification rules
% 2.49/1.31  ----------------------
% 2.49/1.31  #Subsume      : 0
% 2.49/1.31  #Demod        : 124
% 2.49/1.31  #Tautology    : 119
% 2.49/1.31  #SimpNegUnit  : 1
% 2.49/1.31  #BackRed      : 3
% 2.49/1.31  
% 2.49/1.31  #Partial instantiations: 0
% 2.49/1.31  #Strategies tried      : 1
% 2.49/1.31  
% 2.49/1.31  Timing (in seconds)
% 2.49/1.31  ----------------------
% 2.49/1.32  Preprocessing        : 0.26
% 2.49/1.32  Parsing              : 0.15
% 2.49/1.32  CNF conversion       : 0.02
% 2.49/1.32  Main loop            : 0.28
% 2.49/1.32  Inferencing          : 0.11
% 2.49/1.32  Reduction            : 0.10
% 2.49/1.32  Demodulation         : 0.08
% 2.49/1.32  BG Simplification    : 0.01
% 2.49/1.32  Subsumption          : 0.04
% 2.49/1.32  Abstraction          : 0.01
% 2.49/1.32  MUC search           : 0.00
% 2.49/1.32  Cooper               : 0.00
% 2.49/1.32  Total                : 0.57
% 2.49/1.32  Index Insertion      : 0.00
% 2.49/1.32  Index Deletion       : 0.00
% 2.49/1.32  Index Matching       : 0.00
% 2.49/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
