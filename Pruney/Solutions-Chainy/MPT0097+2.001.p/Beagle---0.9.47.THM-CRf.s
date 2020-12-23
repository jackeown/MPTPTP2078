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
% DateTime   : Thu Dec  3 09:44:35 EST 2020

% Result     : Theorem 3.12s
% Output     : CNFRefutation 3.12s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 151 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 162 expanded)
%              Number of equality atoms :   33 ( 117 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k3_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l36_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,k3_xboole_0(A,B)),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_xboole_1)).

tff(c_67,plain,(
    ! [A_30,B_31] : k2_xboole_0(k3_xboole_0(A_30,B_31),k4_xboole_0(A_30,B_31)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_30,B_31] : k4_xboole_0(k3_xboole_0(A_30,B_31),A_30) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_153,plain,(
    ! [A_36,B_37,C_38] : k4_xboole_0(k3_xboole_0(A_36,B_37),C_38) = k3_xboole_0(A_36,k4_xboole_0(B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_222,plain,(
    ! [A_40,B_41] : k3_xboole_0(A_40,k4_xboole_0(B_41,A_40)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_153])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(k3_xboole_0(A_12,B_13),k4_xboole_0(A_12,B_13)) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_892,plain,(
    ! [A_63,B_64] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_63,k4_xboole_0(B_64,A_63))) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_14])).

tff(c_16,plain,(
    ! [A_14] : r1_xboole_0(A_14,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_44,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = A_25
      | ~ r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_85,plain,(
    ! [A_6] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_6,k1_xboole_0)) = A_6 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_67])).

tff(c_89,plain,(
    ! [A_6] : k2_xboole_0(k1_xboole_0,A_6) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_85])).

tff(c_905,plain,(
    ! [A_63,B_64] : k4_xboole_0(A_63,k4_xboole_0(B_64,A_63)) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_89])).

tff(c_967,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k4_xboole_0(B_66,A_65)) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_892,c_89])).

tff(c_1008,plain,(
    ! [B_64,A_63] : k4_xboole_0(k4_xboole_0(B_64,A_63),A_63) = k4_xboole_0(B_64,A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_967])).

tff(c_131,plain,(
    ! [A_34,B_35] : k4_xboole_0(k3_xboole_0(A_34,B_35),A_34) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_10])).

tff(c_140,plain,(
    ! [B_35] : k3_xboole_0(k1_xboole_0,B_35) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_131,c_52])).

tff(c_267,plain,(
    ! [A_42,B_43,C_44] : k2_xboole_0(k4_xboole_0(A_42,B_43),k4_xboole_0(A_42,C_44)) = k4_xboole_0(A_42,k3_xboole_0(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_297,plain,(
    ! [A_14,C_44] : k4_xboole_0(A_14,k3_xboole_0(k1_xboole_0,C_44)) = k2_xboole_0(A_14,k4_xboole_0(A_14,C_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_267])).

tff(c_319,plain,(
    ! [A_45,C_46] : k2_xboole_0(A_45,k4_xboole_0(A_45,C_46)) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_140,c_297])).

tff(c_357,plain,(
    ! [A_47] : k4_xboole_0(A_47,A_47) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_10])).

tff(c_6,plain,(
    ! [A_3,B_4,C_5] : k2_xboole_0(k4_xboole_0(A_3,B_4),k4_xboole_0(A_3,C_5)) = k4_xboole_0(A_3,k3_xboole_0(B_4,C_5)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_365,plain,(
    ! [A_47,C_5] : k4_xboole_0(A_47,k3_xboole_0(A_47,C_5)) = k2_xboole_0(k1_xboole_0,k4_xboole_0(A_47,C_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_357,c_6])).

tff(c_400,plain,(
    ! [A_47,C_5] : k4_xboole_0(A_47,k3_xboole_0(A_47,C_5)) = k4_xboole_0(A_47,C_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_365])).

tff(c_39,plain,(
    ! [A_23,B_24] :
      ( r1_xboole_0(A_23,B_24)
      | k4_xboole_0(A_23,B_24) != A_23 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_22,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_43,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')),'#skF_2') != k4_xboole_0('#skF_1',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_39,c_22])).

tff(c_1645,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_2') != k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_400,c_400,c_43])).

tff(c_2482,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:36:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.12/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.49  
% 3.12/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.49  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 3.12/1.49  
% 3.12/1.49  %Foreground sorts:
% 3.12/1.49  
% 3.12/1.49  
% 3.12/1.49  %Background operators:
% 3.12/1.49  
% 3.12/1.49  
% 3.12/1.49  %Foreground operators:
% 3.12/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.12/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.12/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.12/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.12/1.49  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.12/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.12/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.12/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.12/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.12/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.12/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.12/1.49  
% 3.12/1.50  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 3.12/1.50  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.12/1.50  tff(f_37, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 3.12/1.50  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.12/1.50  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.12/1.50  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.12/1.50  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(A, k3_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l36_xboole_1)).
% 3.12/1.50  tff(f_48, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, k3_xboole_0(A, B)), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_xboole_1)).
% 3.12/1.50  tff(c_67, plain, (![A_30, B_31]: (k2_xboole_0(k3_xboole_0(A_30, B_31), k4_xboole_0(A_30, B_31))=A_30)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.50  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.12/1.50  tff(c_73, plain, (![A_30, B_31]: (k4_xboole_0(k3_xboole_0(A_30, B_31), A_30)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67, c_10])).
% 3.12/1.50  tff(c_153, plain, (![A_36, B_37, C_38]: (k4_xboole_0(k3_xboole_0(A_36, B_37), C_38)=k3_xboole_0(A_36, k4_xboole_0(B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.12/1.50  tff(c_222, plain, (![A_40, B_41]: (k3_xboole_0(A_40, k4_xboole_0(B_41, A_40))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_153])).
% 3.12/1.50  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(k3_xboole_0(A_12, B_13), k4_xboole_0(A_12, B_13))=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.12/1.50  tff(c_892, plain, (![A_63, B_64]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_63, k4_xboole_0(B_64, A_63)))=A_63)), inference(superposition, [status(thm), theory('equality')], [c_222, c_14])).
% 3.12/1.50  tff(c_16, plain, (![A_14]: (r1_xboole_0(A_14, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.12/1.50  tff(c_44, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=A_25 | ~r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.12/1.50  tff(c_52, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(resolution, [status(thm)], [c_16, c_44])).
% 3.12/1.50  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.12/1.50  tff(c_85, plain, (![A_6]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_6, k1_xboole_0))=A_6)), inference(superposition, [status(thm), theory('equality')], [c_8, c_67])).
% 3.12/1.50  tff(c_89, plain, (![A_6]: (k2_xboole_0(k1_xboole_0, A_6)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_85])).
% 3.12/1.50  tff(c_905, plain, (![A_63, B_64]: (k4_xboole_0(A_63, k4_xboole_0(B_64, A_63))=A_63)), inference(superposition, [status(thm), theory('equality')], [c_892, c_89])).
% 3.12/1.50  tff(c_967, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k4_xboole_0(B_66, A_65))=A_65)), inference(superposition, [status(thm), theory('equality')], [c_892, c_89])).
% 3.12/1.50  tff(c_1008, plain, (![B_64, A_63]: (k4_xboole_0(k4_xboole_0(B_64, A_63), A_63)=k4_xboole_0(B_64, A_63))), inference(superposition, [status(thm), theory('equality')], [c_905, c_967])).
% 3.12/1.50  tff(c_131, plain, (![A_34, B_35]: (k4_xboole_0(k3_xboole_0(A_34, B_35), A_34)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_67, c_10])).
% 3.12/1.50  tff(c_140, plain, (![B_35]: (k3_xboole_0(k1_xboole_0, B_35)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_131, c_52])).
% 3.12/1.50  tff(c_267, plain, (![A_42, B_43, C_44]: (k2_xboole_0(k4_xboole_0(A_42, B_43), k4_xboole_0(A_42, C_44))=k4_xboole_0(A_42, k3_xboole_0(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.50  tff(c_297, plain, (![A_14, C_44]: (k4_xboole_0(A_14, k3_xboole_0(k1_xboole_0, C_44))=k2_xboole_0(A_14, k4_xboole_0(A_14, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_267])).
% 3.12/1.50  tff(c_319, plain, (![A_45, C_46]: (k2_xboole_0(A_45, k4_xboole_0(A_45, C_46))=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_52, c_140, c_297])).
% 3.12/1.50  tff(c_357, plain, (![A_47]: (k4_xboole_0(A_47, A_47)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_319, c_10])).
% 3.12/1.50  tff(c_6, plain, (![A_3, B_4, C_5]: (k2_xboole_0(k4_xboole_0(A_3, B_4), k4_xboole_0(A_3, C_5))=k4_xboole_0(A_3, k3_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.12/1.50  tff(c_365, plain, (![A_47, C_5]: (k4_xboole_0(A_47, k3_xboole_0(A_47, C_5))=k2_xboole_0(k1_xboole_0, k4_xboole_0(A_47, C_5)))), inference(superposition, [status(thm), theory('equality')], [c_357, c_6])).
% 3.12/1.50  tff(c_400, plain, (![A_47, C_5]: (k4_xboole_0(A_47, k3_xboole_0(A_47, C_5))=k4_xboole_0(A_47, C_5))), inference(demodulation, [status(thm), theory('equality')], [c_89, c_365])).
% 3.12/1.50  tff(c_39, plain, (![A_23, B_24]: (r1_xboole_0(A_23, B_24) | k4_xboole_0(A_23, B_24)!=A_23)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.12/1.50  tff(c_22, plain, (~r1_xboole_0(k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2')), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.12/1.50  tff(c_43, plain, (k4_xboole_0(k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2')), '#skF_2')!=k4_xboole_0('#skF_1', k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_39, c_22])).
% 3.12/1.50  tff(c_1645, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_2')!=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_400, c_400, c_43])).
% 3.12/1.50  tff(c_2482, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1645])).
% 3.12/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.12/1.50  
% 3.12/1.50  Inference rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Ref     : 0
% 3.12/1.50  #Sup     : 616
% 3.12/1.50  #Fact    : 0
% 3.12/1.50  #Define  : 0
% 3.12/1.50  #Split   : 0
% 3.12/1.50  #Chain   : 0
% 3.12/1.50  #Close   : 0
% 3.12/1.50  
% 3.12/1.50  Ordering : KBO
% 3.12/1.50  
% 3.12/1.50  Simplification rules
% 3.12/1.50  ----------------------
% 3.12/1.50  #Subsume      : 1
% 3.12/1.50  #Demod        : 485
% 3.12/1.50  #Tautology    : 442
% 3.12/1.50  #SimpNegUnit  : 0
% 3.12/1.50  #BackRed      : 6
% 3.12/1.50  
% 3.12/1.50  #Partial instantiations: 0
% 3.12/1.50  #Strategies tried      : 1
% 3.12/1.50  
% 3.12/1.50  Timing (in seconds)
% 3.12/1.50  ----------------------
% 3.12/1.50  Preprocessing        : 0.26
% 3.12/1.50  Parsing              : 0.14
% 3.12/1.50  CNF conversion       : 0.02
% 3.12/1.50  Main loop            : 0.46
% 3.12/1.50  Inferencing          : 0.17
% 3.12/1.50  Reduction            : 0.17
% 3.12/1.50  Demodulation         : 0.14
% 3.12/1.50  BG Simplification    : 0.02
% 3.12/1.50  Subsumption          : 0.06
% 3.12/1.50  Abstraction          : 0.03
% 3.12/1.50  MUC search           : 0.00
% 3.12/1.50  Cooper               : 0.00
% 3.12/1.50  Total                : 0.74
% 3.12/1.50  Index Insertion      : 0.00
% 3.12/1.50  Index Deletion       : 0.00
% 3.12/1.50  Index Matching       : 0.00
% 3.12/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
