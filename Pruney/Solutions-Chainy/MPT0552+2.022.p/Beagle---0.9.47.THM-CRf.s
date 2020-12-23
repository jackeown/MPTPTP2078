%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:59 EST 2020

% Result     : Theorem 12.93s
% Output     : CNFRefutation 12.93s
% Verified   : 
% Statistics : Number of formulae       :   50 (  70 expanded)
%              Number of leaves         :   24 (  34 expanded)
%              Depth                    :    6
%              Number of atoms          :   61 (  97 expanded)
%              Number of equality atoms :   13 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k9_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t153_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_65,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_116,plain,(
    ! [B_39,A_40] : k1_setfam_1(k2_tarski(B_39,A_40)) = k3_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_65])).

tff(c_22,plain,(
    ! [A_20,B_21] : k1_setfam_1(k2_tarski(A_20,B_21)) = k3_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_122,plain,(
    ! [B_39,A_40] : k3_xboole_0(B_39,A_40) = k3_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_22])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_80,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_87,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_80])).

tff(c_466,plain,(
    ! [C_78,A_79,B_80] :
      ( k2_xboole_0(k9_relat_1(C_78,A_79),k9_relat_1(C_78,B_80)) = k9_relat_1(C_78,k2_xboole_0(A_79,B_80))
      | ~ v1_relat_1(C_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8391,plain,(
    ! [C_267,A_268,C_269,B_270] :
      ( r1_tarski(k9_relat_1(C_267,A_268),C_269)
      | ~ r1_tarski(k9_relat_1(C_267,k2_xboole_0(A_268,B_270)),C_269)
      | ~ v1_relat_1(C_267) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_8])).

tff(c_14895,plain,(
    ! [C_393,A_394,B_395,C_396] :
      ( r1_tarski(k9_relat_1(C_393,k3_xboole_0(A_394,B_395)),C_396)
      | ~ r1_tarski(k9_relat_1(C_393,A_394),C_396)
      | ~ v1_relat_1(C_393) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_8391])).

tff(c_41673,plain,(
    ! [C_709,A_710,B_711,C_712] :
      ( r1_tarski(k9_relat_1(C_709,k3_xboole_0(A_710,B_711)),C_712)
      | ~ r1_tarski(k9_relat_1(C_709,B_711),C_712)
      | ~ v1_relat_1(C_709) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_14895])).

tff(c_1088,plain,(
    ! [C_104,A_105,C_106,B_107] :
      ( r1_tarski(k9_relat_1(C_104,A_105),C_106)
      | ~ r1_tarski(k9_relat_1(C_104,k2_xboole_0(A_105,B_107)),C_106)
      | ~ v1_relat_1(C_104) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_466,c_8])).

tff(c_7003,plain,(
    ! [C_229,A_230,B_231,C_232] :
      ( r1_tarski(k9_relat_1(C_229,k3_xboole_0(A_230,B_231)),C_232)
      | ~ r1_tarski(k9_relat_1(C_229,A_230),C_232)
      | ~ v1_relat_1(C_229) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_1088])).

tff(c_392,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_26,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_413,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_392,c_26])).

tff(c_528,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_413])).

tff(c_7021,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7003,c_528])).

tff(c_7089,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_7021])).

tff(c_7090,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_413])).

tff(c_41738,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3','#skF_2'),k9_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_41673,c_7090])).

tff(c_41873,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_6,c_41738])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:19:35 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.93/6.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.93/6.33  
% 12.93/6.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.93/6.34  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 12.93/6.34  
% 12.93/6.34  %Foreground sorts:
% 12.93/6.34  
% 12.93/6.34  
% 12.93/6.34  %Background operators:
% 12.93/6.34  
% 12.93/6.34  
% 12.93/6.34  %Foreground operators:
% 12.93/6.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.93/6.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.93/6.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.93/6.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.93/6.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.93/6.34  tff('#skF_2', type, '#skF_2': $i).
% 12.93/6.34  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 12.93/6.34  tff('#skF_3', type, '#skF_3': $i).
% 12.93/6.34  tff('#skF_1', type, '#skF_1': $i).
% 12.93/6.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.93/6.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 12.93/6.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.93/6.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.93/6.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.93/6.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 12.93/6.34  
% 12.93/6.35  tff(f_64, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 12.93/6.35  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 12.93/6.35  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 12.93/6.35  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 12.93/6.35  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 12.93/6.35  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.93/6.35  tff(f_59, axiom, (![A, B, C]: (v1_relat_1(C) => (k9_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t153_relat_1)).
% 12.93/6.35  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 12.93/6.35  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 12.93/6.35  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.93/6.35  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.93/6.35  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 12.93/6.35  tff(c_65, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.93/6.35  tff(c_116, plain, (![B_39, A_40]: (k1_setfam_1(k2_tarski(B_39, A_40))=k3_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_16, c_65])).
% 12.93/6.35  tff(c_22, plain, (![A_20, B_21]: (k1_setfam_1(k2_tarski(A_20, B_21))=k3_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.93/6.35  tff(c_122, plain, (![B_39, A_40]: (k3_xboole_0(B_39, A_40)=k3_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_116, c_22])).
% 12.93/6.35  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 12.93/6.35  tff(c_80, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.93/6.35  tff(c_87, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_80])).
% 12.93/6.35  tff(c_466, plain, (![C_78, A_79, B_80]: (k2_xboole_0(k9_relat_1(C_78, A_79), k9_relat_1(C_78, B_80))=k9_relat_1(C_78, k2_xboole_0(A_79, B_80)) | ~v1_relat_1(C_78))), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.93/6.35  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.93/6.35  tff(c_8391, plain, (![C_267, A_268, C_269, B_270]: (r1_tarski(k9_relat_1(C_267, A_268), C_269) | ~r1_tarski(k9_relat_1(C_267, k2_xboole_0(A_268, B_270)), C_269) | ~v1_relat_1(C_267))), inference(superposition, [status(thm), theory('equality')], [c_466, c_8])).
% 12.93/6.35  tff(c_14895, plain, (![C_393, A_394, B_395, C_396]: (r1_tarski(k9_relat_1(C_393, k3_xboole_0(A_394, B_395)), C_396) | ~r1_tarski(k9_relat_1(C_393, A_394), C_396) | ~v1_relat_1(C_393))), inference(superposition, [status(thm), theory('equality')], [c_87, c_8391])).
% 12.93/6.35  tff(c_41673, plain, (![C_709, A_710, B_711, C_712]: (r1_tarski(k9_relat_1(C_709, k3_xboole_0(A_710, B_711)), C_712) | ~r1_tarski(k9_relat_1(C_709, B_711), C_712) | ~v1_relat_1(C_709))), inference(superposition, [status(thm), theory('equality')], [c_122, c_14895])).
% 12.93/6.35  tff(c_1088, plain, (![C_104, A_105, C_106, B_107]: (r1_tarski(k9_relat_1(C_104, A_105), C_106) | ~r1_tarski(k9_relat_1(C_104, k2_xboole_0(A_105, B_107)), C_106) | ~v1_relat_1(C_104))), inference(superposition, [status(thm), theory('equality')], [c_466, c_8])).
% 12.93/6.35  tff(c_7003, plain, (![C_229, A_230, B_231, C_232]: (r1_tarski(k9_relat_1(C_229, k3_xboole_0(A_230, B_231)), C_232) | ~r1_tarski(k9_relat_1(C_229, A_230), C_232) | ~v1_relat_1(C_229))), inference(superposition, [status(thm), theory('equality')], [c_87, c_1088])).
% 12.93/6.35  tff(c_392, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 12.93/6.35  tff(c_26, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 12.93/6.35  tff(c_413, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_392, c_26])).
% 12.93/6.35  tff(c_528, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_413])).
% 12.93/6.35  tff(c_7021, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7003, c_528])).
% 12.93/6.35  tff(c_7089, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_7021])).
% 12.93/6.35  tff(c_7090, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_413])).
% 12.93/6.35  tff(c_41738, plain, (~r1_tarski(k9_relat_1('#skF_3', '#skF_2'), k9_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_41673, c_7090])).
% 12.93/6.35  tff(c_41873, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_6, c_41738])).
% 12.93/6.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.93/6.35  
% 12.93/6.35  Inference rules
% 12.93/6.35  ----------------------
% 12.93/6.35  #Ref     : 0
% 12.93/6.35  #Sup     : 10950
% 12.93/6.35  #Fact    : 0
% 12.93/6.35  #Define  : 0
% 12.93/6.35  #Split   : 2
% 12.93/6.35  #Chain   : 0
% 12.93/6.35  #Close   : 0
% 12.93/6.35  
% 12.93/6.35  Ordering : KBO
% 12.93/6.35  
% 12.93/6.35  Simplification rules
% 12.93/6.35  ----------------------
% 12.93/6.35  #Subsume      : 1729
% 12.93/6.35  #Demod        : 6997
% 12.93/6.35  #Tautology    : 4519
% 12.93/6.35  #SimpNegUnit  : 4
% 12.93/6.35  #BackRed      : 0
% 12.93/6.35  
% 12.93/6.35  #Partial instantiations: 0
% 12.93/6.35  #Strategies tried      : 1
% 12.93/6.35  
% 12.93/6.35  Timing (in seconds)
% 12.93/6.35  ----------------------
% 12.93/6.35  Preprocessing        : 0.31
% 12.93/6.35  Parsing              : 0.17
% 12.93/6.35  CNF conversion       : 0.02
% 12.93/6.35  Main loop            : 5.21
% 12.93/6.35  Inferencing          : 0.86
% 12.93/6.35  Reduction            : 2.69
% 12.93/6.35  Demodulation         : 2.41
% 12.93/6.35  BG Simplification    : 0.12
% 12.93/6.35  Subsumption          : 1.29
% 12.93/6.35  Abstraction          : 0.18
% 12.93/6.35  MUC search           : 0.00
% 12.93/6.35  Cooper               : 0.00
% 12.93/6.35  Total                : 5.55
% 12.93/6.35  Index Insertion      : 0.00
% 12.93/6.35  Index Deletion       : 0.00
% 12.93/6.35  Index Matching       : 0.00
% 12.93/6.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
