%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:17:25 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   54 (  57 expanded)
%              Number of leaves         :   30 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   52 (  61 expanded)
%              Number of equality atoms :   24 (  27 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_tarski(k10_relat_1(A,C),B)
           => k10_relat_1(A,C) = k10_relat_1(k7_relat_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_funct_2)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(k7_relat_1(C,A),B) = k3_xboole_0(A,k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t139_funct_1)).

tff(c_28,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') != k10_relat_1('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_97,plain,(
    ! [A_40,B_41] : k1_setfam_1(k2_tarski(A_40,B_41)) = k3_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    ! [B_42,A_43] : k1_setfam_1(k2_tarski(B_42,A_43)) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_97])).

tff(c_24,plain,(
    ! [A_24,B_25] : k1_setfam_1(k2_tarski(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_118,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_112,c_24])).

tff(c_6,plain,(
    ! [A_6] : k4_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    r1_tarski(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_343,plain,(
    ! [A_62,C_63,B_64] :
      ( r1_tarski(A_62,C_63)
      | ~ r1_tarski(B_64,C_63)
      | ~ r1_tarski(A_62,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_506,plain,(
    ! [A_77] :
      ( r1_tarski(A_77,'#skF_2')
      | ~ r1_tarski(A_77,k10_relat_1('#skF_1','#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_30,c_343])).

tff(c_533,plain,(
    ! [B_5] : r1_tarski(k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),B_5),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4,c_506])).

tff(c_168,plain,(
    ! [A_46,C_47,B_48] :
      ( r1_xboole_0(A_46,k4_xboole_0(C_47,B_48))
      | ~ r1_tarski(A_46,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_12,plain,(
    ! [A_9] :
      ( ~ r1_xboole_0(A_9,A_9)
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_728,plain,(
    ! [C_90,B_91] :
      ( k4_xboole_0(C_90,B_91) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(C_90,B_91),B_91) ) ),
    inference(resolution,[status(thm)],[c_168,c_12])).

tff(c_749,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_533,c_728])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_769,plain,(
    k4_xboole_0(k10_relat_1('#skF_1','#skF_3'),k1_xboole_0) = k3_xboole_0(k10_relat_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_749,c_8])).

tff(c_781,plain,(
    k3_xboole_0('#skF_2',k10_relat_1('#skF_1','#skF_3')) = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_118,c_6,c_769])).

tff(c_26,plain,(
    ! [A_26,C_28,B_27] :
      ( k3_xboole_0(A_26,k10_relat_1(C_28,B_27)) = k10_relat_1(k7_relat_1(C_28,A_26),B_27)
      | ~ v1_relat_1(C_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2256,plain,
    ( k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_781,c_26])).

tff(c_2278,plain,(
    k10_relat_1(k7_relat_1('#skF_1','#skF_2'),'#skF_3') = k10_relat_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_2256])).

tff(c_2280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_2278])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:47:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.57  
% 3.46/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.57  %$ r1_xboole_0 > r1_tarski > v1_relat_1 > v1_funct_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.46/1.57  
% 3.46/1.57  %Foreground sorts:
% 3.46/1.57  
% 3.46/1.57  
% 3.46/1.57  %Background operators:
% 3.46/1.57  
% 3.46/1.57  
% 3.46/1.57  %Foreground operators:
% 3.46/1.57  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.57  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.46/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.46/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.46/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.46/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.46/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.57  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.46/1.57  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.57  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.46/1.57  
% 3.46/1.58  tff(f_77, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_tarski(k10_relat_1(A, C), B) => (k10_relat_1(A, C) = k10_relat_1(k7_relat_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_funct_2)).
% 3.46/1.58  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.46/1.58  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 3.46/1.58  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.46/1.58  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.46/1.58  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.46/1.58  tff(f_53, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 3.46/1.58  tff(f_49, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.46/1.58  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.46/1.58  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(k7_relat_1(C, A), B) = k3_xboole_0(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t139_funct_1)).
% 3.46/1.58  tff(c_28, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')!=k10_relat_1('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.46/1.58  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.46/1.58  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.58  tff(c_97, plain, (![A_40, B_41]: (k1_setfam_1(k2_tarski(A_40, B_41))=k3_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.58  tff(c_112, plain, (![B_42, A_43]: (k1_setfam_1(k2_tarski(B_42, A_43))=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_16, c_97])).
% 3.46/1.58  tff(c_24, plain, (![A_24, B_25]: (k1_setfam_1(k2_tarski(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.46/1.58  tff(c_118, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(superposition, [status(thm), theory('equality')], [c_112, c_24])).
% 3.46/1.58  tff(c_6, plain, (![A_6]: (k4_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.46/1.58  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.46/1.58  tff(c_30, plain, (r1_tarski(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.46/1.58  tff(c_343, plain, (![A_62, C_63, B_64]: (r1_tarski(A_62, C_63) | ~r1_tarski(B_64, C_63) | ~r1_tarski(A_62, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.58  tff(c_506, plain, (![A_77]: (r1_tarski(A_77, '#skF_2') | ~r1_tarski(A_77, k10_relat_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_30, c_343])).
% 3.46/1.58  tff(c_533, plain, (![B_5]: (r1_tarski(k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), B_5), '#skF_2'))), inference(resolution, [status(thm)], [c_4, c_506])).
% 3.46/1.58  tff(c_168, plain, (![A_46, C_47, B_48]: (r1_xboole_0(A_46, k4_xboole_0(C_47, B_48)) | ~r1_tarski(A_46, B_48))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.46/1.58  tff(c_12, plain, (![A_9]: (~r1_xboole_0(A_9, A_9) | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.58  tff(c_728, plain, (![C_90, B_91]: (k4_xboole_0(C_90, B_91)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(C_90, B_91), B_91))), inference(resolution, [status(thm)], [c_168, c_12])).
% 3.46/1.58  tff(c_749, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_533, c_728])).
% 3.46/1.58  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.58  tff(c_769, plain, (k4_xboole_0(k10_relat_1('#skF_1', '#skF_3'), k1_xboole_0)=k3_xboole_0(k10_relat_1('#skF_1', '#skF_3'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_749, c_8])).
% 3.46/1.58  tff(c_781, plain, (k3_xboole_0('#skF_2', k10_relat_1('#skF_1', '#skF_3'))=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_118, c_6, c_769])).
% 3.46/1.58  tff(c_26, plain, (![A_26, C_28, B_27]: (k3_xboole_0(A_26, k10_relat_1(C_28, B_27))=k10_relat_1(k7_relat_1(C_28, A_26), B_27) | ~v1_relat_1(C_28))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.46/1.58  tff(c_2256, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_781, c_26])).
% 3.46/1.58  tff(c_2278, plain, (k10_relat_1(k7_relat_1('#skF_1', '#skF_2'), '#skF_3')=k10_relat_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_2256])).
% 3.46/1.58  tff(c_2280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_2278])).
% 3.46/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.58  
% 3.46/1.58  Inference rules
% 3.46/1.58  ----------------------
% 3.46/1.58  #Ref     : 0
% 3.46/1.58  #Sup     : 526
% 3.46/1.58  #Fact    : 0
% 3.46/1.58  #Define  : 0
% 3.46/1.58  #Split   : 0
% 3.46/1.58  #Chain   : 0
% 3.46/1.58  #Close   : 0
% 3.46/1.58  
% 3.46/1.58  Ordering : KBO
% 3.46/1.58  
% 3.46/1.58  Simplification rules
% 3.46/1.58  ----------------------
% 3.46/1.58  #Subsume      : 20
% 3.46/1.58  #Demod        : 370
% 3.46/1.58  #Tautology    : 348
% 3.46/1.58  #SimpNegUnit  : 1
% 3.46/1.58  #BackRed      : 0
% 3.46/1.58  
% 3.46/1.58  #Partial instantiations: 0
% 3.46/1.58  #Strategies tried      : 1
% 3.46/1.58  
% 3.46/1.58  Timing (in seconds)
% 3.46/1.58  ----------------------
% 3.46/1.58  Preprocessing        : 0.31
% 3.46/1.58  Parsing              : 0.17
% 3.46/1.58  CNF conversion       : 0.02
% 3.46/1.58  Main loop            : 0.49
% 3.46/1.58  Inferencing          : 0.16
% 3.46/1.58  Reduction            : 0.20
% 3.46/1.58  Demodulation         : 0.16
% 3.46/1.58  BG Simplification    : 0.02
% 3.46/1.58  Subsumption          : 0.07
% 3.46/1.58  Abstraction          : 0.02
% 3.46/1.58  MUC search           : 0.00
% 3.46/1.58  Cooper               : 0.00
% 3.46/1.58  Total                : 0.82
% 3.46/1.58  Index Insertion      : 0.00
% 3.46/1.58  Index Deletion       : 0.00
% 3.46/1.58  Index Matching       : 0.00
% 3.46/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
