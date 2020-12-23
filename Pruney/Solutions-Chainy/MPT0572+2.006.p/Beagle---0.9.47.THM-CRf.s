%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:49 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   56 (  75 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  88 expanded)
%              Number of equality atoms :   18 (  25 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_12,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_60,plain,(
    ! [A_30,B_31] : k1_setfam_1(k2_tarski(A_30,B_31)) = k3_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_84,plain,(
    ! [A_34,B_35] : k1_setfam_1(k2_tarski(A_34,B_35)) = k3_xboole_0(B_35,A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_60])).

tff(c_18,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_90,plain,(
    ! [B_35,A_34] : k3_xboole_0(B_35,A_34) = k3_xboole_0(A_34,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_18])).

tff(c_141,plain,(
    ! [A_38,B_39] : k4_xboole_0(A_38,k4_xboole_0(A_38,B_39)) = k3_xboole_0(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4,plain,(
    ! [A_4,B_5] : r1_tarski(k4_xboole_0(A_4,B_5),A_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [A_40,B_41] : r1_tarski(k3_xboole_0(A_40,B_41),A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_4])).

tff(c_162,plain,(
    ! [B_35,A_34] : r1_tarski(k3_xboole_0(B_35,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_159])).

tff(c_24,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = B_7
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_332,plain,(
    ! [C_60,A_61,B_62] :
      ( k2_xboole_0(k10_relat_1(C_60,A_61),k10_relat_1(C_60,B_62)) = k10_relat_1(C_60,k2_xboole_0(A_61,B_62))
      | ~ v1_relat_1(C_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_10,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_486,plain,(
    ! [C_76,A_77,B_78] :
      ( r1_tarski(k10_relat_1(C_76,A_77),k10_relat_1(C_76,k2_xboole_0(A_77,B_78)))
      | ~ v1_relat_1(C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_10])).

tff(c_525,plain,(
    ! [C_85,A_86,B_87] :
      ( r1_tarski(k10_relat_1(C_85,A_86),k10_relat_1(C_85,B_87))
      | ~ v1_relat_1(C_85)
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_486])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_185,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,k4_xboole_0(B_48,A_47)) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_197,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(k4_xboole_0(A_8,B_9),k3_xboole_0(A_8,B_9)) = A_8
      | ~ r1_tarski(k4_xboole_0(A_8,B_9),A_8) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_185])).

tff(c_202,plain,(
    ! [A_49,B_50] : k2_xboole_0(k4_xboole_0(A_49,B_50),k3_xboole_0(A_49,B_50)) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_197])).

tff(c_214,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),k3_xboole_0(A_8,k4_xboole_0(A_8,B_9))) = A_8 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_202])).

tff(c_441,plain,(
    ! [C_67,A_68,B_69] :
      ( r1_tarski(k10_relat_1(C_67,A_68),k10_relat_1(C_67,k2_xboole_0(A_68,B_69)))
      | ~ v1_relat_1(C_67) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_332,c_10])).

tff(c_470,plain,(
    ! [C_73,A_74,B_75] :
      ( r1_tarski(k10_relat_1(C_73,k3_xboole_0(A_74,B_75)),k10_relat_1(C_73,A_74))
      | ~ v1_relat_1(C_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_441])).

tff(c_259,plain,(
    ! [A_53,B_54,C_55] :
      ( r1_tarski(A_53,k3_xboole_0(B_54,C_55))
      | ~ r1_tarski(A_53,C_55)
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_22,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_269,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_259,c_22])).

tff(c_437,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_269])).

tff(c_473,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_470,c_437])).

tff(c_483,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_473])).

tff(c_484,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_269])).

tff(c_528,plain,
    ( ~ v1_relat_1('#skF_3')
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_525,c_484])).

tff(c_532,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_162,c_24,c_528])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.28  
% 2.12/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.29  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 2.12/1.29  
% 2.12/1.29  %Foreground sorts:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Background operators:
% 2.12/1.29  
% 2.12/1.29  
% 2.12/1.29  %Foreground operators:
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.12/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.29  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.12/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.29  
% 2.12/1.30  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.12/1.30  tff(f_49, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.12/1.30  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.12/1.30  tff(f_33, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.12/1.30  tff(f_58, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 2.12/1.30  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.12/1.30  tff(f_53, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 2.12/1.30  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.12/1.30  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.12/1.30  tff(c_12, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.30  tff(c_60, plain, (![A_30, B_31]: (k1_setfam_1(k2_tarski(A_30, B_31))=k3_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.30  tff(c_84, plain, (![A_34, B_35]: (k1_setfam_1(k2_tarski(A_34, B_35))=k3_xboole_0(B_35, A_34))), inference(superposition, [status(thm), theory('equality')], [c_12, c_60])).
% 2.12/1.30  tff(c_18, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.12/1.30  tff(c_90, plain, (![B_35, A_34]: (k3_xboole_0(B_35, A_34)=k3_xboole_0(A_34, B_35))), inference(superposition, [status(thm), theory('equality')], [c_84, c_18])).
% 2.12/1.30  tff(c_141, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k4_xboole_0(A_38, B_39))=k3_xboole_0(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.30  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(k4_xboole_0(A_4, B_5), A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.12/1.30  tff(c_159, plain, (![A_40, B_41]: (r1_tarski(k3_xboole_0(A_40, B_41), A_40))), inference(superposition, [status(thm), theory('equality')], [c_141, c_4])).
% 2.12/1.30  tff(c_162, plain, (![B_35, A_34]: (r1_tarski(k3_xboole_0(B_35, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_90, c_159])).
% 2.12/1.30  tff(c_24, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.30  tff(c_6, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=B_7 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.30  tff(c_332, plain, (![C_60, A_61, B_62]: (k2_xboole_0(k10_relat_1(C_60, A_61), k10_relat_1(C_60, B_62))=k10_relat_1(C_60, k2_xboole_0(A_61, B_62)) | ~v1_relat_1(C_60))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.12/1.30  tff(c_10, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.12/1.30  tff(c_486, plain, (![C_76, A_77, B_78]: (r1_tarski(k10_relat_1(C_76, A_77), k10_relat_1(C_76, k2_xboole_0(A_77, B_78))) | ~v1_relat_1(C_76))), inference(superposition, [status(thm), theory('equality')], [c_332, c_10])).
% 2.12/1.30  tff(c_525, plain, (![C_85, A_86, B_87]: (r1_tarski(k10_relat_1(C_85, A_86), k10_relat_1(C_85, B_87)) | ~v1_relat_1(C_85) | ~r1_tarski(A_86, B_87))), inference(superposition, [status(thm), theory('equality')], [c_6, c_486])).
% 2.12/1.30  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.30  tff(c_185, plain, (![A_47, B_48]: (k2_xboole_0(A_47, k4_xboole_0(B_48, A_47))=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.12/1.30  tff(c_197, plain, (![A_8, B_9]: (k2_xboole_0(k4_xboole_0(A_8, B_9), k3_xboole_0(A_8, B_9))=A_8 | ~r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(superposition, [status(thm), theory('equality')], [c_8, c_185])).
% 2.12/1.30  tff(c_202, plain, (![A_49, B_50]: (k2_xboole_0(k4_xboole_0(A_49, B_50), k3_xboole_0(A_49, B_50))=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_197])).
% 2.12/1.30  tff(c_214, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), k3_xboole_0(A_8, k4_xboole_0(A_8, B_9)))=A_8)), inference(superposition, [status(thm), theory('equality')], [c_8, c_202])).
% 2.12/1.30  tff(c_441, plain, (![C_67, A_68, B_69]: (r1_tarski(k10_relat_1(C_67, A_68), k10_relat_1(C_67, k2_xboole_0(A_68, B_69))) | ~v1_relat_1(C_67))), inference(superposition, [status(thm), theory('equality')], [c_332, c_10])).
% 2.12/1.30  tff(c_470, plain, (![C_73, A_74, B_75]: (r1_tarski(k10_relat_1(C_73, k3_xboole_0(A_74, B_75)), k10_relat_1(C_73, A_74)) | ~v1_relat_1(C_73))), inference(superposition, [status(thm), theory('equality')], [c_214, c_441])).
% 2.12/1.30  tff(c_259, plain, (![A_53, B_54, C_55]: (r1_tarski(A_53, k3_xboole_0(B_54, C_55)) | ~r1_tarski(A_53, C_55) | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.30  tff(c_22, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.30  tff(c_269, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_259, c_22])).
% 2.12/1.30  tff(c_437, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_269])).
% 2.12/1.30  tff(c_473, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_470, c_437])).
% 2.12/1.30  tff(c_483, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_473])).
% 2.12/1.30  tff(c_484, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_269])).
% 2.12/1.30  tff(c_528, plain, (~v1_relat_1('#skF_3') | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_525, c_484])).
% 2.12/1.30  tff(c_532, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_162, c_24, c_528])).
% 2.12/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  Inference rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Ref     : 0
% 2.12/1.30  #Sup     : 125
% 2.12/1.30  #Fact    : 0
% 2.12/1.30  #Define  : 0
% 2.12/1.30  #Split   : 1
% 2.12/1.30  #Chain   : 0
% 2.12/1.30  #Close   : 0
% 2.12/1.30  
% 2.12/1.30  Ordering : KBO
% 2.12/1.30  
% 2.12/1.30  Simplification rules
% 2.12/1.30  ----------------------
% 2.12/1.30  #Subsume      : 3
% 2.12/1.30  #Demod        : 40
% 2.12/1.30  #Tautology    : 77
% 2.12/1.30  #SimpNegUnit  : 0
% 2.12/1.30  #BackRed      : 0
% 2.12/1.30  
% 2.12/1.30  #Partial instantiations: 0
% 2.12/1.30  #Strategies tried      : 1
% 2.12/1.30  
% 2.12/1.30  Timing (in seconds)
% 2.12/1.30  ----------------------
% 2.42/1.30  Preprocessing        : 0.29
% 2.42/1.30  Parsing              : 0.15
% 2.42/1.30  CNF conversion       : 0.02
% 2.42/1.30  Main loop            : 0.25
% 2.42/1.30  Inferencing          : 0.10
% 2.42/1.30  Reduction            : 0.09
% 2.42/1.30  Demodulation         : 0.07
% 2.42/1.30  BG Simplification    : 0.01
% 2.42/1.30  Subsumption          : 0.04
% 2.42/1.30  Abstraction          : 0.02
% 2.42/1.30  MUC search           : 0.00
% 2.42/1.30  Cooper               : 0.00
% 2.42/1.30  Total                : 0.57
% 2.42/1.30  Index Insertion      : 0.00
% 2.42/1.30  Index Deletion       : 0.00
% 2.42/1.31  Index Matching       : 0.00
% 2.42/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
