%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:48 EST 2020

% Result     : Theorem 13.32s
% Output     : CNFRefutation 13.32s
% Verified   : 
% Statistics : Number of formulae       :   55 (  74 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   63 (  97 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k10_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t176_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_63,axiom,(
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

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

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

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_73,plain,(
    ! [A_52,B_53] : k1_setfam_1(k2_tarski(A_52,B_53)) = k3_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_124,plain,(
    ! [B_61,A_62] : k1_setfam_1(k2_tarski(B_61,A_62)) = k3_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_73])).

tff(c_30,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_130,plain,(
    ! [B_61,A_62] : k3_xboole_0(B_61,A_62) = k3_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_97,plain,(
    ! [A_56,B_57] :
      ( k2_xboole_0(A_56,B_57) = B_57
      | ~ r1_tarski(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_104,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_97])).

tff(c_8125,plain,(
    ! [C_313,A_314,B_315] :
      ( k2_xboole_0(k10_relat_1(C_313,A_314),k10_relat_1(C_313,B_315)) = k10_relat_1(C_313,k2_xboole_0(A_314,B_315))
      | ~ v1_relat_1(C_313) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10561,plain,(
    ! [C_360,A_361,C_362,B_363] :
      ( r1_tarski(k10_relat_1(C_360,A_361),C_362)
      | ~ r1_tarski(k10_relat_1(C_360,k2_xboole_0(A_361,B_363)),C_362)
      | ~ v1_relat_1(C_360) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8125,c_8])).

tff(c_15653,plain,(
    ! [C_470,A_471,B_472,C_473] :
      ( r1_tarski(k10_relat_1(C_470,k3_xboole_0(A_471,B_472)),C_473)
      | ~ r1_tarski(k10_relat_1(C_470,A_471),C_473)
      | ~ v1_relat_1(C_470) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_10561])).

tff(c_40728,plain,(
    ! [C_770,B_771,A_772,C_773] :
      ( r1_tarski(k10_relat_1(C_770,k3_xboole_0(B_771,A_772)),C_773)
      | ~ r1_tarski(k10_relat_1(C_770,A_772),C_773)
      | ~ v1_relat_1(C_770) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_130,c_15653])).

tff(c_800,plain,(
    ! [C_129,A_130,B_131] :
      ( k2_xboole_0(k10_relat_1(C_129,A_130),k10_relat_1(C_129,B_131)) = k10_relat_1(C_129,k2_xboole_0(A_130,B_131))
      | ~ v1_relat_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2373,plain,(
    ! [C_173,A_174,C_175,B_176] :
      ( r1_tarski(k10_relat_1(C_173,A_174),C_175)
      | ~ r1_tarski(k10_relat_1(C_173,k2_xboole_0(A_174,B_176)),C_175)
      | ~ v1_relat_1(C_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_8])).

tff(c_7650,plain,(
    ! [C_284,A_285,B_286,C_287] :
      ( r1_tarski(k10_relat_1(C_284,k3_xboole_0(A_285,B_286)),C_287)
      | ~ r1_tarski(k10_relat_1(C_284,A_285),C_287)
      | ~ v1_relat_1(C_284) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_2373])).

tff(c_400,plain,(
    ! [A_91,B_92,C_93] :
      ( r1_tarski(A_91,k3_xboole_0(B_92,C_93))
      | ~ r1_tarski(A_91,C_93)
      | ~ r1_tarski(A_91,B_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_34,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_421,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_400,c_34])).

tff(c_511,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_7675,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7650,c_511])).

tff(c_7738,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_7675])).

tff(c_7739,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_40798,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_2'),k10_relat_1('#skF_3','#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40728,c_7739])).

tff(c_40935,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_40798])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:04:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.32/6.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/6.24  
% 13.32/6.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/6.24  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 13.32/6.24  
% 13.32/6.24  %Foreground sorts:
% 13.32/6.24  
% 13.32/6.24  
% 13.32/6.24  %Background operators:
% 13.32/6.24  
% 13.32/6.24  
% 13.32/6.24  %Foreground operators:
% 13.32/6.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.32/6.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.32/6.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.32/6.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.32/6.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.32/6.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.32/6.24  tff('#skF_2', type, '#skF_2': $i).
% 13.32/6.24  tff('#skF_3', type, '#skF_3': $i).
% 13.32/6.24  tff('#skF_1', type, '#skF_1': $i).
% 13.32/6.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.32/6.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.32/6.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.32/6.24  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 13.32/6.24  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.32/6.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.32/6.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.32/6.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.32/6.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.32/6.24  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.32/6.24  
% 13.32/6.25  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 13.32/6.25  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.32/6.25  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.32/6.25  tff(f_63, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 13.32/6.25  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.32/6.25  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.32/6.25  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 13.32/6.25  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 13.32/6.25  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 13.32/6.25  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.32/6.25  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 13.32/6.25  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.32/6.25  tff(c_73, plain, (![A_52, B_53]: (k1_setfam_1(k2_tarski(A_52, B_53))=k3_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.32/6.25  tff(c_124, plain, (![B_61, A_62]: (k1_setfam_1(k2_tarski(B_61, A_62))=k3_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_16, c_73])).
% 13.32/6.25  tff(c_30, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_63])).
% 13.32/6.25  tff(c_130, plain, (![B_61, A_62]: (k3_xboole_0(B_61, A_62)=k3_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_124, c_30])).
% 13.32/6.25  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.32/6.25  tff(c_97, plain, (![A_56, B_57]: (k2_xboole_0(A_56, B_57)=B_57 | ~r1_tarski(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.32/6.25  tff(c_104, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_97])).
% 13.32/6.25  tff(c_8125, plain, (![C_313, A_314, B_315]: (k2_xboole_0(k10_relat_1(C_313, A_314), k10_relat_1(C_313, B_315))=k10_relat_1(C_313, k2_xboole_0(A_314, B_315)) | ~v1_relat_1(C_313))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.32/6.25  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.32/6.25  tff(c_10561, plain, (![C_360, A_361, C_362, B_363]: (r1_tarski(k10_relat_1(C_360, A_361), C_362) | ~r1_tarski(k10_relat_1(C_360, k2_xboole_0(A_361, B_363)), C_362) | ~v1_relat_1(C_360))), inference(superposition, [status(thm), theory('equality')], [c_8125, c_8])).
% 13.32/6.25  tff(c_15653, plain, (![C_470, A_471, B_472, C_473]: (r1_tarski(k10_relat_1(C_470, k3_xboole_0(A_471, B_472)), C_473) | ~r1_tarski(k10_relat_1(C_470, A_471), C_473) | ~v1_relat_1(C_470))), inference(superposition, [status(thm), theory('equality')], [c_104, c_10561])).
% 13.32/6.25  tff(c_40728, plain, (![C_770, B_771, A_772, C_773]: (r1_tarski(k10_relat_1(C_770, k3_xboole_0(B_771, A_772)), C_773) | ~r1_tarski(k10_relat_1(C_770, A_772), C_773) | ~v1_relat_1(C_770))), inference(superposition, [status(thm), theory('equality')], [c_130, c_15653])).
% 13.32/6.25  tff(c_800, plain, (![C_129, A_130, B_131]: (k2_xboole_0(k10_relat_1(C_129, A_130), k10_relat_1(C_129, B_131))=k10_relat_1(C_129, k2_xboole_0(A_130, B_131)) | ~v1_relat_1(C_129))), inference(cnfTransformation, [status(thm)], [f_67])).
% 13.32/6.25  tff(c_2373, plain, (![C_173, A_174, C_175, B_176]: (r1_tarski(k10_relat_1(C_173, A_174), C_175) | ~r1_tarski(k10_relat_1(C_173, k2_xboole_0(A_174, B_176)), C_175) | ~v1_relat_1(C_173))), inference(superposition, [status(thm), theory('equality')], [c_800, c_8])).
% 13.32/6.25  tff(c_7650, plain, (![C_284, A_285, B_286, C_287]: (r1_tarski(k10_relat_1(C_284, k3_xboole_0(A_285, B_286)), C_287) | ~r1_tarski(k10_relat_1(C_284, A_285), C_287) | ~v1_relat_1(C_284))), inference(superposition, [status(thm), theory('equality')], [c_104, c_2373])).
% 13.32/6.25  tff(c_400, plain, (![A_91, B_92, C_93]: (r1_tarski(A_91, k3_xboole_0(B_92, C_93)) | ~r1_tarski(A_91, C_93) | ~r1_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.32/6.25  tff(c_34, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 13.32/6.25  tff(c_421, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_400, c_34])).
% 13.32/6.25  tff(c_511, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_421])).
% 13.32/6.25  tff(c_7675, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7650, c_511])).
% 13.32/6.25  tff(c_7738, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_7675])).
% 13.32/6.25  tff(c_7739, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_421])).
% 13.32/6.25  tff(c_40798, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_2'), k10_relat_1('#skF_3', '#skF_2')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40728, c_7739])).
% 13.32/6.25  tff(c_40935, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_40798])).
% 13.32/6.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.32/6.25  
% 13.32/6.25  Inference rules
% 13.32/6.25  ----------------------
% 13.32/6.25  #Ref     : 0
% 13.32/6.25  #Sup     : 10657
% 13.32/6.25  #Fact    : 0
% 13.32/6.25  #Define  : 0
% 13.32/6.25  #Split   : 2
% 13.32/6.25  #Chain   : 0
% 13.32/6.25  #Close   : 0
% 13.32/6.25  
% 13.32/6.25  Ordering : KBO
% 13.32/6.25  
% 13.32/6.25  Simplification rules
% 13.32/6.25  ----------------------
% 13.32/6.25  #Subsume      : 1627
% 13.32/6.25  #Demod        : 6764
% 13.32/6.25  #Tautology    : 4494
% 13.32/6.25  #SimpNegUnit  : 4
% 13.32/6.25  #BackRed      : 0
% 13.32/6.25  
% 13.32/6.25  #Partial instantiations: 0
% 13.32/6.25  #Strategies tried      : 1
% 13.32/6.25  
% 13.32/6.25  Timing (in seconds)
% 13.32/6.25  ----------------------
% 13.32/6.26  Preprocessing        : 0.34
% 13.32/6.26  Parsing              : 0.18
% 13.32/6.26  CNF conversion       : 0.02
% 13.32/6.26  Main loop            : 5.08
% 13.32/6.26  Inferencing          : 0.84
% 13.32/6.26  Reduction            : 2.58
% 13.32/6.26  Demodulation         : 2.31
% 13.32/6.26  BG Simplification    : 0.12
% 13.32/6.26  Subsumption          : 1.28
% 13.32/6.26  Abstraction          : 0.19
% 13.32/6.26  MUC search           : 0.00
% 13.32/6.26  Cooper               : 0.00
% 13.32/6.26  Total                : 5.44
% 13.32/6.26  Index Insertion      : 0.00
% 13.32/6.26  Index Deletion       : 0.00
% 13.32/6.26  Index Matching       : 0.00
% 13.32/6.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------
