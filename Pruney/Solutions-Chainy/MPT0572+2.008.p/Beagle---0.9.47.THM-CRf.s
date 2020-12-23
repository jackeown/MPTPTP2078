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

% Result     : Theorem 10.93s
% Output     : CNFRefutation 10.96s
% Verified   : 
% Statistics : Number of formulae       :   52 (  69 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   57 (  89 expanded)
%              Number of equality atoms :   10 (  14 expanded)
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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_36,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [B_50,A_51] : k3_xboole_0(B_50,A_51) = k3_xboole_0(A_51,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [B_50,A_51] : r1_tarski(k3_xboole_0(B_50,A_51),A_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_14])).

tff(c_107,plain,(
    ! [A_58,B_59] :
      ( k2_xboole_0(A_58,B_59) = B_59
      | ~ r1_tarski(A_58,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [B_50,A_51] : k2_xboole_0(k3_xboole_0(B_50,A_51),A_51) = A_51 ),
    inference(resolution,[status(thm)],[c_55,c_107])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8264,plain,(
    ! [C_312,A_313,B_314] :
      ( k2_xboole_0(k10_relat_1(C_312,A_313),k10_relat_1(C_312,B_314)) = k10_relat_1(C_312,k2_xboole_0(A_313,B_314))
      | ~ v1_relat_1(C_312) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10698,plain,(
    ! [C_359,A_360,C_361,B_362] :
      ( r1_tarski(k10_relat_1(C_359,A_360),C_361)
      | ~ r1_tarski(k10_relat_1(C_359,k2_xboole_0(A_360,B_362)),C_361)
      | ~ v1_relat_1(C_359) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8264,c_10])).

tff(c_12236,plain,(
    ! [C_393,A_394,B_395] :
      ( r1_tarski(k10_relat_1(C_393,A_394),k10_relat_1(C_393,k2_xboole_0(A_394,B_395)))
      | ~ v1_relat_1(C_393) ) ),
    inference(resolution,[status(thm)],[c_8,c_10698])).

tff(c_26427,plain,(
    ! [C_628,B_629,A_630] :
      ( r1_tarski(k10_relat_1(C_628,k3_xboole_0(B_629,A_630)),k10_relat_1(C_628,A_630))
      | ~ v1_relat_1(C_628) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_12236])).

tff(c_118,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_14,c_107])).

tff(c_827,plain,(
    ! [C_128,A_129,B_130] :
      ( k2_xboole_0(k10_relat_1(C_128,A_129),k10_relat_1(C_128,B_130)) = k10_relat_1(C_128,k2_xboole_0(A_129,B_130))
      | ~ v1_relat_1(C_128) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2875,plain,(
    ! [C_173,A_174,C_175,B_176] :
      ( r1_tarski(k10_relat_1(C_173,A_174),C_175)
      | ~ r1_tarski(k10_relat_1(C_173,k2_xboole_0(A_174,B_176)),C_175)
      | ~ v1_relat_1(C_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_10])).

tff(c_7841,plain,(
    ! [C_285,A_286,B_287,C_288] :
      ( r1_tarski(k10_relat_1(C_285,k3_xboole_0(A_286,B_287)),C_288)
      | ~ r1_tarski(k10_relat_1(C_285,A_286),C_288)
      | ~ v1_relat_1(C_285) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_2875])).

tff(c_426,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski(A_100,k3_xboole_0(B_101,C_102))
      | ~ r1_tarski(A_100,C_102)
      | ~ r1_tarski(A_100,B_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_447,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_426,c_34])).

tff(c_504,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_7866,plain,
    ( ~ r1_tarski(k10_relat_1('#skF_3','#skF_1'),k10_relat_1('#skF_3','#skF_1'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_7841,c_504])).

tff(c_7929,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_8,c_7866])).

tff(c_7930,plain,(
    ~ r1_tarski(k10_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k10_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_26442,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_26427,c_7930])).

tff(c_26530,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_26442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:01:55 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.93/4.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.96/4.27  
% 10.96/4.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.96/4.27  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 10.96/4.27  
% 10.96/4.27  %Foreground sorts:
% 10.96/4.27  
% 10.96/4.27  
% 10.96/4.27  %Background operators:
% 10.96/4.27  
% 10.96/4.27  
% 10.96/4.27  %Foreground operators:
% 10.96/4.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.96/4.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.96/4.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.96/4.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.96/4.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.96/4.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.96/4.27  tff('#skF_2', type, '#skF_2': $i).
% 10.96/4.27  tff('#skF_3', type, '#skF_3': $i).
% 10.96/4.27  tff('#skF_1', type, '#skF_1': $i).
% 10.96/4.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.96/4.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 10.96/4.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.96/4.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 10.96/4.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.96/4.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.96/4.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.96/4.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.96/4.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 10.96/4.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 10.96/4.27  
% 10.96/4.28  tff(f_72, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k10_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t176_relat_1)).
% 10.96/4.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.96/4.28  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 10.96/4.28  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 10.96/4.28  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 10.96/4.28  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t175_relat_1)).
% 10.96/4.28  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_xboole_1)).
% 10.96/4.28  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 10.96/4.28  tff(c_36, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.96/4.28  tff(c_40, plain, (![B_50, A_51]: (k3_xboole_0(B_50, A_51)=k3_xboole_0(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.96/4.28  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.96/4.28  tff(c_55, plain, (![B_50, A_51]: (r1_tarski(k3_xboole_0(B_50, A_51), A_51))), inference(superposition, [status(thm), theory('equality')], [c_40, c_14])).
% 10.96/4.28  tff(c_107, plain, (![A_58, B_59]: (k2_xboole_0(A_58, B_59)=B_59 | ~r1_tarski(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.96/4.28  tff(c_117, plain, (![B_50, A_51]: (k2_xboole_0(k3_xboole_0(B_50, A_51), A_51)=A_51)), inference(resolution, [status(thm)], [c_55, c_107])).
% 10.96/4.28  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 10.96/4.28  tff(c_8264, plain, (![C_312, A_313, B_314]: (k2_xboole_0(k10_relat_1(C_312, A_313), k10_relat_1(C_312, B_314))=k10_relat_1(C_312, k2_xboole_0(A_313, B_314)) | ~v1_relat_1(C_312))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.96/4.28  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.96/4.28  tff(c_10698, plain, (![C_359, A_360, C_361, B_362]: (r1_tarski(k10_relat_1(C_359, A_360), C_361) | ~r1_tarski(k10_relat_1(C_359, k2_xboole_0(A_360, B_362)), C_361) | ~v1_relat_1(C_359))), inference(superposition, [status(thm), theory('equality')], [c_8264, c_10])).
% 10.96/4.28  tff(c_12236, plain, (![C_393, A_394, B_395]: (r1_tarski(k10_relat_1(C_393, A_394), k10_relat_1(C_393, k2_xboole_0(A_394, B_395))) | ~v1_relat_1(C_393))), inference(resolution, [status(thm)], [c_8, c_10698])).
% 10.96/4.28  tff(c_26427, plain, (![C_628, B_629, A_630]: (r1_tarski(k10_relat_1(C_628, k3_xboole_0(B_629, A_630)), k10_relat_1(C_628, A_630)) | ~v1_relat_1(C_628))), inference(superposition, [status(thm), theory('equality')], [c_117, c_12236])).
% 10.96/4.28  tff(c_118, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_14, c_107])).
% 10.96/4.28  tff(c_827, plain, (![C_128, A_129, B_130]: (k2_xboole_0(k10_relat_1(C_128, A_129), k10_relat_1(C_128, B_130))=k10_relat_1(C_128, k2_xboole_0(A_129, B_130)) | ~v1_relat_1(C_128))), inference(cnfTransformation, [status(thm)], [f_67])).
% 10.96/4.28  tff(c_2875, plain, (![C_173, A_174, C_175, B_176]: (r1_tarski(k10_relat_1(C_173, A_174), C_175) | ~r1_tarski(k10_relat_1(C_173, k2_xboole_0(A_174, B_176)), C_175) | ~v1_relat_1(C_173))), inference(superposition, [status(thm), theory('equality')], [c_827, c_10])).
% 10.96/4.28  tff(c_7841, plain, (![C_285, A_286, B_287, C_288]: (r1_tarski(k10_relat_1(C_285, k3_xboole_0(A_286, B_287)), C_288) | ~r1_tarski(k10_relat_1(C_285, A_286), C_288) | ~v1_relat_1(C_285))), inference(superposition, [status(thm), theory('equality')], [c_118, c_2875])).
% 10.96/4.28  tff(c_426, plain, (![A_100, B_101, C_102]: (r1_tarski(A_100, k3_xboole_0(B_101, C_102)) | ~r1_tarski(A_100, C_102) | ~r1_tarski(A_100, B_101))), inference(cnfTransformation, [status(thm)], [f_49])).
% 10.96/4.28  tff(c_34, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.96/4.28  tff(c_447, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_426, c_34])).
% 10.96/4.28  tff(c_504, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_447])).
% 10.96/4.28  tff(c_7866, plain, (~r1_tarski(k10_relat_1('#skF_3', '#skF_1'), k10_relat_1('#skF_3', '#skF_1')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_7841, c_504])).
% 10.96/4.28  tff(c_7929, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_8, c_7866])).
% 10.96/4.28  tff(c_7930, plain, (~r1_tarski(k10_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k10_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_447])).
% 10.96/4.28  tff(c_26442, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_26427, c_7930])).
% 10.96/4.28  tff(c_26530, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_26442])).
% 10.96/4.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.96/4.28  
% 10.96/4.28  Inference rules
% 10.96/4.28  ----------------------
% 10.96/4.28  #Ref     : 0
% 10.96/4.28  #Sup     : 6710
% 10.96/4.28  #Fact    : 0
% 10.96/4.28  #Define  : 0
% 10.96/4.28  #Split   : 2
% 10.96/4.28  #Chain   : 0
% 10.96/4.28  #Close   : 0
% 10.96/4.28  
% 10.96/4.28  Ordering : KBO
% 10.96/4.28  
% 10.96/4.28  Simplification rules
% 10.96/4.28  ----------------------
% 10.96/4.28  #Subsume      : 794
% 10.96/4.28  #Demod        : 4400
% 10.96/4.28  #Tautology    : 3206
% 10.96/4.28  #SimpNegUnit  : 2
% 10.96/4.28  #BackRed      : 0
% 10.96/4.28  
% 10.96/4.28  #Partial instantiations: 0
% 10.96/4.28  #Strategies tried      : 1
% 10.96/4.28  
% 10.96/4.28  Timing (in seconds)
% 10.96/4.28  ----------------------
% 10.96/4.28  Preprocessing        : 0.32
% 10.96/4.28  Parsing              : 0.17
% 10.96/4.28  CNF conversion       : 0.02
% 10.96/4.28  Main loop            : 3.21
% 10.96/4.28  Inferencing          : 0.66
% 10.96/4.28  Reduction            : 1.58
% 10.96/4.28  Demodulation         : 1.38
% 10.96/4.28  BG Simplification    : 0.09
% 10.96/4.28  Subsumption          : 0.72
% 10.96/4.29  Abstraction          : 0.13
% 10.96/4.29  MUC search           : 0.00
% 10.96/4.29  Cooper               : 0.00
% 10.96/4.29  Total                : 3.56
% 10.96/4.29  Index Insertion      : 0.00
% 10.96/4.29  Index Deletion       : 0.00
% 10.96/4.29  Index Matching       : 0.00
% 10.96/4.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
