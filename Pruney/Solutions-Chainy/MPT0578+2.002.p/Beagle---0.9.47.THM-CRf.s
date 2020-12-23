%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:55 EST 2020

% Result     : Theorem 6.16s
% Output     : CNFRefutation 6.16s
% Verified   : 
% Statistics : Number of formulae       :   43 (  55 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   90 ( 120 expanded)
%              Number of equality atoms :   17 (  25 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => r1_tarski(k10_relat_1(C,A),k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_18,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k5_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( r1_tarski(k10_relat_1(B_8,A_7),k1_relat_1(B_8))
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,(
    ! [B_35,C_36,A_37] :
      ( k10_relat_1(k5_relat_1(B_35,C_36),A_37) = k10_relat_1(B_35,k10_relat_1(C_36,A_37))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_345,plain,(
    ! [B_68,C_69] :
      ( k10_relat_1(B_68,k10_relat_1(C_69,k2_relat_1(k5_relat_1(B_68,C_69)))) = k1_relat_1(k5_relat_1(B_68,C_69))
      | ~ v1_relat_1(k5_relat_1(B_68,C_69))
      | ~ v1_relat_1(C_69)
      | ~ v1_relat_1(B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_10])).

tff(c_12,plain,(
    ! [C_12,A_10,B_11] :
      ( r1_tarski(k10_relat_1(C_12,A_10),k10_relat_1(C_12,B_11))
      | ~ r1_tarski(A_10,B_11)
      | ~ v1_relat_1(C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3132,plain,(
    ! [B_232,C_233,B_234] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_232,C_233)),k10_relat_1(B_232,B_234))
      | ~ r1_tarski(k10_relat_1(C_233,k2_relat_1(k5_relat_1(B_232,C_233))),B_234)
      | ~ v1_relat_1(B_232)
      | ~ v1_relat_1(k5_relat_1(B_232,C_233))
      | ~ v1_relat_1(C_233)
      | ~ v1_relat_1(B_232) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_12])).

tff(c_3152,plain,(
    ! [B_235,B_236] :
      ( r1_tarski(k1_relat_1(k5_relat_1(B_235,B_236)),k10_relat_1(B_235,k1_relat_1(B_236)))
      | ~ v1_relat_1(k5_relat_1(B_235,B_236))
      | ~ v1_relat_1(B_235)
      | ~ v1_relat_1(B_236) ) ),
    inference(resolution,[status(thm)],[c_8,c_3132])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_3167,plain,(
    ! [B_237,B_238] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(B_237,B_238)),k10_relat_1(B_237,k1_relat_1(B_238))) = k1_relat_1(k5_relat_1(B_237,B_238))
      | ~ v1_relat_1(k5_relat_1(B_237,B_238))
      | ~ v1_relat_1(B_237)
      | ~ v1_relat_1(B_238) ) ),
    inference(resolution,[status(thm)],[c_3152,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_276,plain,(
    ! [B_53,C_54,A_55] :
      ( r1_tarski(k10_relat_1(B_53,k10_relat_1(C_54,A_55)),k1_relat_1(k5_relat_1(B_53,C_54)))
      | ~ v1_relat_1(k5_relat_1(B_53,C_54))
      | ~ v1_relat_1(C_54)
      | ~ v1_relat_1(B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_8])).

tff(c_323,plain,(
    ! [B_60,A_61] :
      ( r1_tarski(k10_relat_1(B_60,k1_relat_1(A_61)),k1_relat_1(k5_relat_1(B_60,A_61)))
      | ~ v1_relat_1(k5_relat_1(B_60,A_61))
      | ~ v1_relat_1(A_61)
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_276])).

tff(c_328,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(k10_relat_1(B_60,k1_relat_1(A_61)),k1_relat_1(k5_relat_1(B_60,A_61))) = k10_relat_1(B_60,k1_relat_1(A_61))
      | ~ v1_relat_1(k5_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(resolution,[status(thm)],[c_323,c_4])).

tff(c_335,plain,(
    ! [B_60,A_61] :
      ( k3_xboole_0(k1_relat_1(k5_relat_1(B_60,A_61)),k10_relat_1(B_60,k1_relat_1(A_61))) = k10_relat_1(B_60,k1_relat_1(A_61))
      | ~ v1_relat_1(k5_relat_1(B_60,A_61))
      | ~ v1_relat_1(B_60)
      | ~ v1_relat_1(A_61) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_328])).

tff(c_3482,plain,(
    ! [B_251,B_252] :
      ( k10_relat_1(B_251,k1_relat_1(B_252)) = k1_relat_1(k5_relat_1(B_251,B_252))
      | ~ v1_relat_1(k5_relat_1(B_251,B_252))
      | ~ v1_relat_1(B_251)
      | ~ v1_relat_1(B_252)
      | ~ v1_relat_1(k5_relat_1(B_251,B_252))
      | ~ v1_relat_1(B_251)
      | ~ v1_relat_1(B_252) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3167,c_335])).

tff(c_3486,plain,(
    ! [A_253,B_254] :
      ( k10_relat_1(A_253,k1_relat_1(B_254)) = k1_relat_1(k5_relat_1(A_253,B_254))
      | ~ v1_relat_1(k5_relat_1(A_253,B_254))
      | ~ v1_relat_1(B_254)
      | ~ v1_relat_1(A_253) ) ),
    inference(resolution,[status(thm)],[c_6,c_3482])).

tff(c_3491,plain,(
    ! [A_255,B_256] :
      ( k10_relat_1(A_255,k1_relat_1(B_256)) = k1_relat_1(k5_relat_1(A_255,B_256))
      | ~ v1_relat_1(B_256)
      | ~ v1_relat_1(A_255) ) ),
    inference(resolution,[status(thm)],[c_6,c_3486])).

tff(c_16,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_3753,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_3491,c_16])).

tff(c_3771,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_18,c_3753])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:06:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.16/2.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.27  
% 6.16/2.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.27  %$ r1_tarski > v1_relat_1 > k5_relat_1 > k3_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_2 > #skF_1
% 6.16/2.27  
% 6.16/2.27  %Foreground sorts:
% 6.16/2.27  
% 6.16/2.27  
% 6.16/2.27  %Background operators:
% 6.16/2.27  
% 6.16/2.27  
% 6.16/2.27  %Foreground operators:
% 6.16/2.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.16/2.27  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 6.16/2.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.16/2.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.16/2.27  tff('#skF_2', type, '#skF_2': $i).
% 6.16/2.27  tff('#skF_1', type, '#skF_1': $i).
% 6.16/2.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.16/2.27  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.16/2.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.16/2.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.16/2.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.16/2.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.16/2.27  
% 6.16/2.29  tff(f_66, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 6.16/2.29  tff(f_37, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 6.16/2.29  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t167_relat_1)).
% 6.16/2.29  tff(f_58, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 6.16/2.29  tff(f_45, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 6.16/2.29  tff(f_51, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => r1_tarski(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_relat_1)).
% 6.16/2.29  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.16/2.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.16/2.29  tff(c_20, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.16/2.29  tff(c_18, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.16/2.29  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k5_relat_1(A_5, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.16/2.29  tff(c_8, plain, (![B_8, A_7]: (r1_tarski(k10_relat_1(B_8, A_7), k1_relat_1(B_8)) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.16/2.29  tff(c_126, plain, (![B_35, C_36, A_37]: (k10_relat_1(k5_relat_1(B_35, C_36), A_37)=k10_relat_1(B_35, k10_relat_1(C_36, A_37)) | ~v1_relat_1(C_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.16/2.29  tff(c_10, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.16/2.29  tff(c_345, plain, (![B_68, C_69]: (k10_relat_1(B_68, k10_relat_1(C_69, k2_relat_1(k5_relat_1(B_68, C_69))))=k1_relat_1(k5_relat_1(B_68, C_69)) | ~v1_relat_1(k5_relat_1(B_68, C_69)) | ~v1_relat_1(C_69) | ~v1_relat_1(B_68))), inference(superposition, [status(thm), theory('equality')], [c_126, c_10])).
% 6.16/2.29  tff(c_12, plain, (![C_12, A_10, B_11]: (r1_tarski(k10_relat_1(C_12, A_10), k10_relat_1(C_12, B_11)) | ~r1_tarski(A_10, B_11) | ~v1_relat_1(C_12))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.16/2.29  tff(c_3132, plain, (![B_232, C_233, B_234]: (r1_tarski(k1_relat_1(k5_relat_1(B_232, C_233)), k10_relat_1(B_232, B_234)) | ~r1_tarski(k10_relat_1(C_233, k2_relat_1(k5_relat_1(B_232, C_233))), B_234) | ~v1_relat_1(B_232) | ~v1_relat_1(k5_relat_1(B_232, C_233)) | ~v1_relat_1(C_233) | ~v1_relat_1(B_232))), inference(superposition, [status(thm), theory('equality')], [c_345, c_12])).
% 6.16/2.29  tff(c_3152, plain, (![B_235, B_236]: (r1_tarski(k1_relat_1(k5_relat_1(B_235, B_236)), k10_relat_1(B_235, k1_relat_1(B_236))) | ~v1_relat_1(k5_relat_1(B_235, B_236)) | ~v1_relat_1(B_235) | ~v1_relat_1(B_236))), inference(resolution, [status(thm)], [c_8, c_3132])).
% 6.16/2.29  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.16/2.29  tff(c_3167, plain, (![B_237, B_238]: (k3_xboole_0(k1_relat_1(k5_relat_1(B_237, B_238)), k10_relat_1(B_237, k1_relat_1(B_238)))=k1_relat_1(k5_relat_1(B_237, B_238)) | ~v1_relat_1(k5_relat_1(B_237, B_238)) | ~v1_relat_1(B_237) | ~v1_relat_1(B_238))), inference(resolution, [status(thm)], [c_3152, c_4])).
% 6.16/2.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.16/2.29  tff(c_276, plain, (![B_53, C_54, A_55]: (r1_tarski(k10_relat_1(B_53, k10_relat_1(C_54, A_55)), k1_relat_1(k5_relat_1(B_53, C_54))) | ~v1_relat_1(k5_relat_1(B_53, C_54)) | ~v1_relat_1(C_54) | ~v1_relat_1(B_53))), inference(superposition, [status(thm), theory('equality')], [c_126, c_8])).
% 6.16/2.29  tff(c_323, plain, (![B_60, A_61]: (r1_tarski(k10_relat_1(B_60, k1_relat_1(A_61)), k1_relat_1(k5_relat_1(B_60, A_61))) | ~v1_relat_1(k5_relat_1(B_60, A_61)) | ~v1_relat_1(A_61) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(superposition, [status(thm), theory('equality')], [c_10, c_276])).
% 6.16/2.29  tff(c_328, plain, (![B_60, A_61]: (k3_xboole_0(k10_relat_1(B_60, k1_relat_1(A_61)), k1_relat_1(k5_relat_1(B_60, A_61)))=k10_relat_1(B_60, k1_relat_1(A_61)) | ~v1_relat_1(k5_relat_1(B_60, A_61)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(resolution, [status(thm)], [c_323, c_4])).
% 6.16/2.29  tff(c_335, plain, (![B_60, A_61]: (k3_xboole_0(k1_relat_1(k5_relat_1(B_60, A_61)), k10_relat_1(B_60, k1_relat_1(A_61)))=k10_relat_1(B_60, k1_relat_1(A_61)) | ~v1_relat_1(k5_relat_1(B_60, A_61)) | ~v1_relat_1(B_60) | ~v1_relat_1(A_61))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_328])).
% 6.16/2.29  tff(c_3482, plain, (![B_251, B_252]: (k10_relat_1(B_251, k1_relat_1(B_252))=k1_relat_1(k5_relat_1(B_251, B_252)) | ~v1_relat_1(k5_relat_1(B_251, B_252)) | ~v1_relat_1(B_251) | ~v1_relat_1(B_252) | ~v1_relat_1(k5_relat_1(B_251, B_252)) | ~v1_relat_1(B_251) | ~v1_relat_1(B_252))), inference(superposition, [status(thm), theory('equality')], [c_3167, c_335])).
% 6.16/2.29  tff(c_3486, plain, (![A_253, B_254]: (k10_relat_1(A_253, k1_relat_1(B_254))=k1_relat_1(k5_relat_1(A_253, B_254)) | ~v1_relat_1(k5_relat_1(A_253, B_254)) | ~v1_relat_1(B_254) | ~v1_relat_1(A_253))), inference(resolution, [status(thm)], [c_6, c_3482])).
% 6.16/2.29  tff(c_3491, plain, (![A_255, B_256]: (k10_relat_1(A_255, k1_relat_1(B_256))=k1_relat_1(k5_relat_1(A_255, B_256)) | ~v1_relat_1(B_256) | ~v1_relat_1(A_255))), inference(resolution, [status(thm)], [c_6, c_3486])).
% 6.16/2.29  tff(c_16, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.16/2.29  tff(c_3753, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_3491, c_16])).
% 6.16/2.29  tff(c_3771, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_18, c_3753])).
% 6.16/2.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.16/2.29  
% 6.16/2.29  Inference rules
% 6.16/2.29  ----------------------
% 6.16/2.29  #Ref     : 0
% 6.16/2.29  #Sup     : 1099
% 6.16/2.29  #Fact    : 0
% 6.16/2.29  #Define  : 0
% 6.16/2.29  #Split   : 0
% 6.16/2.29  #Chain   : 0
% 6.16/2.29  #Close   : 0
% 6.16/2.29  
% 6.16/2.29  Ordering : KBO
% 6.16/2.29  
% 6.16/2.29  Simplification rules
% 6.16/2.29  ----------------------
% 6.16/2.29  #Subsume      : 191
% 6.16/2.29  #Demod        : 31
% 6.16/2.29  #Tautology    : 112
% 6.16/2.29  #SimpNegUnit  : 0
% 6.16/2.29  #BackRed      : 0
% 6.16/2.29  
% 6.16/2.29  #Partial instantiations: 0
% 6.16/2.29  #Strategies tried      : 1
% 6.16/2.29  
% 6.16/2.29  Timing (in seconds)
% 6.16/2.29  ----------------------
% 6.16/2.29  Preprocessing        : 0.31
% 6.16/2.29  Parsing              : 0.17
% 6.16/2.29  CNF conversion       : 0.02
% 6.16/2.29  Main loop            : 1.16
% 6.16/2.29  Inferencing          : 0.42
% 6.16/2.29  Reduction            : 0.28
% 6.16/2.29  Demodulation         : 0.20
% 6.16/2.29  BG Simplification    : 0.06
% 6.16/2.29  Subsumption          : 0.34
% 6.16/2.29  Abstraction          : 0.06
% 6.16/2.29  MUC search           : 0.00
% 6.16/2.29  Cooper               : 0.00
% 6.16/2.29  Total                : 1.49
% 6.16/2.29  Index Insertion      : 0.00
% 6.16/2.29  Index Deletion       : 0.00
% 6.16/2.29  Index Matching       : 0.00
% 6.16/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
