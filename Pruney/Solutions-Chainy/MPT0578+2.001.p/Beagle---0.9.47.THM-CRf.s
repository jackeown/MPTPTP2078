%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:55 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   45 (  56 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :   12
%              Number of atoms          :   92 ( 120 expanded)
%              Number of equality atoms :   26 (  35 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => k1_relat_1(k5_relat_1(A,B)) = k10_relat_1(A,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t182_relat_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(A)
        & v1_relat_1(B) )
     => v1_relat_1(k5_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k10_relat_1(A,k2_relat_1(A)) = k1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t169_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k10_relat_1(B,A) = k10_relat_1(B,k3_xboole_0(k2_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t168_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ! [C] :
          ( v1_relat_1(C)
         => k10_relat_1(k5_relat_1(B,C),A) = k10_relat_1(B,k10_relat_1(C,A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t181_relat_1)).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( v1_relat_1(k5_relat_1(A_5,B_6))
      | ~ v1_relat_1(B_6)
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_9] :
      ( k10_relat_1(A_9,k2_relat_1(A_9)) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_tarski(B_2,A_1) = k2_tarski(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_52,plain,(
    ! [A_17,B_18] : k1_setfam_1(k2_tarski(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_67,plain,(
    ! [B_19,A_20] : k1_setfam_1(k2_tarski(B_19,A_20)) = k3_xboole_0(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_52])).

tff(c_4,plain,(
    ! [A_3,B_4] : k1_setfam_1(k2_tarski(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [B_19,A_20] : k3_xboole_0(B_19,A_20) = k3_xboole_0(A_20,B_19) ),
    inference(superposition,[status(thm),theory(equality)],[c_67,c_4])).

tff(c_134,plain,(
    ! [B_26,A_27] :
      ( k10_relat_1(B_26,k3_xboole_0(k2_relat_1(B_26),A_27)) = k10_relat_1(B_26,A_27)
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_144,plain,(
    ! [B_26,B_19] :
      ( k10_relat_1(B_26,k3_xboole_0(B_19,k2_relat_1(B_26))) = k10_relat_1(B_26,B_19)
      | ~ v1_relat_1(B_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_134])).

tff(c_178,plain,(
    ! [B_30,C_31,A_32] :
      ( k10_relat_1(k5_relat_1(B_30,C_31),A_32) = k10_relat_1(B_30,k10_relat_1(C_31,A_32))
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( k10_relat_1(B_8,k3_xboole_0(k2_relat_1(B_8),A_7)) = k10_relat_1(B_8,A_7)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_232,plain,(
    ! [B_35,C_36,A_37] :
      ( k10_relat_1(B_35,k10_relat_1(C_36,k3_xboole_0(k2_relat_1(k5_relat_1(B_35,C_36)),A_37))) = k10_relat_1(k5_relat_1(B_35,C_36),A_37)
      | ~ v1_relat_1(k5_relat_1(B_35,C_36))
      | ~ v1_relat_1(C_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_8])).

tff(c_308,plain,(
    ! [B_41,B_42] :
      ( k10_relat_1(B_41,k10_relat_1(B_42,k2_relat_1(k5_relat_1(B_41,B_42)))) = k10_relat_1(k5_relat_1(B_41,B_42),k2_relat_1(B_42))
      | ~ v1_relat_1(k5_relat_1(B_41,B_42))
      | ~ v1_relat_1(B_42)
      | ~ v1_relat_1(B_41)
      | ~ v1_relat_1(B_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_232])).

tff(c_193,plain,(
    ! [B_30,C_31] :
      ( k10_relat_1(B_30,k10_relat_1(C_31,k2_relat_1(k5_relat_1(B_30,C_31)))) = k1_relat_1(k5_relat_1(B_30,C_31))
      | ~ v1_relat_1(k5_relat_1(B_30,C_31))
      | ~ v1_relat_1(C_31)
      | ~ v1_relat_1(B_30) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_178,c_10])).

tff(c_360,plain,(
    ! [B_46,B_47] :
      ( k10_relat_1(k5_relat_1(B_46,B_47),k2_relat_1(B_47)) = k1_relat_1(k5_relat_1(B_46,B_47))
      | ~ v1_relat_1(k5_relat_1(B_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(k5_relat_1(B_46,B_47))
      | ~ v1_relat_1(B_47)
      | ~ v1_relat_1(B_46)
      | ~ v1_relat_1(B_47) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_193])).

tff(c_12,plain,(
    ! [B_11,C_13,A_10] :
      ( k10_relat_1(k5_relat_1(B_11,C_13),A_10) = k10_relat_1(B_11,k10_relat_1(C_13,A_10))
      | ~ v1_relat_1(C_13)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_376,plain,(
    ! [B_48,B_49] :
      ( k10_relat_1(B_48,k10_relat_1(B_49,k2_relat_1(B_49))) = k1_relat_1(k5_relat_1(B_48,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(k5_relat_1(B_48,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(k5_relat_1(B_48,B_49))
      | ~ v1_relat_1(B_49)
      | ~ v1_relat_1(B_48)
      | ~ v1_relat_1(B_49) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_360,c_12])).

tff(c_400,plain,(
    ! [B_50,A_51] :
      ( k10_relat_1(B_50,k1_relat_1(A_51)) = k1_relat_1(k5_relat_1(B_50,A_51))
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(k5_relat_1(B_50,A_51))
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(k5_relat_1(B_50,A_51))
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(B_50)
      | ~ v1_relat_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_376])).

tff(c_404,plain,(
    ! [A_52,B_53] :
      ( k10_relat_1(A_52,k1_relat_1(B_53)) = k1_relat_1(k5_relat_1(A_52,B_53))
      | ~ v1_relat_1(k5_relat_1(A_52,B_53))
      | ~ v1_relat_1(B_53)
      | ~ v1_relat_1(A_52) ) ),
    inference(resolution,[status(thm)],[c_6,c_400])).

tff(c_409,plain,(
    ! [A_54,B_55] :
      ( k10_relat_1(A_54,k1_relat_1(B_55)) = k1_relat_1(k5_relat_1(A_54,B_55))
      | ~ v1_relat_1(B_55)
      | ~ v1_relat_1(A_54) ) ),
    inference(resolution,[status(thm)],[c_6,c_404])).

tff(c_14,plain,(
    k10_relat_1('#skF_1',k1_relat_1('#skF_2')) != k1_relat_1(k5_relat_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_419,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_14])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_419])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:15:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.30  
% 2.12/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  %$ v1_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 2.12/1.31  
% 2.12/1.31  %Foreground sorts:
% 2.12/1.31  
% 2.12/1.31  
% 2.12/1.31  %Background operators:
% 2.12/1.31  
% 2.12/1.31  
% 2.12/1.31  %Foreground operators:
% 2.12/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.31  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.12/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.12/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.12/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.12/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.31  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.12/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.12/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.12/1.31  
% 2.12/1.32  tff(f_58, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k5_relat_1(A, B)) = k10_relat_1(A, k1_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t182_relat_1)).
% 2.12/1.32  tff(f_35, axiom, (![A, B]: ((v1_relat_1(A) & v1_relat_1(B)) => v1_relat_1(k5_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k5_relat_1)).
% 2.12/1.32  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k10_relat_1(A, k2_relat_1(A)) = k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t169_relat_1)).
% 2.12/1.32  tff(f_27, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.12/1.32  tff(f_29, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.12/1.32  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (k10_relat_1(B, A) = k10_relat_1(B, k3_xboole_0(k2_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t168_relat_1)).
% 2.12/1.32  tff(f_50, axiom, (![A, B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k10_relat_1(k5_relat_1(B, C), A) = k10_relat_1(B, k10_relat_1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t181_relat_1)).
% 2.12/1.32  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.32  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.32  tff(c_6, plain, (![A_5, B_6]: (v1_relat_1(k5_relat_1(A_5, B_6)) | ~v1_relat_1(B_6) | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.12/1.32  tff(c_10, plain, (![A_9]: (k10_relat_1(A_9, k2_relat_1(A_9))=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_tarski(B_2, A_1)=k2_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.12/1.32  tff(c_52, plain, (![A_17, B_18]: (k1_setfam_1(k2_tarski(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.32  tff(c_67, plain, (![B_19, A_20]: (k1_setfam_1(k2_tarski(B_19, A_20))=k3_xboole_0(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_2, c_52])).
% 2.12/1.32  tff(c_4, plain, (![A_3, B_4]: (k1_setfam_1(k2_tarski(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.32  tff(c_73, plain, (![B_19, A_20]: (k3_xboole_0(B_19, A_20)=k3_xboole_0(A_20, B_19))), inference(superposition, [status(thm), theory('equality')], [c_67, c_4])).
% 2.12/1.32  tff(c_134, plain, (![B_26, A_27]: (k10_relat_1(B_26, k3_xboole_0(k2_relat_1(B_26), A_27))=k10_relat_1(B_26, A_27) | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.32  tff(c_144, plain, (![B_26, B_19]: (k10_relat_1(B_26, k3_xboole_0(B_19, k2_relat_1(B_26)))=k10_relat_1(B_26, B_19) | ~v1_relat_1(B_26))), inference(superposition, [status(thm), theory('equality')], [c_73, c_134])).
% 2.12/1.32  tff(c_178, plain, (![B_30, C_31, A_32]: (k10_relat_1(k5_relat_1(B_30, C_31), A_32)=k10_relat_1(B_30, k10_relat_1(C_31, A_32)) | ~v1_relat_1(C_31) | ~v1_relat_1(B_30))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.32  tff(c_8, plain, (![B_8, A_7]: (k10_relat_1(B_8, k3_xboole_0(k2_relat_1(B_8), A_7))=k10_relat_1(B_8, A_7) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.32  tff(c_232, plain, (![B_35, C_36, A_37]: (k10_relat_1(B_35, k10_relat_1(C_36, k3_xboole_0(k2_relat_1(k5_relat_1(B_35, C_36)), A_37)))=k10_relat_1(k5_relat_1(B_35, C_36), A_37) | ~v1_relat_1(k5_relat_1(B_35, C_36)) | ~v1_relat_1(C_36) | ~v1_relat_1(B_35))), inference(superposition, [status(thm), theory('equality')], [c_178, c_8])).
% 2.12/1.32  tff(c_308, plain, (![B_41, B_42]: (k10_relat_1(B_41, k10_relat_1(B_42, k2_relat_1(k5_relat_1(B_41, B_42))))=k10_relat_1(k5_relat_1(B_41, B_42), k2_relat_1(B_42)) | ~v1_relat_1(k5_relat_1(B_41, B_42)) | ~v1_relat_1(B_42) | ~v1_relat_1(B_41) | ~v1_relat_1(B_42))), inference(superposition, [status(thm), theory('equality')], [c_144, c_232])).
% 2.12/1.32  tff(c_193, plain, (![B_30, C_31]: (k10_relat_1(B_30, k10_relat_1(C_31, k2_relat_1(k5_relat_1(B_30, C_31))))=k1_relat_1(k5_relat_1(B_30, C_31)) | ~v1_relat_1(k5_relat_1(B_30, C_31)) | ~v1_relat_1(C_31) | ~v1_relat_1(B_30))), inference(superposition, [status(thm), theory('equality')], [c_178, c_10])).
% 2.12/1.32  tff(c_360, plain, (![B_46, B_47]: (k10_relat_1(k5_relat_1(B_46, B_47), k2_relat_1(B_47))=k1_relat_1(k5_relat_1(B_46, B_47)) | ~v1_relat_1(k5_relat_1(B_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(B_46) | ~v1_relat_1(k5_relat_1(B_46, B_47)) | ~v1_relat_1(B_47) | ~v1_relat_1(B_46) | ~v1_relat_1(B_47))), inference(superposition, [status(thm), theory('equality')], [c_308, c_193])).
% 2.12/1.32  tff(c_12, plain, (![B_11, C_13, A_10]: (k10_relat_1(k5_relat_1(B_11, C_13), A_10)=k10_relat_1(B_11, k10_relat_1(C_13, A_10)) | ~v1_relat_1(C_13) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.12/1.32  tff(c_376, plain, (![B_48, B_49]: (k10_relat_1(B_48, k10_relat_1(B_49, k2_relat_1(B_49)))=k1_relat_1(k5_relat_1(B_48, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(B_48) | ~v1_relat_1(k5_relat_1(B_48, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(B_48) | ~v1_relat_1(k5_relat_1(B_48, B_49)) | ~v1_relat_1(B_49) | ~v1_relat_1(B_48) | ~v1_relat_1(B_49))), inference(superposition, [status(thm), theory('equality')], [c_360, c_12])).
% 2.12/1.32  tff(c_400, plain, (![B_50, A_51]: (k10_relat_1(B_50, k1_relat_1(A_51))=k1_relat_1(k5_relat_1(B_50, A_51)) | ~v1_relat_1(A_51) | ~v1_relat_1(B_50) | ~v1_relat_1(k5_relat_1(B_50, A_51)) | ~v1_relat_1(A_51) | ~v1_relat_1(B_50) | ~v1_relat_1(k5_relat_1(B_50, A_51)) | ~v1_relat_1(A_51) | ~v1_relat_1(B_50) | ~v1_relat_1(A_51) | ~v1_relat_1(A_51))), inference(superposition, [status(thm), theory('equality')], [c_10, c_376])).
% 2.12/1.32  tff(c_404, plain, (![A_52, B_53]: (k10_relat_1(A_52, k1_relat_1(B_53))=k1_relat_1(k5_relat_1(A_52, B_53)) | ~v1_relat_1(k5_relat_1(A_52, B_53)) | ~v1_relat_1(B_53) | ~v1_relat_1(A_52))), inference(resolution, [status(thm)], [c_6, c_400])).
% 2.12/1.32  tff(c_409, plain, (![A_54, B_55]: (k10_relat_1(A_54, k1_relat_1(B_55))=k1_relat_1(k5_relat_1(A_54, B_55)) | ~v1_relat_1(B_55) | ~v1_relat_1(A_54))), inference(resolution, [status(thm)], [c_6, c_404])).
% 2.12/1.32  tff(c_14, plain, (k10_relat_1('#skF_1', k1_relat_1('#skF_2'))!=k1_relat_1(k5_relat_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.12/1.32  tff(c_419, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_409, c_14])).
% 2.12/1.32  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_419])).
% 2.12/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.32  
% 2.12/1.32  Inference rules
% 2.12/1.32  ----------------------
% 2.12/1.32  #Ref     : 0
% 2.12/1.32  #Sup     : 99
% 2.12/1.32  #Fact    : 0
% 2.12/1.32  #Define  : 0
% 2.12/1.32  #Split   : 0
% 2.12/1.32  #Chain   : 0
% 2.12/1.32  #Close   : 0
% 2.12/1.32  
% 2.12/1.32  Ordering : KBO
% 2.12/1.32  
% 2.12/1.32  Simplification rules
% 2.12/1.32  ----------------------
% 2.12/1.32  #Subsume      : 16
% 2.12/1.32  #Demod        : 5
% 2.12/1.32  #Tautology    : 50
% 2.12/1.32  #SimpNegUnit  : 0
% 2.12/1.32  #BackRed      : 0
% 2.12/1.32  
% 2.12/1.32  #Partial instantiations: 0
% 2.12/1.32  #Strategies tried      : 1
% 2.12/1.32  
% 2.12/1.32  Timing (in seconds)
% 2.12/1.32  ----------------------
% 2.12/1.32  Preprocessing        : 0.27
% 2.12/1.32  Parsing              : 0.15
% 2.12/1.32  CNF conversion       : 0.02
% 2.12/1.32  Main loop            : 0.26
% 2.12/1.32  Inferencing          : 0.11
% 2.12/1.32  Reduction            : 0.07
% 2.12/1.32  Demodulation         : 0.05
% 2.12/1.32  BG Simplification    : 0.02
% 2.12/1.32  Subsumption          : 0.05
% 2.12/1.32  Abstraction          : 0.01
% 2.12/1.32  MUC search           : 0.00
% 2.12/1.32  Cooper               : 0.00
% 2.12/1.32  Total                : 0.56
% 2.12/1.32  Index Insertion      : 0.00
% 2.12/1.32  Index Deletion       : 0.00
% 2.12/1.32  Index Matching       : 0.00
% 2.12/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
