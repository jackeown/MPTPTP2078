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
% DateTime   : Thu Dec  3 10:01:00 EST 2020

% Result     : Theorem 4.80s
% Output     : CNFRefutation 4.80s
% Verified   : 
% Statistics : Number of formulae       :   59 (  94 expanded)
%              Number of leaves         :   24 (  42 expanded)
%              Depth                    :    9
%              Number of atoms          :   95 ( 163 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => r1_tarski(k9_relat_1(C,k3_xboole_0(A,B)),k3_xboole_0(k9_relat_1(C,A),k9_relat_1(C,B))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t154_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r1_tarski(A,B)
       => k7_relat_1(k7_relat_1(C,B),A) = k7_relat_1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k9_relat_1(B,A),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t144_relat_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_22,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( v1_relat_1(k7_relat_1(A_12,B_13))
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ! [A_29,B_30] : k1_setfam_1(k2_tarski(A_29,B_30)) = k3_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [B_31,A_32] : k1_setfam_1(k2_tarski(B_31,A_32)) = k3_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_67])).

tff(c_10,plain,(
    ! [A_10,B_11] : k1_setfam_1(k2_tarski(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [B_33,A_34] : k3_xboole_0(B_33,A_34) = k3_xboole_0(A_34,B_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_10])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_120,plain,(
    ! [B_33,A_34] : r1_tarski(k3_xboole_0(B_33,A_34),A_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_2])).

tff(c_18,plain,(
    ! [B_20,A_19] :
      ( k2_relat_1(k7_relat_1(B_20,A_19)) = k9_relat_1(B_20,A_19)
      | ~ v1_relat_1(B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_179,plain,(
    ! [C_44,B_45,A_46] :
      ( k7_relat_1(k7_relat_1(C_44,B_45),A_46) = k7_relat_1(C_44,A_46)
      | ~ r1_tarski(A_46,B_45)
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_962,plain,(
    ! [C_140,B_141,A_142] :
      ( k9_relat_1(k7_relat_1(C_140,B_141),A_142) = k2_relat_1(k7_relat_1(C_140,A_142))
      | ~ v1_relat_1(k7_relat_1(C_140,B_141))
      | ~ r1_tarski(A_142,B_141)
      | ~ v1_relat_1(C_140) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_18])).

tff(c_968,plain,(
    ! [A_143,B_144,A_145] :
      ( k9_relat_1(k7_relat_1(A_143,B_144),A_145) = k2_relat_1(k7_relat_1(A_143,A_145))
      | ~ r1_tarski(A_145,B_144)
      | ~ v1_relat_1(A_143) ) ),
    inference(resolution,[status(thm)],[c_12,c_962])).

tff(c_156,plain,(
    ! [B_39,A_40] :
      ( k2_relat_1(k7_relat_1(B_39,A_40)) = k9_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_16,plain,(
    ! [B_18,A_17] :
      ( r1_tarski(k9_relat_1(B_18,A_17),k2_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_162,plain,(
    ! [B_39,A_40,A_17] :
      ( r1_tarski(k9_relat_1(k7_relat_1(B_39,A_40),A_17),k9_relat_1(B_39,A_40))
      | ~ v1_relat_1(k7_relat_1(B_39,A_40))
      | ~ v1_relat_1(B_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_16])).

tff(c_1030,plain,(
    ! [A_157,A_158,B_159] :
      ( r1_tarski(k2_relat_1(k7_relat_1(A_157,A_158)),k9_relat_1(A_157,B_159))
      | ~ v1_relat_1(k7_relat_1(A_157,B_159))
      | ~ v1_relat_1(A_157)
      | ~ r1_tarski(A_158,B_159)
      | ~ v1_relat_1(A_157) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_162])).

tff(c_2105,plain,(
    ! [B_239,A_240,B_241] :
      ( r1_tarski(k9_relat_1(B_239,A_240),k9_relat_1(B_239,B_241))
      | ~ v1_relat_1(k7_relat_1(B_239,B_241))
      | ~ v1_relat_1(B_239)
      | ~ r1_tarski(A_240,B_241)
      | ~ v1_relat_1(B_239)
      | ~ v1_relat_1(B_239) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_1030])).

tff(c_205,plain,(
    ! [C_50,B_51,A_52] :
      ( k9_relat_1(k7_relat_1(C_50,B_51),A_52) = k2_relat_1(k7_relat_1(C_50,A_52))
      | ~ v1_relat_1(k7_relat_1(C_50,B_51))
      | ~ r1_tarski(A_52,B_51)
      | ~ v1_relat_1(C_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_18])).

tff(c_211,plain,(
    ! [A_53,B_54,A_55] :
      ( k9_relat_1(k7_relat_1(A_53,B_54),A_55) = k2_relat_1(k7_relat_1(A_53,A_55))
      | ~ r1_tarski(A_55,B_54)
      | ~ v1_relat_1(A_53) ) ),
    inference(resolution,[status(thm)],[c_12,c_205])).

tff(c_245,plain,(
    ! [A_59,A_60,B_61] :
      ( r1_tarski(k2_relat_1(k7_relat_1(A_59,A_60)),k9_relat_1(A_59,B_61))
      | ~ v1_relat_1(k7_relat_1(A_59,B_61))
      | ~ v1_relat_1(A_59)
      | ~ r1_tarski(A_60,B_61)
      | ~ v1_relat_1(A_59) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_162])).

tff(c_934,plain,(
    ! [B_137,A_138,B_139] :
      ( r1_tarski(k9_relat_1(B_137,A_138),k9_relat_1(B_137,B_139))
      | ~ v1_relat_1(k7_relat_1(B_137,B_139))
      | ~ v1_relat_1(B_137)
      | ~ r1_tarski(A_138,B_139)
      | ~ v1_relat_1(B_137)
      | ~ v1_relat_1(B_137) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_245])).

tff(c_168,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(A_41,k3_xboole_0(B_42,C_43))
      | ~ r1_tarski(A_41,C_43)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k9_relat_1('#skF_3','#skF_1'),k9_relat_1('#skF_3','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_178,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(resolution,[status(thm)],[c_168,c_20])).

tff(c_204,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_941,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_1')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_934,c_204])).

tff(c_952,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_941])).

tff(c_955,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_952])).

tff(c_959,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_955])).

tff(c_960,plain,(
    ~ r1_tarski(k9_relat_1('#skF_3',k3_xboole_0('#skF_1','#skF_2')),k9_relat_1('#skF_3','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_2115,plain,
    ( ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski(k3_xboole_0('#skF_1','#skF_2'),'#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_2105,c_960])).

tff(c_2129,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_120,c_2115])).

tff(c_2313,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_2129])).

tff(c_2317,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2313])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:35:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.80/1.92  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.93  
% 4.80/1.93  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.93  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 4.80/1.93  
% 4.80/1.93  %Foreground sorts:
% 4.80/1.93  
% 4.80/1.93  
% 4.80/1.93  %Background operators:
% 4.80/1.93  
% 4.80/1.93  
% 4.80/1.93  %Foreground operators:
% 4.80/1.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.80/1.93  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.80/1.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.80/1.93  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.80/1.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.80/1.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.80/1.93  tff('#skF_2', type, '#skF_2': $i).
% 4.80/1.93  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.80/1.93  tff('#skF_3', type, '#skF_3': $i).
% 4.80/1.93  tff('#skF_1', type, '#skF_1': $i).
% 4.80/1.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.80/1.93  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.80/1.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.80/1.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.80/1.93  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.80/1.93  
% 4.80/1.94  tff(f_62, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => r1_tarski(k9_relat_1(C, k3_xboole_0(A, B)), k3_xboole_0(k9_relat_1(C, A), k9_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t154_relat_1)).
% 4.80/1.94  tff(f_43, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 4.80/1.94  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.80/1.94  tff(f_39, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 4.80/1.94  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 4.80/1.94  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 4.80/1.94  tff(f_49, axiom, (![A, B, C]: (v1_relat_1(C) => (r1_tarski(A, B) => (k7_relat_1(k7_relat_1(C, B), A) = k7_relat_1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_relat_1)).
% 4.80/1.94  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k9_relat_1(B, A), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t144_relat_1)).
% 4.80/1.94  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_xboole_1)).
% 4.80/1.94  tff(c_22, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.80/1.94  tff(c_12, plain, (![A_12, B_13]: (v1_relat_1(k7_relat_1(A_12, B_13)) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.80/1.94  tff(c_6, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.80/1.94  tff(c_67, plain, (![A_29, B_30]: (k1_setfam_1(k2_tarski(A_29, B_30))=k3_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.80/1.94  tff(c_82, plain, (![B_31, A_32]: (k1_setfam_1(k2_tarski(B_31, A_32))=k3_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_6, c_67])).
% 4.80/1.94  tff(c_10, plain, (![A_10, B_11]: (k1_setfam_1(k2_tarski(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.80/1.94  tff(c_105, plain, (![B_33, A_34]: (k3_xboole_0(B_33, A_34)=k3_xboole_0(A_34, B_33))), inference(superposition, [status(thm), theory('equality')], [c_82, c_10])).
% 4.80/1.94  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.80/1.94  tff(c_120, plain, (![B_33, A_34]: (r1_tarski(k3_xboole_0(B_33, A_34), A_34))), inference(superposition, [status(thm), theory('equality')], [c_105, c_2])).
% 4.80/1.94  tff(c_18, plain, (![B_20, A_19]: (k2_relat_1(k7_relat_1(B_20, A_19))=k9_relat_1(B_20, A_19) | ~v1_relat_1(B_20))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.80/1.94  tff(c_179, plain, (![C_44, B_45, A_46]: (k7_relat_1(k7_relat_1(C_44, B_45), A_46)=k7_relat_1(C_44, A_46) | ~r1_tarski(A_46, B_45) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.80/1.94  tff(c_962, plain, (![C_140, B_141, A_142]: (k9_relat_1(k7_relat_1(C_140, B_141), A_142)=k2_relat_1(k7_relat_1(C_140, A_142)) | ~v1_relat_1(k7_relat_1(C_140, B_141)) | ~r1_tarski(A_142, B_141) | ~v1_relat_1(C_140))), inference(superposition, [status(thm), theory('equality')], [c_179, c_18])).
% 4.80/1.94  tff(c_968, plain, (![A_143, B_144, A_145]: (k9_relat_1(k7_relat_1(A_143, B_144), A_145)=k2_relat_1(k7_relat_1(A_143, A_145)) | ~r1_tarski(A_145, B_144) | ~v1_relat_1(A_143))), inference(resolution, [status(thm)], [c_12, c_962])).
% 4.80/1.94  tff(c_156, plain, (![B_39, A_40]: (k2_relat_1(k7_relat_1(B_39, A_40))=k9_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.80/1.94  tff(c_16, plain, (![B_18, A_17]: (r1_tarski(k9_relat_1(B_18, A_17), k2_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.80/1.94  tff(c_162, plain, (![B_39, A_40, A_17]: (r1_tarski(k9_relat_1(k7_relat_1(B_39, A_40), A_17), k9_relat_1(B_39, A_40)) | ~v1_relat_1(k7_relat_1(B_39, A_40)) | ~v1_relat_1(B_39))), inference(superposition, [status(thm), theory('equality')], [c_156, c_16])).
% 4.80/1.94  tff(c_1030, plain, (![A_157, A_158, B_159]: (r1_tarski(k2_relat_1(k7_relat_1(A_157, A_158)), k9_relat_1(A_157, B_159)) | ~v1_relat_1(k7_relat_1(A_157, B_159)) | ~v1_relat_1(A_157) | ~r1_tarski(A_158, B_159) | ~v1_relat_1(A_157))), inference(superposition, [status(thm), theory('equality')], [c_968, c_162])).
% 4.80/1.94  tff(c_2105, plain, (![B_239, A_240, B_241]: (r1_tarski(k9_relat_1(B_239, A_240), k9_relat_1(B_239, B_241)) | ~v1_relat_1(k7_relat_1(B_239, B_241)) | ~v1_relat_1(B_239) | ~r1_tarski(A_240, B_241) | ~v1_relat_1(B_239) | ~v1_relat_1(B_239))), inference(superposition, [status(thm), theory('equality')], [c_18, c_1030])).
% 4.80/1.94  tff(c_205, plain, (![C_50, B_51, A_52]: (k9_relat_1(k7_relat_1(C_50, B_51), A_52)=k2_relat_1(k7_relat_1(C_50, A_52)) | ~v1_relat_1(k7_relat_1(C_50, B_51)) | ~r1_tarski(A_52, B_51) | ~v1_relat_1(C_50))), inference(superposition, [status(thm), theory('equality')], [c_179, c_18])).
% 4.80/1.94  tff(c_211, plain, (![A_53, B_54, A_55]: (k9_relat_1(k7_relat_1(A_53, B_54), A_55)=k2_relat_1(k7_relat_1(A_53, A_55)) | ~r1_tarski(A_55, B_54) | ~v1_relat_1(A_53))), inference(resolution, [status(thm)], [c_12, c_205])).
% 4.80/1.94  tff(c_245, plain, (![A_59, A_60, B_61]: (r1_tarski(k2_relat_1(k7_relat_1(A_59, A_60)), k9_relat_1(A_59, B_61)) | ~v1_relat_1(k7_relat_1(A_59, B_61)) | ~v1_relat_1(A_59) | ~r1_tarski(A_60, B_61) | ~v1_relat_1(A_59))), inference(superposition, [status(thm), theory('equality')], [c_211, c_162])).
% 4.80/1.94  tff(c_934, plain, (![B_137, A_138, B_139]: (r1_tarski(k9_relat_1(B_137, A_138), k9_relat_1(B_137, B_139)) | ~v1_relat_1(k7_relat_1(B_137, B_139)) | ~v1_relat_1(B_137) | ~r1_tarski(A_138, B_139) | ~v1_relat_1(B_137) | ~v1_relat_1(B_137))), inference(superposition, [status(thm), theory('equality')], [c_18, c_245])).
% 4.80/1.94  tff(c_168, plain, (![A_41, B_42, C_43]: (r1_tarski(A_41, k3_xboole_0(B_42, C_43)) | ~r1_tarski(A_41, C_43) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.80/1.94  tff(c_20, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k9_relat_1('#skF_3', '#skF_1'), k9_relat_1('#skF_3', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.80/1.94  tff(c_178, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(resolution, [status(thm)], [c_168, c_20])).
% 4.80/1.94  tff(c_204, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_1'))), inference(splitLeft, [status(thm)], [c_178])).
% 4.80/1.94  tff(c_941, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_1') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_934, c_204])).
% 4.80/1.94  tff(c_952, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_941])).
% 4.80/1.94  tff(c_955, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_952])).
% 4.80/1.94  tff(c_959, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_955])).
% 4.80/1.94  tff(c_960, plain, (~r1_tarski(k9_relat_1('#skF_3', k3_xboole_0('#skF_1', '#skF_2')), k9_relat_1('#skF_3', '#skF_2'))), inference(splitRight, [status(thm)], [c_178])).
% 4.80/1.94  tff(c_2115, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2')) | ~r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_2105, c_960])).
% 4.80/1.94  tff(c_2129, plain, (~v1_relat_1(k7_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_120, c_2115])).
% 4.80/1.94  tff(c_2313, plain, (~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_12, c_2129])).
% 4.80/1.94  tff(c_2317, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_2313])).
% 4.80/1.94  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.80/1.94  
% 4.80/1.94  Inference rules
% 4.80/1.94  ----------------------
% 4.80/1.94  #Ref     : 0
% 4.80/1.94  #Sup     : 651
% 4.80/1.94  #Fact    : 0
% 4.80/1.94  #Define  : 0
% 4.80/1.94  #Split   : 1
% 4.80/1.94  #Chain   : 0
% 4.80/1.94  #Close   : 0
% 4.80/1.94  
% 4.80/1.94  Ordering : KBO
% 4.80/1.94  
% 4.80/1.94  Simplification rules
% 4.80/1.94  ----------------------
% 4.80/1.94  #Subsume      : 173
% 4.80/1.94  #Demod        : 20
% 4.80/1.94  #Tautology    : 60
% 4.80/1.94  #SimpNegUnit  : 0
% 4.80/1.94  #BackRed      : 0
% 4.80/1.94  
% 4.80/1.94  #Partial instantiations: 0
% 4.80/1.94  #Strategies tried      : 1
% 4.80/1.94  
% 4.80/1.94  Timing (in seconds)
% 4.80/1.94  ----------------------
% 4.80/1.95  Preprocessing        : 0.32
% 4.80/1.95  Parsing              : 0.15
% 4.80/1.95  CNF conversion       : 0.02
% 4.80/1.95  Main loop            : 0.86
% 4.80/1.95  Inferencing          : 0.29
% 4.80/1.95  Reduction            : 0.29
% 4.80/1.95  Demodulation         : 0.23
% 4.80/1.95  BG Simplification    : 0.04
% 4.80/1.95  Subsumption          : 0.19
% 4.80/1.95  Abstraction          : 0.05
% 4.80/1.95  MUC search           : 0.00
% 4.80/1.95  Cooper               : 0.00
% 4.80/1.95  Total                : 1.21
% 4.80/1.95  Index Insertion      : 0.00
% 4.80/1.95  Index Deletion       : 0.00
% 4.80/1.95  Index Matching       : 0.00
% 4.80/1.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
