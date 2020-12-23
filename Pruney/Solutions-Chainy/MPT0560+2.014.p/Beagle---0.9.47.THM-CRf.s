%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:12 EST 2020

% Result     : Theorem 2.42s
% Output     : CNFRefutation 2.42s
% Verified   : 
% Statistics : Number of formulae       :   57 (  72 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :   13
%              Number of atoms          :   72 (  97 expanded)
%              Number of equality atoms :   32 (  42 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B,C] :
            ( r1_tarski(B,C)
           => k9_relat_1(k7_relat_1(A,C),B) = k9_relat_1(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_29,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k1_relat_1(k7_relat_1(B,A)) = k3_xboole_0(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t90_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_28,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k2_relat_1(k7_relat_1(B_14,A_13)) = k9_relat_1(B_14,A_13)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( v1_relat_1(k7_relat_1(A_4,B_5))
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_26,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_16,plain,(
    ! [A_15] : k1_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_4,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_76,plain,(
    ! [B_33,A_34] :
      ( k5_relat_1(B_33,k6_relat_1(A_34)) = k8_relat_1(A_34,B_33)
      | ~ v1_relat_1(B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( k5_relat_1(k6_relat_1(A_18),B_19) = k7_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_83,plain,(
    ! [A_34,A_18] :
      ( k8_relat_1(A_34,k6_relat_1(A_18)) = k7_relat_1(k6_relat_1(A_34),A_18)
      | ~ v1_relat_1(k6_relat_1(A_34))
      | ~ v1_relat_1(k6_relat_1(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_22])).

tff(c_93,plain,(
    ! [A_34,A_18] : k8_relat_1(A_34,k6_relat_1(A_18)) = k7_relat_1(k6_relat_1(A_34),A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_4,c_83])).

tff(c_18,plain,(
    ! [A_15] : k2_relat_1(k6_relat_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_37,B_38] :
      ( k8_relat_1(A_37,B_38) = B_38
      | ~ r1_tarski(k2_relat_1(B_38),A_37)
      | ~ v1_relat_1(B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [A_37,A_15] :
      ( k8_relat_1(A_37,k6_relat_1(A_15)) = k6_relat_1(A_15)
      | ~ r1_tarski(A_15,A_37)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_115,plain,(
    ! [A_37,A_15] :
      ( k7_relat_1(k6_relat_1(A_37),A_15) = k6_relat_1(A_15)
      | ~ r1_tarski(A_15,A_37) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_93,c_113])).

tff(c_135,plain,(
    ! [B_41,A_42] :
      ( k3_xboole_0(k1_relat_1(B_41),A_42) = k1_relat_1(k7_relat_1(B_41,A_42))
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    ! [A_15,A_42] :
      ( k1_relat_1(k7_relat_1(k6_relat_1(A_15),A_42)) = k3_xboole_0(A_15,A_42)
      | ~ v1_relat_1(k6_relat_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_135])).

tff(c_149,plain,(
    ! [A_43,A_44] : k1_relat_1(k7_relat_1(k6_relat_1(A_43),A_44)) = k3_xboole_0(A_43,A_44) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_144])).

tff(c_161,plain,(
    ! [A_37,A_15] :
      ( k3_xboole_0(A_37,A_15) = k1_relat_1(k6_relat_1(A_15))
      | ~ r1_tarski(A_15,A_37) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_149])).

tff(c_165,plain,(
    ! [A_45,A_46] :
      ( k3_xboole_0(A_45,A_46) = A_46
      | ~ r1_tarski(A_46,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_161])).

tff(c_169,plain,(
    k3_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_165])).

tff(c_174,plain,(
    ! [C_47,A_48,B_49] :
      ( k7_relat_1(k7_relat_1(C_47,A_48),B_49) = k7_relat_1(C_47,k3_xboole_0(A_48,B_49))
      | ~ v1_relat_1(C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_297,plain,(
    ! [C_62,A_63,B_64] :
      ( k2_relat_1(k7_relat_1(C_62,k3_xboole_0(A_63,B_64))) = k9_relat_1(k7_relat_1(C_62,A_63),B_64)
      | ~ v1_relat_1(k7_relat_1(C_62,A_63))
      | ~ v1_relat_1(C_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_14])).

tff(c_423,plain,(
    ! [C_68] :
      ( k9_relat_1(k7_relat_1(C_68,'#skF_3'),'#skF_2') = k2_relat_1(k7_relat_1(C_68,'#skF_2'))
      | ~ v1_relat_1(k7_relat_1(C_68,'#skF_3'))
      | ~ v1_relat_1(C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_169,c_297])).

tff(c_529,plain,(
    ! [A_71] :
      ( k9_relat_1(k7_relat_1(A_71,'#skF_3'),'#skF_2') = k2_relat_1(k7_relat_1(A_71,'#skF_2'))
      | ~ v1_relat_1(A_71) ) ),
    inference(resolution,[status(thm)],[c_6,c_423])).

tff(c_24,plain,(
    k9_relat_1(k7_relat_1('#skF_1','#skF_3'),'#skF_2') != k9_relat_1('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_538,plain,
    ( k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2')
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_529,c_24])).

tff(c_558,plain,(
    k2_relat_1(k7_relat_1('#skF_1','#skF_2')) != k9_relat_1('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_538])).

tff(c_586,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_558])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_586])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 14:12:56 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.42/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  
% 2.42/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.33  %$ r1_tarski > v1_relat_1 > k9_relat_1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.42/1.33  
% 2.42/1.33  %Foreground sorts:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Background operators:
% 2.42/1.33  
% 2.42/1.33  
% 2.42/1.33  %Foreground operators:
% 2.42/1.33  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.42/1.33  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.42/1.33  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.42/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.42/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.42/1.33  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.42/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.42/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.42/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.42/1.33  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.42/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.42/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.42/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.42/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.42/1.33  
% 2.42/1.35  tff(f_71, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B, C]: (r1_tarski(B, C) => (k9_relat_1(k7_relat_1(A, C), B) = k9_relat_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_relat_1)).
% 2.42/1.35  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.42/1.35  tff(f_33, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.42/1.35  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.42/1.35  tff(f_29, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.42/1.35  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t123_relat_1)).
% 2.42/1.35  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 2.42/1.35  tff(f_47, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.42/1.35  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k1_relat_1(k7_relat_1(B, A)) = k3_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t90_relat_1)).
% 2.42/1.35  tff(f_37, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 2.42/1.35  tff(c_28, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.42/1.35  tff(c_14, plain, (![B_14, A_13]: (k2_relat_1(k7_relat_1(B_14, A_13))=k9_relat_1(B_14, A_13) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.42/1.35  tff(c_6, plain, (![A_4, B_5]: (v1_relat_1(k7_relat_1(A_4, B_5)) | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.42/1.35  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.42/1.35  tff(c_16, plain, (![A_15]: (k1_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.42/1.35  tff(c_4, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.42/1.35  tff(c_76, plain, (![B_33, A_34]: (k5_relat_1(B_33, k6_relat_1(A_34))=k8_relat_1(A_34, B_33) | ~v1_relat_1(B_33))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.42/1.35  tff(c_22, plain, (![A_18, B_19]: (k5_relat_1(k6_relat_1(A_18), B_19)=k7_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.42/1.35  tff(c_83, plain, (![A_34, A_18]: (k8_relat_1(A_34, k6_relat_1(A_18))=k7_relat_1(k6_relat_1(A_34), A_18) | ~v1_relat_1(k6_relat_1(A_34)) | ~v1_relat_1(k6_relat_1(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_22])).
% 2.42/1.35  tff(c_93, plain, (![A_34, A_18]: (k8_relat_1(A_34, k6_relat_1(A_18))=k7_relat_1(k6_relat_1(A_34), A_18))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_4, c_83])).
% 2.42/1.35  tff(c_18, plain, (![A_15]: (k2_relat_1(k6_relat_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.42/1.35  tff(c_107, plain, (![A_37, B_38]: (k8_relat_1(A_37, B_38)=B_38 | ~r1_tarski(k2_relat_1(B_38), A_37) | ~v1_relat_1(B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.42/1.35  tff(c_113, plain, (![A_37, A_15]: (k8_relat_1(A_37, k6_relat_1(A_15))=k6_relat_1(A_15) | ~r1_tarski(A_15, A_37) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_107])).
% 2.42/1.35  tff(c_115, plain, (![A_37, A_15]: (k7_relat_1(k6_relat_1(A_37), A_15)=k6_relat_1(A_15) | ~r1_tarski(A_15, A_37))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_93, c_113])).
% 2.42/1.35  tff(c_135, plain, (![B_41, A_42]: (k3_xboole_0(k1_relat_1(B_41), A_42)=k1_relat_1(k7_relat_1(B_41, A_42)) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.42/1.35  tff(c_144, plain, (![A_15, A_42]: (k1_relat_1(k7_relat_1(k6_relat_1(A_15), A_42))=k3_xboole_0(A_15, A_42) | ~v1_relat_1(k6_relat_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_135])).
% 2.42/1.35  tff(c_149, plain, (![A_43, A_44]: (k1_relat_1(k7_relat_1(k6_relat_1(A_43), A_44))=k3_xboole_0(A_43, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_144])).
% 2.42/1.35  tff(c_161, plain, (![A_37, A_15]: (k3_xboole_0(A_37, A_15)=k1_relat_1(k6_relat_1(A_15)) | ~r1_tarski(A_15, A_37))), inference(superposition, [status(thm), theory('equality')], [c_115, c_149])).
% 2.42/1.35  tff(c_165, plain, (![A_45, A_46]: (k3_xboole_0(A_45, A_46)=A_46 | ~r1_tarski(A_46, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_161])).
% 2.42/1.35  tff(c_169, plain, (k3_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_26, c_165])).
% 2.42/1.35  tff(c_174, plain, (![C_47, A_48, B_49]: (k7_relat_1(k7_relat_1(C_47, A_48), B_49)=k7_relat_1(C_47, k3_xboole_0(A_48, B_49)) | ~v1_relat_1(C_47))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.42/1.35  tff(c_297, plain, (![C_62, A_63, B_64]: (k2_relat_1(k7_relat_1(C_62, k3_xboole_0(A_63, B_64)))=k9_relat_1(k7_relat_1(C_62, A_63), B_64) | ~v1_relat_1(k7_relat_1(C_62, A_63)) | ~v1_relat_1(C_62))), inference(superposition, [status(thm), theory('equality')], [c_174, c_14])).
% 2.42/1.35  tff(c_423, plain, (![C_68]: (k9_relat_1(k7_relat_1(C_68, '#skF_3'), '#skF_2')=k2_relat_1(k7_relat_1(C_68, '#skF_2')) | ~v1_relat_1(k7_relat_1(C_68, '#skF_3')) | ~v1_relat_1(C_68))), inference(superposition, [status(thm), theory('equality')], [c_169, c_297])).
% 2.42/1.35  tff(c_529, plain, (![A_71]: (k9_relat_1(k7_relat_1(A_71, '#skF_3'), '#skF_2')=k2_relat_1(k7_relat_1(A_71, '#skF_2')) | ~v1_relat_1(A_71))), inference(resolution, [status(thm)], [c_6, c_423])).
% 2.42/1.35  tff(c_24, plain, (k9_relat_1(k7_relat_1('#skF_1', '#skF_3'), '#skF_2')!=k9_relat_1('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.42/1.35  tff(c_538, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2') | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_529, c_24])).
% 2.42/1.35  tff(c_558, plain, (k2_relat_1(k7_relat_1('#skF_1', '#skF_2'))!=k9_relat_1('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_538])).
% 2.42/1.35  tff(c_586, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_14, c_558])).
% 2.42/1.35  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_586])).
% 2.42/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.42/1.35  
% 2.42/1.35  Inference rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Ref     : 0
% 2.42/1.35  #Sup     : 131
% 2.42/1.35  #Fact    : 0
% 2.42/1.35  #Define  : 0
% 2.42/1.35  #Split   : 0
% 2.42/1.35  #Chain   : 0
% 2.42/1.35  #Close   : 0
% 2.42/1.35  
% 2.42/1.35  Ordering : KBO
% 2.42/1.35  
% 2.42/1.35  Simplification rules
% 2.42/1.35  ----------------------
% 2.42/1.35  #Subsume      : 13
% 2.42/1.35  #Demod        : 55
% 2.42/1.35  #Tautology    : 55
% 2.42/1.35  #SimpNegUnit  : 0
% 2.42/1.35  #BackRed      : 0
% 2.42/1.35  
% 2.42/1.35  #Partial instantiations: 0
% 2.42/1.35  #Strategies tried      : 1
% 2.42/1.35  
% 2.42/1.35  Timing (in seconds)
% 2.42/1.35  ----------------------
% 2.42/1.35  Preprocessing        : 0.29
% 2.42/1.35  Parsing              : 0.16
% 2.42/1.35  CNF conversion       : 0.02
% 2.42/1.35  Main loop            : 0.26
% 2.42/1.35  Inferencing          : 0.11
% 2.42/1.35  Reduction            : 0.08
% 2.42/1.35  Demodulation         : 0.06
% 2.42/1.35  BG Simplification    : 0.02
% 2.42/1.35  Subsumption          : 0.04
% 2.42/1.35  Abstraction          : 0.02
% 2.42/1.35  MUC search           : 0.00
% 2.42/1.35  Cooper               : 0.00
% 2.42/1.35  Total                : 0.58
% 2.42/1.35  Index Insertion      : 0.00
% 2.42/1.35  Index Deletion       : 0.00
% 2.42/1.35  Index Matching       : 0.00
% 2.42/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
