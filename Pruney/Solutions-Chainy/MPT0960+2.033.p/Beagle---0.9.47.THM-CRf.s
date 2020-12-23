%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:41 EST 2020

% Result     : Theorem 2.49s
% Output     : CNFRefutation 2.77s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 103 expanded)
%              Number of leaves         :   31 (  47 expanded)
%              Depth                    :   11
%              Number of atoms          :   65 ( 109 expanded)
%              Number of equality atoms :   38 (  68 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_58,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_37,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_26,plain,(
    ! [A_21] : v1_relat_1(k1_wellord2(A_21)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_184,plain,(
    ! [A_45,B_46] : k2_xboole_0(k3_xboole_0(A_45,B_46),k4_xboole_0(A_45,B_46)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [A_47] : k2_xboole_0(k1_xboole_0,k4_xboole_0(A_47,k1_xboole_0)) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_184])).

tff(c_12,plain,(
    ! [A_8] : r1_tarski(k1_xboole_0,A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [A_32,B_33] :
      ( k2_xboole_0(A_32,B_33) = B_33
      | ~ r1_tarski(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_80,plain,(
    ! [A_8] : k2_xboole_0(k1_xboole_0,A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_72])).

tff(c_245,plain,(
    ! [A_48] : k4_xboole_0(A_48,k1_xboole_0) = A_48 ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_80])).

tff(c_14,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_254,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k3_xboole_0(A_48,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_245,c_14])).

tff(c_268,plain,(
    ! [A_48] : k4_xboole_0(A_48,A_48) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_254])).

tff(c_228,plain,(
    ! [A_47] : k4_xboole_0(A_47,k1_xboole_0) = A_47 ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_80])).

tff(c_292,plain,(
    ! [A_52] : k4_xboole_0(A_52,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_254])).

tff(c_304,plain,(
    ! [A_52] : k4_xboole_0(A_52,k1_xboole_0) = k3_xboole_0(A_52,A_52) ),
    inference(superposition,[status(thm),theory(equality)],[c_292,c_14])).

tff(c_324,plain,(
    ! [A_53] : k3_xboole_0(A_53,A_53) = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_228,c_304])).

tff(c_6,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_337,plain,(
    ! [A_53] : k5_xboole_0(A_53,A_53) = k4_xboole_0(A_53,A_53) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_6])).

tff(c_356,plain,(
    ! [A_53] : k5_xboole_0(A_53,A_53) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_268,c_337])).

tff(c_18,plain,(
    ! [A_13] : r1_tarski(A_13,k1_zfmisc_1(k3_tarski(A_13))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    ! [B_23,A_22] :
      ( k2_wellord1(k1_wellord2(B_23),A_22) = k1_wellord2(A_22)
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_430,plain,(
    ! [B_58,A_59] :
      ( k2_wellord1(k2_wellord1(B_58,A_59),A_59) = k2_wellord1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_445,plain,(
    ! [B_23,A_22] :
      ( k2_wellord1(k1_wellord2(B_23),A_22) = k2_wellord1(k1_wellord2(A_22),A_22)
      | ~ v1_relat_1(k1_wellord2(B_23))
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_430])).

tff(c_654,plain,(
    ! [B_69,A_70] :
      ( k2_wellord1(k1_wellord2(B_69),A_70) = k2_wellord1(k1_wellord2(A_70),A_70)
      | ~ r1_tarski(A_70,B_69) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_445])).

tff(c_986,plain,(
    ! [A_81,B_82] :
      ( k2_wellord1(k1_wellord2(A_81),A_81) = k1_wellord2(A_81)
      | ~ r1_tarski(A_81,B_82)
      | ~ r1_tarski(A_81,B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_654])).

tff(c_990,plain,(
    ! [A_13] :
      ( k2_wellord1(k1_wellord2(A_13),A_13) = k1_wellord2(A_13)
      | ~ r1_tarski(A_13,k1_zfmisc_1(k3_tarski(A_13))) ) ),
    inference(resolution,[status(thm)],[c_18,c_986])).

tff(c_1002,plain,(
    ! [A_83] : k2_wellord1(k1_wellord2(A_83),A_83) = k1_wellord2(A_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_990])).

tff(c_380,plain,(
    ! [A_55,B_56] :
      ( k3_xboole_0(A_55,k2_zfmisc_1(B_56,B_56)) = k2_wellord1(A_55,B_56)
      | ~ v1_relat_1(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_397,plain,(
    ! [A_55,B_56] :
      ( k5_xboole_0(A_55,k2_wellord1(A_55,B_56)) = k4_xboole_0(A_55,k2_zfmisc_1(B_56,B_56))
      | ~ v1_relat_1(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_6])).

tff(c_1008,plain,(
    ! [A_83] :
      ( k5_xboole_0(k1_wellord2(A_83),k1_wellord2(A_83)) = k4_xboole_0(k1_wellord2(A_83),k2_zfmisc_1(A_83,A_83))
      | ~ v1_relat_1(k1_wellord2(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1002,c_397])).

tff(c_1027,plain,(
    ! [A_83] : k4_xboole_0(k1_wellord2(A_83),k2_zfmisc_1(A_83,A_83)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_356,c_1008])).

tff(c_81,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(A_34,B_35)
      | k4_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_93,plain,(
    k4_xboole_0(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_81,c_30])).

tff(c_1039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1027,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:13:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.49/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.38  
% 2.49/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.49/1.38  %$ r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_1
% 2.49/1.38  
% 2.49/1.38  %Foreground sorts:
% 2.49/1.38  
% 2.49/1.38  
% 2.49/1.38  %Background operators:
% 2.49/1.38  
% 2.49/1.38  
% 2.49/1.38  %Foreground operators:
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.49/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.49/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.49/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.49/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.49/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.49/1.38  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.49/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.49/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.49/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.49/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.49/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.49/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.49/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.49/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.49/1.38  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.49/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.49/1.38  
% 2.77/1.39  tff(f_58, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.77/1.39  tff(f_37, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.77/1.39  tff(f_43, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.77/1.39  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.77/1.39  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.77/1.39  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.77/1.39  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.77/1.39  tff(f_45, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.77/1.39  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord2)).
% 2.77/1.39  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_wellord1)).
% 2.77/1.39  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_wellord1)).
% 2.77/1.39  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.77/1.39  tff(f_65, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_wellord2)).
% 2.77/1.39  tff(c_26, plain, (![A_21]: (v1_relat_1(k1_wellord2(A_21)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.77/1.39  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.77/1.39  tff(c_184, plain, (![A_45, B_46]: (k2_xboole_0(k3_xboole_0(A_45, B_46), k4_xboole_0(A_45, B_46))=A_45)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.77/1.39  tff(c_222, plain, (![A_47]: (k2_xboole_0(k1_xboole_0, k4_xboole_0(A_47, k1_xboole_0))=A_47)), inference(superposition, [status(thm), theory('equality')], [c_10, c_184])).
% 2.77/1.39  tff(c_12, plain, (![A_8]: (r1_tarski(k1_xboole_0, A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.77/1.39  tff(c_72, plain, (![A_32, B_33]: (k2_xboole_0(A_32, B_33)=B_33 | ~r1_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.77/1.39  tff(c_80, plain, (![A_8]: (k2_xboole_0(k1_xboole_0, A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_72])).
% 2.77/1.39  tff(c_245, plain, (![A_48]: (k4_xboole_0(A_48, k1_xboole_0)=A_48)), inference(superposition, [status(thm), theory('equality')], [c_222, c_80])).
% 2.77/1.39  tff(c_14, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.77/1.39  tff(c_254, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k3_xboole_0(A_48, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_245, c_14])).
% 2.77/1.39  tff(c_268, plain, (![A_48]: (k4_xboole_0(A_48, A_48)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_254])).
% 2.77/1.39  tff(c_228, plain, (![A_47]: (k4_xboole_0(A_47, k1_xboole_0)=A_47)), inference(superposition, [status(thm), theory('equality')], [c_222, c_80])).
% 2.77/1.39  tff(c_292, plain, (![A_52]: (k4_xboole_0(A_52, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_254])).
% 2.77/1.39  tff(c_304, plain, (![A_52]: (k4_xboole_0(A_52, k1_xboole_0)=k3_xboole_0(A_52, A_52))), inference(superposition, [status(thm), theory('equality')], [c_292, c_14])).
% 2.77/1.39  tff(c_324, plain, (![A_53]: (k3_xboole_0(A_53, A_53)=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_228, c_304])).
% 2.77/1.40  tff(c_6, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.77/1.40  tff(c_337, plain, (![A_53]: (k5_xboole_0(A_53, A_53)=k4_xboole_0(A_53, A_53))), inference(superposition, [status(thm), theory('equality')], [c_324, c_6])).
% 2.77/1.40  tff(c_356, plain, (![A_53]: (k5_xboole_0(A_53, A_53)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_268, c_337])).
% 2.77/1.40  tff(c_18, plain, (![A_13]: (r1_tarski(A_13, k1_zfmisc_1(k3_tarski(A_13))))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.77/1.40  tff(c_28, plain, (![B_23, A_22]: (k2_wellord1(k1_wellord2(B_23), A_22)=k1_wellord2(A_22) | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.77/1.40  tff(c_430, plain, (![B_58, A_59]: (k2_wellord1(k2_wellord1(B_58, A_59), A_59)=k2_wellord1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.77/1.40  tff(c_445, plain, (![B_23, A_22]: (k2_wellord1(k1_wellord2(B_23), A_22)=k2_wellord1(k1_wellord2(A_22), A_22) | ~v1_relat_1(k1_wellord2(B_23)) | ~r1_tarski(A_22, B_23))), inference(superposition, [status(thm), theory('equality')], [c_28, c_430])).
% 2.77/1.40  tff(c_654, plain, (![B_69, A_70]: (k2_wellord1(k1_wellord2(B_69), A_70)=k2_wellord1(k1_wellord2(A_70), A_70) | ~r1_tarski(A_70, B_69))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_445])).
% 2.77/1.40  tff(c_986, plain, (![A_81, B_82]: (k2_wellord1(k1_wellord2(A_81), A_81)=k1_wellord2(A_81) | ~r1_tarski(A_81, B_82) | ~r1_tarski(A_81, B_82))), inference(superposition, [status(thm), theory('equality')], [c_28, c_654])).
% 2.77/1.40  tff(c_990, plain, (![A_13]: (k2_wellord1(k1_wellord2(A_13), A_13)=k1_wellord2(A_13) | ~r1_tarski(A_13, k1_zfmisc_1(k3_tarski(A_13))))), inference(resolution, [status(thm)], [c_18, c_986])).
% 2.77/1.40  tff(c_1002, plain, (![A_83]: (k2_wellord1(k1_wellord2(A_83), A_83)=k1_wellord2(A_83))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_990])).
% 2.77/1.40  tff(c_380, plain, (![A_55, B_56]: (k3_xboole_0(A_55, k2_zfmisc_1(B_56, B_56))=k2_wellord1(A_55, B_56) | ~v1_relat_1(A_55))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.77/1.40  tff(c_397, plain, (![A_55, B_56]: (k5_xboole_0(A_55, k2_wellord1(A_55, B_56))=k4_xboole_0(A_55, k2_zfmisc_1(B_56, B_56)) | ~v1_relat_1(A_55))), inference(superposition, [status(thm), theory('equality')], [c_380, c_6])).
% 2.77/1.40  tff(c_1008, plain, (![A_83]: (k5_xboole_0(k1_wellord2(A_83), k1_wellord2(A_83))=k4_xboole_0(k1_wellord2(A_83), k2_zfmisc_1(A_83, A_83)) | ~v1_relat_1(k1_wellord2(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_1002, c_397])).
% 2.77/1.40  tff(c_1027, plain, (![A_83]: (k4_xboole_0(k1_wellord2(A_83), k2_zfmisc_1(A_83, A_83))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_356, c_1008])).
% 2.77/1.40  tff(c_81, plain, (![A_34, B_35]: (r1_tarski(A_34, B_35) | k4_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.77/1.40  tff(c_30, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.77/1.40  tff(c_93, plain, (k4_xboole_0(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_81, c_30])).
% 2.77/1.40  tff(c_1039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1027, c_93])).
% 2.77/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.77/1.40  
% 2.77/1.40  Inference rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Ref     : 0
% 2.77/1.40  #Sup     : 239
% 2.77/1.40  #Fact    : 0
% 2.77/1.40  #Define  : 0
% 2.77/1.40  #Split   : 1
% 2.77/1.40  #Chain   : 0
% 2.77/1.40  #Close   : 0
% 2.77/1.40  
% 2.77/1.40  Ordering : KBO
% 2.77/1.40  
% 2.77/1.40  Simplification rules
% 2.77/1.40  ----------------------
% 2.77/1.40  #Subsume      : 7
% 2.77/1.40  #Demod        : 189
% 2.77/1.40  #Tautology    : 163
% 2.77/1.40  #SimpNegUnit  : 0
% 2.77/1.40  #BackRed      : 4
% 2.77/1.40  
% 2.77/1.40  #Partial instantiations: 0
% 2.77/1.40  #Strategies tried      : 1
% 2.77/1.40  
% 2.77/1.40  Timing (in seconds)
% 2.77/1.40  ----------------------
% 2.77/1.40  Preprocessing        : 0.28
% 2.77/1.40  Parsing              : 0.16
% 2.77/1.40  CNF conversion       : 0.02
% 2.77/1.40  Main loop            : 0.34
% 2.77/1.40  Inferencing          : 0.14
% 2.77/1.40  Reduction            : 0.11
% 2.77/1.40  Demodulation         : 0.09
% 2.77/1.40  BG Simplification    : 0.02
% 2.77/1.40  Subsumption          : 0.05
% 2.77/1.40  Abstraction          : 0.02
% 2.77/1.40  MUC search           : 0.00
% 2.77/1.40  Cooper               : 0.00
% 2.77/1.40  Total                : 0.65
% 2.77/1.40  Index Insertion      : 0.00
% 2.77/1.40  Index Deletion       : 0.00
% 2.77/1.40  Index Matching       : 0.00
% 2.77/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------
