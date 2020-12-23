%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   52 (  60 expanded)
%              Number of leaves         :   27 (  32 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  65 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_1

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

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_54,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_24,plain,(
    ! [A_17] : v1_relat_1(k1_wellord2(A_17)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_56,plain,(
    ! [A_28,B_29] :
      ( k4_xboole_0(A_28,B_29) = k1_xboole_0
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_56])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_83,plain,(
    ! [A_32,B_33] : k5_xboole_0(A_32,k3_xboole_0(A_32,B_33)) = k4_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_83])).

tff(c_95,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_92])).

tff(c_16,plain,(
    ! [A_9] : r1_tarski(A_9,k1_zfmisc_1(k3_tarski(A_9))) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [B_19,A_18] :
      ( k2_wellord1(k1_wellord2(B_19),A_18) = k1_wellord2(A_18)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_167,plain,(
    ! [B_44,A_45] :
      ( k2_wellord1(k2_wellord1(B_44,A_45),A_45) = k2_wellord1(B_44,A_45)
      | ~ v1_relat_1(B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_182,plain,(
    ! [B_19,A_18] :
      ( k2_wellord1(k1_wellord2(B_19),A_18) = k2_wellord1(k1_wellord2(A_18),A_18)
      | ~ v1_relat_1(k1_wellord2(B_19))
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_167])).

tff(c_200,plain,(
    ! [B_49,A_50] :
      ( k2_wellord1(k1_wellord2(B_49),A_50) = k2_wellord1(k1_wellord2(A_50),A_50)
      | ~ r1_tarski(A_50,B_49) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_182])).

tff(c_281,plain,(
    ! [A_54,B_55] :
      ( k2_wellord1(k1_wellord2(A_54),A_54) = k1_wellord2(A_54)
      | ~ r1_tarski(A_54,B_55)
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_26])).

tff(c_285,plain,(
    ! [A_9] :
      ( k2_wellord1(k1_wellord2(A_9),A_9) = k1_wellord2(A_9)
      | ~ r1_tarski(A_9,k1_zfmisc_1(k3_tarski(A_9))) ) ),
    inference(resolution,[status(thm)],[c_16,c_281])).

tff(c_297,plain,(
    ! [A_56] : k2_wellord1(k1_wellord2(A_56),A_56) = k1_wellord2(A_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_285])).

tff(c_125,plain,(
    ! [A_39,B_40] :
      ( k3_xboole_0(A_39,k2_zfmisc_1(B_40,B_40)) = k2_wellord1(A_39,B_40)
      | ~ v1_relat_1(A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_131,plain,(
    ! [A_39,B_40] :
      ( k5_xboole_0(A_39,k2_wellord1(A_39,B_40)) = k4_xboole_0(A_39,k2_zfmisc_1(B_40,B_40))
      | ~ v1_relat_1(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_14])).

tff(c_303,plain,(
    ! [A_56] :
      ( k5_xboole_0(k1_wellord2(A_56),k1_wellord2(A_56)) = k4_xboole_0(k1_wellord2(A_56),k2_zfmisc_1(A_56,A_56))
      | ~ v1_relat_1(k1_wellord2(A_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_297,c_131])).

tff(c_319,plain,(
    ! [A_56] : k4_xboole_0(k1_wellord2(A_56),k2_zfmisc_1(A_56,A_56)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_95,c_303])).

tff(c_51,plain,(
    ! [A_26,B_27] :
      ( r1_tarski(A_26,B_27)
      | k4_xboole_0(A_26,B_27) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_55,plain,(
    k4_xboole_0(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_51,c_28])).

tff(c_333,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_55])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:02:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.37  
% 2.13/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.38  %$ r1_tarski > v1_relat_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_1
% 2.13/1.38  
% 2.13/1.38  %Foreground sorts:
% 2.13/1.38  
% 2.13/1.38  
% 2.13/1.38  %Background operators:
% 2.13/1.38  
% 2.13/1.38  
% 2.13/1.38  %Foreground operators:
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.38  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.13/1.38  tff('#skF_1', type, '#skF_1': $i).
% 2.13/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.38  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.38  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.38  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.38  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.13/1.38  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.38  
% 2.30/1.40  tff(f_54, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.30/1.40  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.40  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.30/1.40  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.30/1.40  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.30/1.40  tff(f_41, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.30/1.40  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.30/1.40  tff(f_52, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_wellord1)).
% 2.30/1.40  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 2.30/1.40  tff(f_61, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.30/1.40  tff(c_24, plain, (![A_17]: (v1_relat_1(k1_wellord2(A_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.30/1.40  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.30/1.40  tff(c_56, plain, (![A_28, B_29]: (k4_xboole_0(A_28, B_29)=k1_xboole_0 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.40  tff(c_68, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_56])).
% 2.30/1.40  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.40  tff(c_83, plain, (![A_32, B_33]: (k5_xboole_0(A_32, k3_xboole_0(A_32, B_33))=k4_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.40  tff(c_92, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_83])).
% 2.30/1.40  tff(c_95, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_68, c_92])).
% 2.30/1.40  tff(c_16, plain, (![A_9]: (r1_tarski(A_9, k1_zfmisc_1(k3_tarski(A_9))))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.30/1.40  tff(c_26, plain, (![B_19, A_18]: (k2_wellord1(k1_wellord2(B_19), A_18)=k1_wellord2(A_18) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.40  tff(c_167, plain, (![B_44, A_45]: (k2_wellord1(k2_wellord1(B_44, A_45), A_45)=k2_wellord1(B_44, A_45) | ~v1_relat_1(B_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.30/1.40  tff(c_182, plain, (![B_19, A_18]: (k2_wellord1(k1_wellord2(B_19), A_18)=k2_wellord1(k1_wellord2(A_18), A_18) | ~v1_relat_1(k1_wellord2(B_19)) | ~r1_tarski(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_26, c_167])).
% 2.30/1.40  tff(c_200, plain, (![B_49, A_50]: (k2_wellord1(k1_wellord2(B_49), A_50)=k2_wellord1(k1_wellord2(A_50), A_50) | ~r1_tarski(A_50, B_49))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_182])).
% 2.30/1.40  tff(c_281, plain, (![A_54, B_55]: (k2_wellord1(k1_wellord2(A_54), A_54)=k1_wellord2(A_54) | ~r1_tarski(A_54, B_55) | ~r1_tarski(A_54, B_55))), inference(superposition, [status(thm), theory('equality')], [c_200, c_26])).
% 2.30/1.40  tff(c_285, plain, (![A_9]: (k2_wellord1(k1_wellord2(A_9), A_9)=k1_wellord2(A_9) | ~r1_tarski(A_9, k1_zfmisc_1(k3_tarski(A_9))))), inference(resolution, [status(thm)], [c_16, c_281])).
% 2.30/1.40  tff(c_297, plain, (![A_56]: (k2_wellord1(k1_wellord2(A_56), A_56)=k1_wellord2(A_56))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_285])).
% 2.30/1.40  tff(c_125, plain, (![A_39, B_40]: (k3_xboole_0(A_39, k2_zfmisc_1(B_40, B_40))=k2_wellord1(A_39, B_40) | ~v1_relat_1(A_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.30/1.40  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.40  tff(c_131, plain, (![A_39, B_40]: (k5_xboole_0(A_39, k2_wellord1(A_39, B_40))=k4_xboole_0(A_39, k2_zfmisc_1(B_40, B_40)) | ~v1_relat_1(A_39))), inference(superposition, [status(thm), theory('equality')], [c_125, c_14])).
% 2.30/1.40  tff(c_303, plain, (![A_56]: (k5_xboole_0(k1_wellord2(A_56), k1_wellord2(A_56))=k4_xboole_0(k1_wellord2(A_56), k2_zfmisc_1(A_56, A_56)) | ~v1_relat_1(k1_wellord2(A_56)))), inference(superposition, [status(thm), theory('equality')], [c_297, c_131])).
% 2.30/1.40  tff(c_319, plain, (![A_56]: (k4_xboole_0(k1_wellord2(A_56), k2_zfmisc_1(A_56, A_56))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_95, c_303])).
% 2.30/1.40  tff(c_51, plain, (![A_26, B_27]: (r1_tarski(A_26, B_27) | k4_xboole_0(A_26, B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.40  tff(c_28, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.30/1.40  tff(c_55, plain, (k4_xboole_0(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_51, c_28])).
% 2.30/1.40  tff(c_333, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_319, c_55])).
% 2.30/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.40  
% 2.30/1.40  Inference rules
% 2.30/1.40  ----------------------
% 2.30/1.40  #Ref     : 0
% 2.30/1.40  #Sup     : 66
% 2.30/1.40  #Fact    : 0
% 2.30/1.40  #Define  : 0
% 2.30/1.40  #Split   : 0
% 2.30/1.40  #Chain   : 0
% 2.30/1.40  #Close   : 0
% 2.30/1.40  
% 2.30/1.40  Ordering : KBO
% 2.30/1.40  
% 2.30/1.40  Simplification rules
% 2.30/1.40  ----------------------
% 2.30/1.40  #Subsume      : 6
% 2.30/1.40  #Demod        : 28
% 2.30/1.40  #Tautology    : 39
% 2.30/1.40  #SimpNegUnit  : 0
% 2.30/1.40  #BackRed      : 2
% 2.30/1.40  
% 2.30/1.40  #Partial instantiations: 0
% 2.30/1.40  #Strategies tried      : 1
% 2.30/1.40  
% 2.30/1.40  Timing (in seconds)
% 2.30/1.40  ----------------------
% 2.30/1.40  Preprocessing        : 0.33
% 2.30/1.40  Parsing              : 0.17
% 2.30/1.40  CNF conversion       : 0.03
% 2.30/1.40  Main loop            : 0.25
% 2.30/1.40  Inferencing          : 0.10
% 2.30/1.40  Reduction            : 0.07
% 2.30/1.40  Demodulation         : 0.05
% 2.30/1.41  BG Simplification    : 0.02
% 2.30/1.41  Subsumption          : 0.05
% 2.30/1.41  Abstraction          : 0.01
% 2.30/1.41  MUC search           : 0.00
% 2.30/1.41  Cooper               : 0.00
% 2.30/1.41  Total                : 0.63
% 2.30/1.41  Index Insertion      : 0.00
% 2.30/1.41  Index Deletion       : 0.00
% 2.30/1.41  Index Matching       : 0.00
% 2.30/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
