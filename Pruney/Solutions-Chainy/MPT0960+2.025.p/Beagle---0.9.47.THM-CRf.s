%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:40 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   53 (  61 expanded)
%              Number of leaves         :   28 (  33 expanded)
%              Depth                    :    9
%              Number of atoms          :   54 (  65 expanded)
%              Number of equality atoms :   27 (  31 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_wellord1(k2_wellord1(B,A),A) = k2_wellord1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_wellord1)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_28,plain,(
    ! [A_22] : v1_relat_1(k1_wellord2(A_22)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [A_34,B_35] :
      ( k4_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_72,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_64])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_118,plain,(
    ! [A_45,B_46] : k5_xboole_0(A_45,k3_xboole_0(A_45,B_46)) = k4_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_127,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_118])).

tff(c_130,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_127])).

tff(c_16,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( k2_wellord1(k1_wellord2(B_24),A_23) = k1_wellord2(A_23)
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_169,plain,(
    ! [B_54,A_55] :
      ( k2_wellord1(k2_wellord1(B_54,A_55),A_55) = k2_wellord1(B_54,A_55)
      | ~ v1_relat_1(B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_184,plain,(
    ! [B_24,A_23] :
      ( k2_wellord1(k1_wellord2(B_24),A_23) = k2_wellord1(k1_wellord2(A_23),A_23)
      | ~ v1_relat_1(k1_wellord2(B_24))
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_169])).

tff(c_222,plain,(
    ! [B_62,A_63] :
      ( k2_wellord1(k1_wellord2(B_62),A_63) = k2_wellord1(k1_wellord2(A_63),A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_184])).

tff(c_303,plain,(
    ! [A_67,B_68] :
      ( k2_wellord1(k1_wellord2(A_67),A_67) = k1_wellord2(A_67)
      | ~ r1_tarski(A_67,B_68)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_222])).

tff(c_307,plain,(
    ! [A_9,B_10] :
      ( k2_wellord1(k1_wellord2(A_9),A_9) = k1_wellord2(A_9)
      | ~ r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ) ),
    inference(resolution,[status(thm)],[c_16,c_303])).

tff(c_319,plain,(
    ! [A_69] : k2_wellord1(k1_wellord2(A_69),A_69) = k1_wellord2(A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_307])).

tff(c_191,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,k2_zfmisc_1(B_57,B_57)) = k2_wellord1(A_56,B_57)
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_197,plain,(
    ! [A_56,B_57] :
      ( k5_xboole_0(A_56,k2_wellord1(A_56,B_57)) = k4_xboole_0(A_56,k2_zfmisc_1(B_57,B_57))
      | ~ v1_relat_1(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_191,c_14])).

tff(c_325,plain,(
    ! [A_69] :
      ( k5_xboole_0(k1_wellord2(A_69),k1_wellord2(A_69)) = k4_xboole_0(k1_wellord2(A_69),k2_zfmisc_1(A_69,A_69))
      | ~ v1_relat_1(k1_wellord2(A_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_319,c_197])).

tff(c_341,plain,(
    ! [A_69] : k4_xboole_0(k1_wellord2(A_69),k2_zfmisc_1(A_69,A_69)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_130,c_325])).

tff(c_96,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(A_41,B_42)
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_32,plain,(
    ~ r1_tarski(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_104,plain,(
    k4_xboole_0(k1_wellord2('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_96,c_32])).

tff(c_354,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_341,c_104])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:01:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.22  
% 2.09/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.22  %$ r1_tarski > v1_relat_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_wellord1 > k2_tarski > #nlpp > k3_tarski > k1_wellord2 > k1_setfam_1 > k1_xboole_0 > #skF_1
% 2.09/1.22  
% 2.09/1.22  %Foreground sorts:
% 2.09/1.22  
% 2.09/1.22  
% 2.09/1.22  %Background operators:
% 2.09/1.22  
% 2.09/1.22  
% 2.09/1.22  %Foreground operators:
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.22  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 2.09/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.09/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.09/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.22  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 2.09/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.22  
% 2.09/1.23  tff(f_58, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 2.09/1.23  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.09/1.23  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.09/1.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.09/1.23  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.09/1.23  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.09/1.23  tff(f_62, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 2.09/1.23  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => (k2_wellord1(k2_wellord1(B, A), A) = k2_wellord1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_wellord1)).
% 2.09/1.23  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 2.09/1.23  tff(f_65, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 2.09/1.23  tff(c_28, plain, (![A_22]: (v1_relat_1(k1_wellord2(A_22)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.09/1.23  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.23  tff(c_64, plain, (![A_34, B_35]: (k4_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.23  tff(c_72, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_64])).
% 2.09/1.23  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.23  tff(c_118, plain, (![A_45, B_46]: (k5_xboole_0(A_45, k3_xboole_0(A_45, B_46))=k4_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.23  tff(c_127, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_118])).
% 2.09/1.23  tff(c_130, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_72, c_127])).
% 2.09/1.23  tff(c_16, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.09/1.23  tff(c_30, plain, (![B_24, A_23]: (k2_wellord1(k1_wellord2(B_24), A_23)=k1_wellord2(A_23) | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.23  tff(c_169, plain, (![B_54, A_55]: (k2_wellord1(k2_wellord1(B_54, A_55), A_55)=k2_wellord1(B_54, A_55) | ~v1_relat_1(B_54))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.09/1.23  tff(c_184, plain, (![B_24, A_23]: (k2_wellord1(k1_wellord2(B_24), A_23)=k2_wellord1(k1_wellord2(A_23), A_23) | ~v1_relat_1(k1_wellord2(B_24)) | ~r1_tarski(A_23, B_24))), inference(superposition, [status(thm), theory('equality')], [c_30, c_169])).
% 2.09/1.23  tff(c_222, plain, (![B_62, A_63]: (k2_wellord1(k1_wellord2(B_62), A_63)=k2_wellord1(k1_wellord2(A_63), A_63) | ~r1_tarski(A_63, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_184])).
% 2.09/1.23  tff(c_303, plain, (![A_67, B_68]: (k2_wellord1(k1_wellord2(A_67), A_67)=k1_wellord2(A_67) | ~r1_tarski(A_67, B_68) | ~r1_tarski(A_67, B_68))), inference(superposition, [status(thm), theory('equality')], [c_30, c_222])).
% 2.09/1.23  tff(c_307, plain, (![A_9, B_10]: (k2_wellord1(k1_wellord2(A_9), A_9)=k1_wellord2(A_9) | ~r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(resolution, [status(thm)], [c_16, c_303])).
% 2.09/1.23  tff(c_319, plain, (![A_69]: (k2_wellord1(k1_wellord2(A_69), A_69)=k1_wellord2(A_69))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_307])).
% 2.09/1.23  tff(c_191, plain, (![A_56, B_57]: (k3_xboole_0(A_56, k2_zfmisc_1(B_57, B_57))=k2_wellord1(A_56, B_57) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.09/1.23  tff(c_14, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.09/1.23  tff(c_197, plain, (![A_56, B_57]: (k5_xboole_0(A_56, k2_wellord1(A_56, B_57))=k4_xboole_0(A_56, k2_zfmisc_1(B_57, B_57)) | ~v1_relat_1(A_56))), inference(superposition, [status(thm), theory('equality')], [c_191, c_14])).
% 2.09/1.23  tff(c_325, plain, (![A_69]: (k5_xboole_0(k1_wellord2(A_69), k1_wellord2(A_69))=k4_xboole_0(k1_wellord2(A_69), k2_zfmisc_1(A_69, A_69)) | ~v1_relat_1(k1_wellord2(A_69)))), inference(superposition, [status(thm), theory('equality')], [c_319, c_197])).
% 2.09/1.23  tff(c_341, plain, (![A_69]: (k4_xboole_0(k1_wellord2(A_69), k2_zfmisc_1(A_69, A_69))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_130, c_325])).
% 2.09/1.23  tff(c_96, plain, (![A_41, B_42]: (r1_tarski(A_41, B_42) | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.23  tff(c_32, plain, (~r1_tarski(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.09/1.23  tff(c_104, plain, (k4_xboole_0(k1_wellord2('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_96, c_32])).
% 2.09/1.23  tff(c_354, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_341, c_104])).
% 2.09/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  Inference rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Ref     : 0
% 2.09/1.23  #Sup     : 70
% 2.09/1.23  #Fact    : 0
% 2.09/1.23  #Define  : 0
% 2.09/1.23  #Split   : 0
% 2.09/1.23  #Chain   : 0
% 2.09/1.23  #Close   : 0
% 2.09/1.23  
% 2.09/1.23  Ordering : KBO
% 2.09/1.23  
% 2.09/1.23  Simplification rules
% 2.09/1.23  ----------------------
% 2.09/1.23  #Subsume      : 7
% 2.09/1.23  #Demod        : 27
% 2.09/1.23  #Tautology    : 42
% 2.09/1.23  #SimpNegUnit  : 0
% 2.09/1.23  #BackRed      : 2
% 2.09/1.23  
% 2.09/1.23  #Partial instantiations: 0
% 2.09/1.23  #Strategies tried      : 1
% 2.09/1.23  
% 2.09/1.23  Timing (in seconds)
% 2.09/1.23  ----------------------
% 2.09/1.23  Preprocessing        : 0.29
% 2.09/1.23  Parsing              : 0.15
% 2.09/1.23  CNF conversion       : 0.02
% 2.09/1.23  Main loop            : 0.19
% 2.09/1.23  Inferencing          : 0.08
% 2.09/1.23  Reduction            : 0.06
% 2.09/1.23  Demodulation         : 0.04
% 2.09/1.23  BG Simplification    : 0.01
% 2.09/1.23  Subsumption          : 0.03
% 2.09/1.23  Abstraction          : 0.01
% 2.09/1.23  MUC search           : 0.00
% 2.09/1.23  Cooper               : 0.00
% 2.09/1.23  Total                : 0.51
% 2.09/1.23  Index Insertion      : 0.00
% 2.09/1.23  Index Deletion       : 0.00
% 2.09/1.23  Index Matching       : 0.00
% 2.09/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
