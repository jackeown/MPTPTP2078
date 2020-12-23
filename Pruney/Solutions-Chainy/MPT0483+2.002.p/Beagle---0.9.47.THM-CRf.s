%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:32 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   54 (  60 expanded)
%              Number of leaves         :   33 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 (  67 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > r1_setfam_1 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k2_setfam_1 > #nlpp > k6_relat_1 > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k2_setfam_1,type,(
    k2_setfam_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : r1_setfam_1(A,k2_setfam_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
     => r1_tarski(k3_tarski(A),k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_setfam_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B,C,D] :
          ( ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
            | r1_tarski(k2_zfmisc_1(B,A),k2_zfmisc_1(D,C)) )
         => r1_tarski(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t139_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : ~ v1_xboole_0(k1_tarski(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_relat_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_28,plain,(
    ! [A_29] : r1_setfam_1(A_29,k2_setfam_1(A_29,A_29)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_26,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(k3_tarski(A_27),k3_tarski(B_28))
      | ~ r1_setfam_1(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    ! [A_15,C_17,B_16] :
      ( r1_tarski(k2_zfmisc_1(A_15,C_17),k2_zfmisc_1(B_16,C_17))
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_108,plain,(
    ! [A_58,B_59,C_60,D_61] :
      ( ~ r1_tarski(k2_zfmisc_1(A_58,B_59),k2_zfmisc_1(C_60,D_61))
      | r1_tarski(B_59,D_61)
      | v1_xboole_0(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_116,plain,(
    ! [C_17,A_15,B_16] :
      ( r1_tarski(C_17,C_17)
      | v1_xboole_0(A_15)
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(resolution,[status(thm)],[c_18,c_108])).

tff(c_118,plain,(
    ! [A_62,B_63] :
      ( v1_xboole_0(A_62)
      | ~ r1_tarski(A_62,B_63) ) ),
    inference(splitLeft,[status(thm)],[c_116])).

tff(c_135,plain,(
    ! [A_64,B_65] :
      ( v1_xboole_0(k3_tarski(A_64))
      | ~ r1_setfam_1(A_64,B_65) ) ),
    inference(resolution,[status(thm)],[c_26,c_118])).

tff(c_149,plain,(
    ! [A_70] : v1_xboole_0(k3_tarski(A_70)) ),
    inference(resolution,[status(thm)],[c_28,c_135])).

tff(c_152,plain,(
    ! [A_71,B_72] : v1_xboole_0(k2_xboole_0(A_71,B_72)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_149])).

tff(c_154,plain,(
    ! [A_1] : v1_xboole_0(A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_152])).

tff(c_12,plain,(
    ! [A_12] : ~ v1_xboole_0(k1_tarski(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_12])).

tff(c_164,plain,(
    ! [C_73] : r1_tarski(C_73,C_73) ),
    inference(splitRight,[status(thm)],[c_116])).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( k5_relat_1(k6_relat_1(A_30),B_31) = B_31
      | ~ r1_tarski(k1_relat_1(B_31),A_30)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_176,plain,(
    ! [B_74] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(B_74)),B_74) = B_74
      | ~ v1_relat_1(B_74) ) ),
    inference(resolution,[status(thm)],[c_164,c_30])).

tff(c_32,plain,(
    k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')),'#skF_1') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_182,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_176,c_32])).

tff(c_190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:37:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  
% 1.96/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.20  %$ r1_tarski > r1_setfam_1 > v1_xboole_0 > v1_relat_1 > k6_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > k2_setfam_1 > #nlpp > k6_relat_1 > k3_tarski > k1_tarski > k1_setfam_1 > k1_relat_1 > #skF_1
% 1.96/1.20  
% 1.96/1.20  %Foreground sorts:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Background operators:
% 1.96/1.20  
% 1.96/1.20  
% 1.96/1.20  %Foreground operators:
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.20  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.96/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.96/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.20  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.20  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.96/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.96/1.20  tff(k2_setfam_1, type, k2_setfam_1: ($i * $i) > $i).
% 1.96/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.96/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.96/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.20  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.20  
% 2.06/1.21  tff(f_75, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 2.06/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.06/1.21  tff(f_40, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.06/1.21  tff(f_64, axiom, (![A]: r1_setfam_1(A, k2_setfam_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_setfam_1)).
% 2.06/1.21  tff(f_62, axiom, (![A, B]: (r1_setfam_1(A, B) => r1_tarski(k3_tarski(A), k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_setfam_1)).
% 2.06/1.21  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 2.06/1.21  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (![B, C, D]: ((r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) | r1_tarski(k2_zfmisc_1(B, A), k2_zfmisc_1(D, C))) => r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t139_zfmisc_1)).
% 2.06/1.21  tff(f_38, axiom, (![A]: ~v1_xboole_0(k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc2_xboole_0)).
% 2.06/1.21  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_relat_1)).
% 2.06/1.21  tff(c_34, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.21  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.21  tff(c_14, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.21  tff(c_28, plain, (![A_29]: (r1_setfam_1(A_29, k2_setfam_1(A_29, A_29)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.06/1.21  tff(c_26, plain, (![A_27, B_28]: (r1_tarski(k3_tarski(A_27), k3_tarski(B_28)) | ~r1_setfam_1(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.06/1.21  tff(c_18, plain, (![A_15, C_17, B_16]: (r1_tarski(k2_zfmisc_1(A_15, C_17), k2_zfmisc_1(B_16, C_17)) | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.06/1.21  tff(c_108, plain, (![A_58, B_59, C_60, D_61]: (~r1_tarski(k2_zfmisc_1(A_58, B_59), k2_zfmisc_1(C_60, D_61)) | r1_tarski(B_59, D_61) | v1_xboole_0(A_58))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.06/1.21  tff(c_116, plain, (![C_17, A_15, B_16]: (r1_tarski(C_17, C_17) | v1_xboole_0(A_15) | ~r1_tarski(A_15, B_16))), inference(resolution, [status(thm)], [c_18, c_108])).
% 2.06/1.21  tff(c_118, plain, (![A_62, B_63]: (v1_xboole_0(A_62) | ~r1_tarski(A_62, B_63))), inference(splitLeft, [status(thm)], [c_116])).
% 2.06/1.21  tff(c_135, plain, (![A_64, B_65]: (v1_xboole_0(k3_tarski(A_64)) | ~r1_setfam_1(A_64, B_65))), inference(resolution, [status(thm)], [c_26, c_118])).
% 2.06/1.21  tff(c_149, plain, (![A_70]: (v1_xboole_0(k3_tarski(A_70)))), inference(resolution, [status(thm)], [c_28, c_135])).
% 2.06/1.21  tff(c_152, plain, (![A_71, B_72]: (v1_xboole_0(k2_xboole_0(A_71, B_72)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_149])).
% 2.06/1.21  tff(c_154, plain, (![A_1]: (v1_xboole_0(A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_152])).
% 2.06/1.21  tff(c_12, plain, (![A_12]: (~v1_xboole_0(k1_tarski(A_12)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.06/1.21  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_154, c_12])).
% 2.06/1.21  tff(c_164, plain, (![C_73]: (r1_tarski(C_73, C_73))), inference(splitRight, [status(thm)], [c_116])).
% 2.06/1.21  tff(c_30, plain, (![A_30, B_31]: (k5_relat_1(k6_relat_1(A_30), B_31)=B_31 | ~r1_tarski(k1_relat_1(B_31), A_30) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.06/1.21  tff(c_176, plain, (![B_74]: (k5_relat_1(k6_relat_1(k1_relat_1(B_74)), B_74)=B_74 | ~v1_relat_1(B_74))), inference(resolution, [status(thm)], [c_164, c_30])).
% 2.06/1.21  tff(c_32, plain, (k5_relat_1(k6_relat_1(k1_relat_1('#skF_1')), '#skF_1')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.06/1.21  tff(c_182, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_176, c_32])).
% 2.06/1.21  tff(c_190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_182])).
% 2.06/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.21  
% 2.06/1.21  Inference rules
% 2.06/1.21  ----------------------
% 2.06/1.21  #Ref     : 0
% 2.06/1.21  #Sup     : 32
% 2.06/1.21  #Fact    : 0
% 2.06/1.21  #Define  : 0
% 2.06/1.21  #Split   : 1
% 2.06/1.21  #Chain   : 0
% 2.06/1.21  #Close   : 0
% 2.06/1.21  
% 2.06/1.21  Ordering : KBO
% 2.06/1.21  
% 2.06/1.21  Simplification rules
% 2.06/1.21  ----------------------
% 2.06/1.21  #Subsume      : 1
% 2.06/1.21  #Demod        : 9
% 2.06/1.21  #Tautology    : 22
% 2.06/1.21  #SimpNegUnit  : 0
% 2.06/1.21  #BackRed      : 1
% 2.06/1.21  
% 2.06/1.21  #Partial instantiations: 0
% 2.06/1.21  #Strategies tried      : 1
% 2.06/1.21  
% 2.06/1.21  Timing (in seconds)
% 2.06/1.21  ----------------------
% 2.06/1.21  Preprocessing        : 0.29
% 2.06/1.21  Parsing              : 0.16
% 2.06/1.21  CNF conversion       : 0.02
% 2.06/1.21  Main loop            : 0.14
% 2.06/1.21  Inferencing          : 0.06
% 2.06/1.21  Reduction            : 0.04
% 2.06/1.21  Demodulation         : 0.03
% 2.06/1.21  BG Simplification    : 0.01
% 2.06/1.21  Subsumption          : 0.02
% 2.06/1.21  Abstraction          : 0.01
% 2.06/1.21  MUC search           : 0.00
% 2.06/1.21  Cooper               : 0.00
% 2.06/1.21  Total                : 0.46
% 2.06/1.21  Index Insertion      : 0.00
% 2.06/1.21  Index Deletion       : 0.00
% 2.06/1.21  Index Matching       : 0.00
% 2.06/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------
