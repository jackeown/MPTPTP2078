%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:25 EST 2020

% Result     : Theorem 2.48s
% Output     : CNFRefutation 2.48s
% Verified   : 
% Statistics : Number of formulae       :   63 (  71 expanded)
%              Number of leaves         :   37 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   44 (  52 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_74,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_41,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_44,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_1'(A_46),A_46)
      | v1_relat_1(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10,plain,(
    ! [A_8] : k4_xboole_0(k1_xboole_0,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_151,plain,(
    ! [C_75,B_76] : ~ r2_hidden(C_75,k4_xboole_0(B_76,k1_tarski(C_75))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_155,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_151])).

tff(c_160,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_44,c_155])).

tff(c_501,plain,(
    ! [B_109,A_110] :
      ( k3_xboole_0(B_109,k2_zfmisc_1(k1_relat_1(B_109),A_110)) = k8_relat_1(A_110,B_109)
      | ~ v1_relat_1(B_109) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_184,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k4_xboole_0(B_86,A_85)) = k2_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_193,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = k2_xboole_0(A_8,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_184])).

tff(c_206,plain,(
    ! [A_88] : k2_xboole_0(A_88,k1_xboole_0) = A_88 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_193])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_212,plain,(
    ! [A_88] : k2_xboole_0(k1_xboole_0,A_88) = A_88 ),
    inference(superposition,[status(thm),theory(equality)],[c_206,c_2])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_266,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_278,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_266])).

tff(c_305,plain,(
    ! [A_93] : k4_xboole_0(A_93,k1_xboole_0) = A_93 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_278])).

tff(c_16,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k4_xboole_0(B_12,A_11)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_315,plain,(
    ! [A_93] : k5_xboole_0(k1_xboole_0,A_93) = k2_xboole_0(k1_xboole_0,A_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_16])).

tff(c_367,plain,(
    ! [A_95] : k5_xboole_0(k1_xboole_0,A_95) = A_95 ),
    inference(demodulation,[status(thm),theory(equality)],[c_212,c_315])).

tff(c_393,plain,(
    ! [B_6] : k4_xboole_0(k1_xboole_0,B_6) = k3_xboole_0(k1_xboole_0,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_367])).

tff(c_412,plain,(
    ! [B_6] : k3_xboole_0(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_393])).

tff(c_508,plain,(
    ! [A_110] :
      ( k8_relat_1(A_110,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_501,c_412])).

tff(c_521,plain,(
    ! [A_110] : k8_relat_1(A_110,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_160,c_508])).

tff(c_48,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_521,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:33:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.48/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.30  
% 2.48/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.31  %$ r2_hidden > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.48/1.31  
% 2.48/1.31  %Foreground sorts:
% 2.48/1.31  
% 2.48/1.31  
% 2.48/1.31  %Background operators:
% 2.48/1.31  
% 2.48/1.31  
% 2.48/1.31  %Foreground operators:
% 2.48/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.48/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.48/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.48/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.48/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.48/1.31  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.48/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.48/1.31  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.48/1.31  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.48/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.48/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.48/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.48/1.31  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.31  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.48/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.48/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.48/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.48/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.48/1.31  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.48/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.48/1.31  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.48/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.48/1.31  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.48/1.31  
% 2.48/1.32  tff(f_74, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.48/1.32  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.48/1.32  tff(f_62, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.48/1.32  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t124_relat_1)).
% 2.48/1.32  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.48/1.32  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.48/1.32  tff(f_41, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.48/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.48/1.32  tff(f_33, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.48/1.32  tff(f_81, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 2.48/1.32  tff(c_44, plain, (![A_46]: (r2_hidden('#skF_1'(A_46), A_46) | v1_relat_1(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.48/1.32  tff(c_10, plain, (![A_8]: (k4_xboole_0(k1_xboole_0, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.48/1.32  tff(c_151, plain, (![C_75, B_76]: (~r2_hidden(C_75, k4_xboole_0(B_76, k1_tarski(C_75))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.48/1.32  tff(c_155, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_151])).
% 2.48/1.32  tff(c_160, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_44, c_155])).
% 2.48/1.32  tff(c_501, plain, (![B_109, A_110]: (k3_xboole_0(B_109, k2_zfmisc_1(k1_relat_1(B_109), A_110))=k8_relat_1(A_110, B_109) | ~v1_relat_1(B_109))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.48/1.32  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.32  tff(c_12, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.48/1.32  tff(c_184, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k4_xboole_0(B_86, A_85))=k2_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.32  tff(c_193, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=k2_xboole_0(A_8, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_184])).
% 2.48/1.32  tff(c_206, plain, (![A_88]: (k2_xboole_0(A_88, k1_xboole_0)=A_88)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_193])).
% 2.48/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.48/1.32  tff(c_212, plain, (![A_88]: (k2_xboole_0(k1_xboole_0, A_88)=A_88)), inference(superposition, [status(thm), theory('equality')], [c_206, c_2])).
% 2.48/1.32  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.48/1.32  tff(c_266, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.48/1.32  tff(c_278, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_266])).
% 2.48/1.32  tff(c_305, plain, (![A_93]: (k4_xboole_0(A_93, k1_xboole_0)=A_93)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_278])).
% 2.48/1.32  tff(c_16, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k4_xboole_0(B_12, A_11))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.48/1.32  tff(c_315, plain, (![A_93]: (k5_xboole_0(k1_xboole_0, A_93)=k2_xboole_0(k1_xboole_0, A_93))), inference(superposition, [status(thm), theory('equality')], [c_305, c_16])).
% 2.48/1.32  tff(c_367, plain, (![A_95]: (k5_xboole_0(k1_xboole_0, A_95)=A_95)), inference(demodulation, [status(thm), theory('equality')], [c_212, c_315])).
% 2.48/1.32  tff(c_393, plain, (![B_6]: (k4_xboole_0(k1_xboole_0, B_6)=k3_xboole_0(k1_xboole_0, B_6))), inference(superposition, [status(thm), theory('equality')], [c_6, c_367])).
% 2.48/1.32  tff(c_412, plain, (![B_6]: (k3_xboole_0(k1_xboole_0, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_393])).
% 2.48/1.32  tff(c_508, plain, (![A_110]: (k8_relat_1(A_110, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_501, c_412])).
% 2.48/1.32  tff(c_521, plain, (![A_110]: (k8_relat_1(A_110, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_160, c_508])).
% 2.48/1.32  tff(c_48, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.48/1.32  tff(c_536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_521, c_48])).
% 2.48/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.48/1.32  
% 2.48/1.32  Inference rules
% 2.48/1.32  ----------------------
% 2.48/1.32  #Ref     : 0
% 2.48/1.32  #Sup     : 107
% 2.48/1.32  #Fact    : 0
% 2.48/1.32  #Define  : 0
% 2.48/1.32  #Split   : 0
% 2.48/1.32  #Chain   : 0
% 2.48/1.32  #Close   : 0
% 2.48/1.32  
% 2.48/1.32  Ordering : KBO
% 2.48/1.32  
% 2.48/1.32  Simplification rules
% 2.48/1.32  ----------------------
% 2.48/1.32  #Subsume      : 4
% 2.48/1.32  #Demod        : 25
% 2.48/1.32  #Tautology    : 87
% 2.48/1.32  #SimpNegUnit  : 3
% 2.48/1.32  #BackRed      : 1
% 2.48/1.32  
% 2.48/1.32  #Partial instantiations: 0
% 2.48/1.32  #Strategies tried      : 1
% 2.48/1.32  
% 2.48/1.32  Timing (in seconds)
% 2.48/1.32  ----------------------
% 2.48/1.32  Preprocessing        : 0.34
% 2.48/1.32  Parsing              : 0.18
% 2.48/1.32  CNF conversion       : 0.02
% 2.48/1.32  Main loop            : 0.21
% 2.48/1.32  Inferencing          : 0.08
% 2.48/1.32  Reduction            : 0.07
% 2.48/1.32  Demodulation         : 0.05
% 2.48/1.32  BG Simplification    : 0.02
% 2.48/1.32  Subsumption          : 0.03
% 2.48/1.32  Abstraction          : 0.02
% 2.48/1.32  MUC search           : 0.00
% 2.48/1.32  Cooper               : 0.00
% 2.48/1.32  Total                : 0.59
% 2.48/1.32  Index Insertion      : 0.00
% 2.48/1.32  Index Deletion       : 0.00
% 2.48/1.32  Index Matching       : 0.00
% 2.48/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------
