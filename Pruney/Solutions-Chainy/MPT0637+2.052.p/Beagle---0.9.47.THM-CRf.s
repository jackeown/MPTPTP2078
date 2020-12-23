%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:03:31 EST 2020

% Result     : Theorem 1.94s
% Output     : CNFRefutation 2.15s
% Verified   : 
% Statistics : Number of formulae       :   50 (  76 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   55 (  94 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k5_relat_1(B,k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_funct_1)).

tff(c_8,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_20] : k2_relat_1(k6_relat_1(A_20)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_140,plain,(
    ! [A_44,B_45] :
      ( k8_relat_1(A_44,B_45) = B_45
      | ~ r1_tarski(k2_relat_1(B_45),A_44)
      | ~ v1_relat_1(B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_151,plain,(
    ! [B_46] :
      ( k8_relat_1(k2_relat_1(B_46),B_46) = B_46
      | ~ v1_relat_1(B_46) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_104,plain,(
    ! [A_40,B_41] :
      ( k5_relat_1(k6_relat_1(A_40),B_41) = k7_relat_1(B_41,A_40)
      | ~ v1_relat_1(B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [B_17,A_16] :
      ( k5_relat_1(B_17,k6_relat_1(A_16)) = k8_relat_1(A_16,B_17)
      | ~ v1_relat_1(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_111,plain,(
    ! [A_16,A_40] :
      ( k8_relat_1(A_16,k6_relat_1(A_40)) = k7_relat_1(k6_relat_1(A_16),A_40)
      | ~ v1_relat_1(k6_relat_1(A_40))
      | ~ v1_relat_1(k6_relat_1(A_16)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_20])).

tff(c_124,plain,(
    ! [A_16,A_40] : k8_relat_1(A_16,k6_relat_1(A_40)) = k7_relat_1(k6_relat_1(A_16),A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_16,c_111])).

tff(c_158,plain,(
    ! [A_40] :
      ( k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_40))),A_40) = k6_relat_1(A_40)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_124])).

tff(c_171,plain,(
    ! [A_40] : k7_relat_1(k6_relat_1(A_40),A_40) = k6_relat_1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26,c_158])).

tff(c_216,plain,(
    ! [C_52,A_53,B_54] :
      ( k7_relat_1(k7_relat_1(C_52,A_53),B_54) = k7_relat_1(C_52,k3_xboole_0(A_53,B_54))
      | ~ v1_relat_1(C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_234,plain,(
    ! [A_40,B_54] :
      ( k7_relat_1(k6_relat_1(A_40),k3_xboole_0(A_40,B_54)) = k7_relat_1(k6_relat_1(A_40),B_54)
      | ~ v1_relat_1(k6_relat_1(A_40)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_216])).

tff(c_241,plain,(
    ! [A_55,B_56] : k7_relat_1(k6_relat_1(A_55),k3_xboole_0(A_55,B_56)) = k7_relat_1(k6_relat_1(A_55),B_56) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_234])).

tff(c_143,plain,(
    ! [A_44,A_20] :
      ( k8_relat_1(A_44,k6_relat_1(A_20)) = k6_relat_1(A_20)
      | ~ r1_tarski(A_20,A_44)
      | ~ v1_relat_1(k6_relat_1(A_20)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_140])).

tff(c_149,plain,(
    ! [A_44,A_20] :
      ( k7_relat_1(k6_relat_1(A_44),A_20) = k6_relat_1(A_20)
      | ~ r1_tarski(A_20,A_44) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_124,c_143])).

tff(c_250,plain,(
    ! [A_55,B_56] :
      ( k7_relat_1(k6_relat_1(A_55),B_56) = k6_relat_1(k3_xboole_0(A_55,B_56))
      | ~ r1_tarski(k3_xboole_0(A_55,B_56),A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_241,c_149])).

tff(c_262,plain,(
    ! [A_55,B_56] : k7_relat_1(k6_relat_1(A_55),B_56) = k6_relat_1(k3_xboole_0(A_55,B_56)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_250])).

tff(c_30,plain,(
    k5_relat_1(k6_relat_1('#skF_2'),k6_relat_1('#skF_1')) != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_114,plain,
    ( k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2'))
    | ~ v1_relat_1(k6_relat_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_30])).

tff(c_126,plain,(
    k7_relat_1(k6_relat_1('#skF_1'),'#skF_2') != k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_114])).

tff(c_271,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:24:53 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.94/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.29  
% 1.94/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.94/1.30  %$ r1_tarski > v1_relat_1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k7_relat_1 > k5_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k2_relat_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 1.94/1.30  
% 1.94/1.30  %Foreground sorts:
% 1.94/1.30  
% 1.94/1.30  
% 1.94/1.30  %Background operators:
% 1.94/1.30  
% 1.94/1.30  
% 1.94/1.30  %Foreground operators:
% 1.94/1.30  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.94/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.94/1.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.94/1.30  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 1.94/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.94/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.94/1.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.94/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.94/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.94/1.30  tff('#skF_2', type, '#skF_2': $i).
% 1.94/1.30  tff('#skF_1', type, '#skF_1': $i).
% 1.94/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.94/1.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.94/1.30  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.94/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.94/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.94/1.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.94/1.30  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.94/1.30  
% 2.15/1.31  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.15/1.31  tff(f_41, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.15/1.31  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 2.15/1.31  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.15/1.31  tff(f_55, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t125_relat_1)).
% 2.15/1.31  tff(f_63, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 2.15/1.31  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k5_relat_1(B, k6_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_relat_1)).
% 2.15/1.31  tff(f_45, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 2.15/1.31  tff(f_66, negated_conjecture, ~(![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_funct_1)).
% 2.15/1.31  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.15/1.31  tff(c_16, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.15/1.31  tff(c_26, plain, (![A_20]: (k2_relat_1(k6_relat_1(A_20))=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.15/1.31  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.15/1.31  tff(c_140, plain, (![A_44, B_45]: (k8_relat_1(A_44, B_45)=B_45 | ~r1_tarski(k2_relat_1(B_45), A_44) | ~v1_relat_1(B_45))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.15/1.31  tff(c_151, plain, (![B_46]: (k8_relat_1(k2_relat_1(B_46), B_46)=B_46 | ~v1_relat_1(B_46))), inference(resolution, [status(thm)], [c_6, c_140])).
% 2.15/1.31  tff(c_104, plain, (![A_40, B_41]: (k5_relat_1(k6_relat_1(A_40), B_41)=k7_relat_1(B_41, A_40) | ~v1_relat_1(B_41))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.15/1.31  tff(c_20, plain, (![B_17, A_16]: (k5_relat_1(B_17, k6_relat_1(A_16))=k8_relat_1(A_16, B_17) | ~v1_relat_1(B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.15/1.31  tff(c_111, plain, (![A_16, A_40]: (k8_relat_1(A_16, k6_relat_1(A_40))=k7_relat_1(k6_relat_1(A_16), A_40) | ~v1_relat_1(k6_relat_1(A_40)) | ~v1_relat_1(k6_relat_1(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_104, c_20])).
% 2.15/1.31  tff(c_124, plain, (![A_16, A_40]: (k8_relat_1(A_16, k6_relat_1(A_40))=k7_relat_1(k6_relat_1(A_16), A_40))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_16, c_111])).
% 2.15/1.31  tff(c_158, plain, (![A_40]: (k7_relat_1(k6_relat_1(k2_relat_1(k6_relat_1(A_40))), A_40)=k6_relat_1(A_40) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_151, c_124])).
% 2.15/1.31  tff(c_171, plain, (![A_40]: (k7_relat_1(k6_relat_1(A_40), A_40)=k6_relat_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26, c_158])).
% 2.15/1.31  tff(c_216, plain, (![C_52, A_53, B_54]: (k7_relat_1(k7_relat_1(C_52, A_53), B_54)=k7_relat_1(C_52, k3_xboole_0(A_53, B_54)) | ~v1_relat_1(C_52))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.15/1.31  tff(c_234, plain, (![A_40, B_54]: (k7_relat_1(k6_relat_1(A_40), k3_xboole_0(A_40, B_54))=k7_relat_1(k6_relat_1(A_40), B_54) | ~v1_relat_1(k6_relat_1(A_40)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_216])).
% 2.15/1.31  tff(c_241, plain, (![A_55, B_56]: (k7_relat_1(k6_relat_1(A_55), k3_xboole_0(A_55, B_56))=k7_relat_1(k6_relat_1(A_55), B_56))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_234])).
% 2.15/1.31  tff(c_143, plain, (![A_44, A_20]: (k8_relat_1(A_44, k6_relat_1(A_20))=k6_relat_1(A_20) | ~r1_tarski(A_20, A_44) | ~v1_relat_1(k6_relat_1(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_140])).
% 2.15/1.31  tff(c_149, plain, (![A_44, A_20]: (k7_relat_1(k6_relat_1(A_44), A_20)=k6_relat_1(A_20) | ~r1_tarski(A_20, A_44))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_124, c_143])).
% 2.15/1.31  tff(c_250, plain, (![A_55, B_56]: (k7_relat_1(k6_relat_1(A_55), B_56)=k6_relat_1(k3_xboole_0(A_55, B_56)) | ~r1_tarski(k3_xboole_0(A_55, B_56), A_55))), inference(superposition, [status(thm), theory('equality')], [c_241, c_149])).
% 2.15/1.31  tff(c_262, plain, (![A_55, B_56]: (k7_relat_1(k6_relat_1(A_55), B_56)=k6_relat_1(k3_xboole_0(A_55, B_56)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_250])).
% 2.15/1.31  tff(c_30, plain, (k5_relat_1(k6_relat_1('#skF_2'), k6_relat_1('#skF_1'))!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.15/1.31  tff(c_114, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(k6_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_104, c_30])).
% 2.15/1.31  tff(c_126, plain, (k7_relat_1(k6_relat_1('#skF_1'), '#skF_2')!=k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_114])).
% 2.15/1.31  tff(c_271, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_126])).
% 2.15/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.15/1.31  
% 2.15/1.31  Inference rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Ref     : 0
% 2.15/1.31  #Sup     : 47
% 2.15/1.31  #Fact    : 0
% 2.15/1.31  #Define  : 0
% 2.15/1.31  #Split   : 1
% 2.15/1.31  #Chain   : 0
% 2.15/1.31  #Close   : 0
% 2.15/1.31  
% 2.15/1.31  Ordering : KBO
% 2.15/1.31  
% 2.15/1.31  Simplification rules
% 2.15/1.31  ----------------------
% 2.15/1.31  #Subsume      : 1
% 2.15/1.31  #Demod        : 31
% 2.15/1.31  #Tautology    : 33
% 2.15/1.31  #SimpNegUnit  : 0
% 2.15/1.31  #BackRed      : 5
% 2.15/1.31  
% 2.15/1.31  #Partial instantiations: 0
% 2.15/1.31  #Strategies tried      : 1
% 2.15/1.31  
% 2.15/1.31  Timing (in seconds)
% 2.15/1.31  ----------------------
% 2.15/1.31  Preprocessing        : 0.33
% 2.15/1.31  Parsing              : 0.17
% 2.15/1.31  CNF conversion       : 0.02
% 2.15/1.31  Main loop            : 0.17
% 2.15/1.31  Inferencing          : 0.06
% 2.15/1.31  Reduction            : 0.06
% 2.15/1.31  Demodulation         : 0.04
% 2.15/1.31  BG Simplification    : 0.01
% 2.15/1.31  Subsumption          : 0.02
% 2.15/1.31  Abstraction          : 0.01
% 2.15/1.31  MUC search           : 0.00
% 2.15/1.31  Cooper               : 0.00
% 2.15/1.31  Total                : 0.53
% 2.15/1.31  Index Insertion      : 0.00
% 2.15/1.31  Index Deletion       : 0.00
% 2.15/1.31  Index Matching       : 0.00
% 2.15/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
