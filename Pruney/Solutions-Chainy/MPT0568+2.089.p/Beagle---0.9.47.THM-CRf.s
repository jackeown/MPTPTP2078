%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:32 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   61 (  61 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :   11
%              Number of atoms          :   53 (  53 expanded)
%              Number of equality atoms :   28 (  28 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_76,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_64,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_60,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_62,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_79,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_47,plain,(
    ! [A_31] : v1_relat_1(k6_relat_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_49,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_47])).

tff(c_248,plain,(
    ! [A_72,B_73,C_74] :
      ( r2_hidden(k4_tarski(A_72,'#skF_2'(A_72,B_73,C_74)),C_74)
      | ~ r2_hidden(A_72,k10_relat_1(C_74,B_73))
      | ~ v1_relat_1(C_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_21] : k1_setfam_1(k1_tarski(A_21)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_105,plain,(
    ! [A_45,B_46] : k1_setfam_1(k2_tarski(A_45,B_46)) = k3_xboole_0(A_45,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_114,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = k1_setfam_1(k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_105])).

tff(c_127,plain,(
    ! [A_49] : k3_xboole_0(A_49,A_49) = A_49 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_114])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_133,plain,(
    ! [A_49] : k5_xboole_0(A_49,A_49) = k4_xboole_0(A_49,A_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_4])).

tff(c_138,plain,(
    ! [A_49] : k4_xboole_0(A_49,A_49) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_133])).

tff(c_22,plain,(
    ! [B_20] : k4_xboole_0(k1_tarski(B_20),k1_tarski(B_20)) != k1_tarski(B_20) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_140,plain,(
    ! [B_20] : k1_tarski(B_20) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_22])).

tff(c_77,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(k1_tarski(A_37),B_38)
      | ~ r2_hidden(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_82,plain,(
    ! [A_37] :
      ( k1_tarski(A_37) = k1_xboole_0
      | ~ r2_hidden(A_37,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_77,c_6])).

tff(c_148,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_140,c_82])).

tff(c_256,plain,(
    ! [A_72,B_73] :
      ( ~ r2_hidden(A_72,k10_relat_1(k1_xboole_0,B_73))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_248,c_148])).

tff(c_261,plain,(
    ! [A_75,B_76] : ~ r2_hidden(A_75,k10_relat_1(k1_xboole_0,B_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49,c_256])).

tff(c_278,plain,(
    ! [B_76] : k10_relat_1(k1_xboole_0,B_76) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_261])).

tff(c_42,plain,(
    k10_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_283,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_278,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:47:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.26  
% 2.07/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.26  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > k10_relat_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.07/1.26  
% 2.07/1.26  %Foreground sorts:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Background operators:
% 2.07/1.26  
% 2.07/1.26  
% 2.07/1.26  %Foreground operators:
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.07/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.07/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.07/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.07/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.26  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.26  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.07/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.26  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.07/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.07/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.07/1.26  
% 2.07/1.27  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.07/1.27  tff(f_76, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.07/1.27  tff(f_64, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.07/1.27  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t166_relat_1)).
% 2.07/1.27  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.07/1.27  tff(f_60, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.07/1.27  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.27  tff(f_62, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.07/1.27  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.07/1.27  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.07/1.27  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.07/1.27  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.07/1.27  tff(f_79, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 2.07/1.27  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.27  tff(c_40, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.07/1.27  tff(c_47, plain, (![A_31]: (v1_relat_1(k6_relat_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.07/1.27  tff(c_49, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_47])).
% 2.07/1.27  tff(c_248, plain, (![A_72, B_73, C_74]: (r2_hidden(k4_tarski(A_72, '#skF_2'(A_72, B_73, C_74)), C_74) | ~r2_hidden(A_72, k10_relat_1(C_74, B_73)) | ~v1_relat_1(C_74))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.07/1.27  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.27  tff(c_26, plain, (![A_21]: (k1_setfam_1(k1_tarski(A_21))=A_21)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.27  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.07/1.27  tff(c_105, plain, (![A_45, B_46]: (k1_setfam_1(k2_tarski(A_45, B_46))=k3_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.07/1.27  tff(c_114, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=k1_setfam_1(k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_105])).
% 2.07/1.27  tff(c_127, plain, (![A_49]: (k3_xboole_0(A_49, A_49)=A_49)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_114])).
% 2.07/1.27  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.07/1.27  tff(c_133, plain, (![A_49]: (k5_xboole_0(A_49, A_49)=k4_xboole_0(A_49, A_49))), inference(superposition, [status(thm), theory('equality')], [c_127, c_4])).
% 2.07/1.27  tff(c_138, plain, (![A_49]: (k4_xboole_0(A_49, A_49)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_133])).
% 2.07/1.27  tff(c_22, plain, (![B_20]: (k4_xboole_0(k1_tarski(B_20), k1_tarski(B_20))!=k1_tarski(B_20))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.07/1.27  tff(c_140, plain, (![B_20]: (k1_tarski(B_20)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_22])).
% 2.07/1.27  tff(c_77, plain, (![A_37, B_38]: (r1_tarski(k1_tarski(A_37), B_38) | ~r2_hidden(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.07/1.27  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.07/1.27  tff(c_82, plain, (![A_37]: (k1_tarski(A_37)=k1_xboole_0 | ~r2_hidden(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_77, c_6])).
% 2.07/1.27  tff(c_148, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_140, c_82])).
% 2.07/1.27  tff(c_256, plain, (![A_72, B_73]: (~r2_hidden(A_72, k10_relat_1(k1_xboole_0, B_73)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_248, c_148])).
% 2.07/1.27  tff(c_261, plain, (![A_75, B_76]: (~r2_hidden(A_75, k10_relat_1(k1_xboole_0, B_76)))), inference(demodulation, [status(thm), theory('equality')], [c_49, c_256])).
% 2.07/1.27  tff(c_278, plain, (![B_76]: (k10_relat_1(k1_xboole_0, B_76)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_261])).
% 2.07/1.27  tff(c_42, plain, (k10_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.07/1.27  tff(c_283, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_278, c_42])).
% 2.07/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.27  
% 2.07/1.27  Inference rules
% 2.07/1.27  ----------------------
% 2.07/1.27  #Ref     : 0
% 2.07/1.27  #Sup     : 51
% 2.07/1.27  #Fact    : 0
% 2.07/1.27  #Define  : 0
% 2.07/1.27  #Split   : 0
% 2.07/1.27  #Chain   : 0
% 2.07/1.27  #Close   : 0
% 2.07/1.27  
% 2.07/1.27  Ordering : KBO
% 2.07/1.27  
% 2.07/1.27  Simplification rules
% 2.07/1.27  ----------------------
% 2.07/1.27  #Subsume      : 4
% 2.07/1.27  #Demod        : 10
% 2.07/1.27  #Tautology    : 35
% 2.07/1.27  #SimpNegUnit  : 3
% 2.07/1.27  #BackRed      : 4
% 2.07/1.27  
% 2.07/1.27  #Partial instantiations: 0
% 2.07/1.27  #Strategies tried      : 1
% 2.07/1.27  
% 2.07/1.27  Timing (in seconds)
% 2.07/1.27  ----------------------
% 2.07/1.27  Preprocessing        : 0.34
% 2.07/1.27  Parsing              : 0.18
% 2.07/1.27  CNF conversion       : 0.02
% 2.07/1.27  Main loop            : 0.17
% 2.07/1.27  Inferencing          : 0.07
% 2.07/1.27  Reduction            : 0.05
% 2.07/1.27  Demodulation         : 0.04
% 2.07/1.27  BG Simplification    : 0.01
% 2.07/1.27  Subsumption          : 0.02
% 2.07/1.27  Abstraction          : 0.01
% 2.07/1.27  MUC search           : 0.00
% 2.07/1.27  Cooper               : 0.00
% 2.07/1.27  Total                : 0.54
% 2.07/1.27  Index Insertion      : 0.00
% 2.07/1.27  Index Deletion       : 0.00
% 2.07/1.27  Index Matching       : 0.00
% 2.07/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
