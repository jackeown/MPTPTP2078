%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:43 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   61 (  61 expanded)
%              Number of leaves         :   38 (  38 expanded)
%              Depth                    :   10
%              Number of atoms          :   50 (  50 expanded)
%              Number of equality atoms :   25 (  25 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_82,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_70,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_61,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_85,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_46,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_53,plain,(
    ! [A_50] : v1_relat_1(k6_relat_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_55,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_53])).

tff(c_384,plain,(
    ! [A_113,B_114,C_115] :
      ( r2_hidden(k4_tarski('#skF_2'(A_113,B_114,C_115),A_113),C_115)
      | ~ r2_hidden(A_113,k9_relat_1(C_115,B_114))
      | ~ v1_relat_1(C_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_131,plain,(
    ! [A_66,B_67] : k3_xboole_0(k1_tarski(A_66),k2_tarski(A_66,B_67)) = k1_tarski(A_66) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_140,plain,(
    ! [A_7] : k3_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_tarski(A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_131])).

tff(c_168,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_177,plain,(
    ! [A_7] : k5_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_168])).

tff(c_186,plain,(
    ! [A_7] : k4_xboole_0(k1_tarski(A_7),k1_tarski(A_7)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_177])).

tff(c_30,plain,(
    ! [B_40] : k4_xboole_0(k1_tarski(B_40),k1_tarski(B_40)) != k1_tarski(B_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_188,plain,(
    ! [B_40] : k1_tarski(B_40) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_186,c_30])).

tff(c_105,plain,(
    ! [A_61,B_62] :
      ( r1_tarski(k1_tarski(A_61),B_62)
      | ~ r2_hidden(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_114,plain,(
    ! [A_61] :
      ( k1_tarski(A_61) = k1_xboole_0
      | ~ r2_hidden(A_61,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_105,c_6])).

tff(c_196,plain,(
    ! [A_61] : ~ r2_hidden(A_61,k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_188,c_114])).

tff(c_396,plain,(
    ! [A_113,B_114] :
      ( ~ r2_hidden(A_113,k9_relat_1(k1_xboole_0,B_114))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_384,c_196])).

tff(c_411,plain,(
    ! [A_123,B_124] : ~ r2_hidden(A_123,k9_relat_1(k1_xboole_0,B_124)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_396])).

tff(c_434,plain,(
    ! [B_124] : k9_relat_1(k1_xboole_0,B_124) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_411])).

tff(c_48,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_439,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_48])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n021.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:34 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  
% 2.25/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.32  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 2.25/1.32  
% 2.25/1.32  %Foreground sorts:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Background operators:
% 2.25/1.32  
% 2.25/1.32  
% 2.25/1.32  %Foreground operators:
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.32  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.32  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.25/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.32  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.32  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.25/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.25/1.32  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.32  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.25/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.32  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.32  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.32  
% 2.25/1.33  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.25/1.33  tff(f_82, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_relat_1)).
% 2.25/1.33  tff(f_70, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.25/1.33  tff(f_81, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 2.25/1.33  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.25/1.33  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.25/1.33  tff(f_61, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.25/1.33  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.25/1.33  tff(f_66, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.25/1.33  tff(f_59, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.25/1.33  tff(f_39, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.25/1.33  tff(f_85, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 2.25/1.33  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.33  tff(c_46, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.25/1.33  tff(c_53, plain, (![A_50]: (v1_relat_1(k6_relat_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.25/1.33  tff(c_55, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_53])).
% 2.25/1.33  tff(c_384, plain, (![A_113, B_114, C_115]: (r2_hidden(k4_tarski('#skF_2'(A_113, B_114, C_115), A_113), C_115) | ~r2_hidden(A_113, k9_relat_1(C_115, B_114)) | ~v1_relat_1(C_115))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.25/1.33  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.25/1.33  tff(c_10, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.25/1.33  tff(c_131, plain, (![A_66, B_67]: (k3_xboole_0(k1_tarski(A_66), k2_tarski(A_66, B_67))=k1_tarski(A_66))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.25/1.33  tff(c_140, plain, (![A_7]: (k3_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_tarski(A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_131])).
% 2.25/1.33  tff(c_168, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.33  tff(c_177, plain, (![A_7]: (k5_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_140, c_168])).
% 2.25/1.33  tff(c_186, plain, (![A_7]: (k4_xboole_0(k1_tarski(A_7), k1_tarski(A_7))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_177])).
% 2.25/1.33  tff(c_30, plain, (![B_40]: (k4_xboole_0(k1_tarski(B_40), k1_tarski(B_40))!=k1_tarski(B_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.25/1.33  tff(c_188, plain, (![B_40]: (k1_tarski(B_40)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_186, c_30])).
% 2.25/1.33  tff(c_105, plain, (![A_61, B_62]: (r1_tarski(k1_tarski(A_61), B_62) | ~r2_hidden(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.25/1.33  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.25/1.33  tff(c_114, plain, (![A_61]: (k1_tarski(A_61)=k1_xboole_0 | ~r2_hidden(A_61, k1_xboole_0))), inference(resolution, [status(thm)], [c_105, c_6])).
% 2.25/1.33  tff(c_196, plain, (![A_61]: (~r2_hidden(A_61, k1_xboole_0))), inference(negUnitSimplification, [status(thm)], [c_188, c_114])).
% 2.25/1.33  tff(c_396, plain, (![A_113, B_114]: (~r2_hidden(A_113, k9_relat_1(k1_xboole_0, B_114)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_384, c_196])).
% 2.25/1.33  tff(c_411, plain, (![A_123, B_124]: (~r2_hidden(A_123, k9_relat_1(k1_xboole_0, B_124)))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_396])).
% 2.25/1.33  tff(c_434, plain, (![B_124]: (k9_relat_1(k1_xboole_0, B_124)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_411])).
% 2.25/1.33  tff(c_48, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.25/1.33  tff(c_439, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_434, c_48])).
% 2.25/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.25/1.33  
% 2.25/1.33  Inference rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Ref     : 0
% 2.25/1.33  #Sup     : 86
% 2.25/1.33  #Fact    : 0
% 2.25/1.33  #Define  : 0
% 2.25/1.33  #Split   : 0
% 2.25/1.33  #Chain   : 0
% 2.25/1.33  #Close   : 0
% 2.25/1.33  
% 2.25/1.33  Ordering : KBO
% 2.25/1.33  
% 2.25/1.33  Simplification rules
% 2.25/1.33  ----------------------
% 2.25/1.33  #Subsume      : 10
% 2.25/1.33  #Demod        : 20
% 2.25/1.33  #Tautology    : 57
% 2.25/1.33  #SimpNegUnit  : 3
% 2.25/1.33  #BackRed      : 4
% 2.25/1.33  
% 2.25/1.33  #Partial instantiations: 0
% 2.25/1.33  #Strategies tried      : 1
% 2.25/1.33  
% 2.25/1.33  Timing (in seconds)
% 2.25/1.33  ----------------------
% 2.25/1.33  Preprocessing        : 0.34
% 2.25/1.33  Parsing              : 0.18
% 2.25/1.33  CNF conversion       : 0.02
% 2.25/1.33  Main loop            : 0.21
% 2.25/1.33  Inferencing          : 0.09
% 2.25/1.34  Reduction            : 0.06
% 2.25/1.34  Demodulation         : 0.05
% 2.25/1.34  BG Simplification    : 0.02
% 2.25/1.34  Subsumption          : 0.03
% 2.25/1.34  Abstraction          : 0.02
% 2.25/1.34  MUC search           : 0.00
% 2.25/1.34  Cooper               : 0.00
% 2.25/1.34  Total                : 0.57
% 2.25/1.34  Index Insertion      : 0.00
% 2.25/1.34  Index Deletion       : 0.00
% 2.25/1.34  Index Matching       : 0.00
% 2.25/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
