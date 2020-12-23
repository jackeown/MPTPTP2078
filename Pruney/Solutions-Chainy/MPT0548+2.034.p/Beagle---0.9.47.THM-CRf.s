%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:39 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 1.96s
% Verified   : 
% Statistics : Number of formulae       :   66 (  74 expanded)
%              Number of leaves         :   40 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  70 expanded)
%              Number of equality atoms :   35 (  40 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_56,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_77,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_70,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_80,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_28,plain,(
    ! [A_30] : k1_setfam_1(k1_tarski(A_30)) = A_30 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_60,B_61] : k1_setfam_1(k2_tarski(A_60,B_61)) = k3_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = k1_setfam_1(k1_tarski(A_5)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_89])).

tff(c_101,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_98])).

tff(c_241,plain,(
    ! [A_86,B_87] : k5_xboole_0(A_86,k3_xboole_0(A_86,B_87)) = k4_xboole_0(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_250,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_241])).

tff(c_253,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_250])).

tff(c_24,plain,(
    ! [B_29] : k4_xboole_0(k1_tarski(B_29),k1_tarski(B_29)) != k1_tarski(B_29) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_254,plain,(
    ! [B_29] : k1_tarski(B_29) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_24])).

tff(c_36,plain,(
    ! [A_33] :
      ( r2_hidden('#skF_1'(A_33),A_33)
      | v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_122,plain,(
    ! [A_70,B_71] :
      ( r1_tarski(k1_tarski(A_70),B_71)
      | ~ r2_hidden(A_70,B_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_133,plain,(
    ! [A_73] :
      ( k1_tarski(A_73) = k1_xboole_0
      | ~ r2_hidden(A_73,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_138,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_133])).

tff(c_139,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [A_51] : k7_relat_1(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_192,plain,(
    ! [B_81,A_82] :
      ( k2_relat_1(k7_relat_1(B_81,A_82)) = k9_relat_1(B_81,A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_201,plain,(
    ! [A_51] :
      ( k9_relat_1(k1_xboole_0,A_51) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_192])).

tff(c_205,plain,(
    ! [A_51] : k9_relat_1(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_42,c_201])).

tff(c_46,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_46])).

tff(c_218,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_264,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:22:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  
% 1.96/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.21  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.96/1.21  
% 1.96/1.21  %Foreground sorts:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Background operators:
% 1.96/1.21  
% 1.96/1.21  
% 1.96/1.21  %Foreground operators:
% 1.96/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.96/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.96/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.96/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.96/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.96/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.96/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.96/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.96/1.22  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.96/1.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.96/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.96/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.96/1.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.96/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.96/1.22  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.96/1.22  
% 1.96/1.23  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 1.96/1.23  tff(f_56, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_setfam_1)).
% 1.96/1.23  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.96/1.23  tff(f_58, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 1.96/1.23  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 1.96/1.23  tff(f_54, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.96/1.23  tff(f_68, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 1.96/1.23  tff(f_49, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 1.96/1.23  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.96/1.23  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.96/1.23  tff(f_70, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.96/1.23  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.96/1.23  tff(f_80, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.96/1.23  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.96/1.23  tff(c_28, plain, (![A_30]: (k1_setfam_1(k1_tarski(A_30))=A_30)), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.96/1.23  tff(c_8, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.96/1.23  tff(c_89, plain, (![A_60, B_61]: (k1_setfam_1(k2_tarski(A_60, B_61))=k3_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.96/1.23  tff(c_98, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=k1_setfam_1(k1_tarski(A_5)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_89])).
% 1.96/1.23  tff(c_101, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_98])).
% 1.96/1.23  tff(c_241, plain, (![A_86, B_87]: (k5_xboole_0(A_86, k3_xboole_0(A_86, B_87))=k4_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.96/1.23  tff(c_250, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_101, c_241])).
% 1.96/1.23  tff(c_253, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_250])).
% 1.96/1.23  tff(c_24, plain, (![B_29]: (k4_xboole_0(k1_tarski(B_29), k1_tarski(B_29))!=k1_tarski(B_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.96/1.23  tff(c_254, plain, (![B_29]: (k1_tarski(B_29)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_253, c_24])).
% 1.96/1.23  tff(c_36, plain, (![A_33]: (r2_hidden('#skF_1'(A_33), A_33) | v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.96/1.23  tff(c_122, plain, (![A_70, B_71]: (r1_tarski(k1_tarski(A_70), B_71) | ~r2_hidden(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.96/1.23  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.96/1.23  tff(c_133, plain, (![A_73]: (k1_tarski(A_73)=k1_xboole_0 | ~r2_hidden(A_73, k1_xboole_0))), inference(resolution, [status(thm)], [c_122, c_4])).
% 1.96/1.23  tff(c_138, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_133])).
% 1.96/1.23  tff(c_139, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_138])).
% 1.96/1.23  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 1.96/1.23  tff(c_38, plain, (![A_51]: (k7_relat_1(k1_xboole_0, A_51)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.96/1.23  tff(c_192, plain, (![B_81, A_82]: (k2_relat_1(k7_relat_1(B_81, A_82))=k9_relat_1(B_81, A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.96/1.23  tff(c_201, plain, (![A_51]: (k9_relat_1(k1_xboole_0, A_51)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_192])).
% 1.96/1.23  tff(c_205, plain, (![A_51]: (k9_relat_1(k1_xboole_0, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_42, c_201])).
% 1.96/1.23  tff(c_46, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 1.96/1.23  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_46])).
% 1.96/1.23  tff(c_218, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_138])).
% 1.96/1.23  tff(c_264, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_218])).
% 1.96/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.96/1.23  
% 1.96/1.23  Inference rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Ref     : 0
% 1.96/1.23  #Sup     : 49
% 1.96/1.23  #Fact    : 0
% 1.96/1.23  #Define  : 0
% 1.96/1.23  #Split   : 1
% 1.96/1.23  #Chain   : 0
% 1.96/1.23  #Close   : 0
% 1.96/1.23  
% 1.96/1.23  Ordering : KBO
% 1.96/1.23  
% 1.96/1.23  Simplification rules
% 1.96/1.23  ----------------------
% 1.96/1.23  #Subsume      : 0
% 1.96/1.23  #Demod        : 13
% 1.96/1.23  #Tautology    : 38
% 1.96/1.23  #SimpNegUnit  : 5
% 1.96/1.23  #BackRed      : 6
% 1.96/1.23  
% 1.96/1.23  #Partial instantiations: 0
% 1.96/1.23  #Strategies tried      : 1
% 1.96/1.23  
% 1.96/1.23  Timing (in seconds)
% 1.96/1.23  ----------------------
% 2.21/1.23  Preprocessing        : 0.32
% 2.21/1.23  Parsing              : 0.17
% 2.21/1.23  CNF conversion       : 0.02
% 2.21/1.23  Main loop            : 0.16
% 2.21/1.23  Inferencing          : 0.06
% 2.21/1.23  Reduction            : 0.05
% 2.21/1.23  Demodulation         : 0.04
% 2.21/1.23  BG Simplification    : 0.01
% 2.21/1.23  Subsumption          : 0.02
% 2.21/1.23  Abstraction          : 0.01
% 2.21/1.23  MUC search           : 0.00
% 2.21/1.23  Cooper               : 0.00
% 2.21/1.23  Total                : 0.50
% 2.21/1.23  Index Insertion      : 0.00
% 2.21/1.23  Index Deletion       : 0.00
% 2.21/1.23  Index Matching       : 0.00
% 2.21/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
