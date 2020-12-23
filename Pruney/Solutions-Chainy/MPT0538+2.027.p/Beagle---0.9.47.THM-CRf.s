%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:26 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   36 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  82 expanded)
%              Number of equality atoms :   27 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k8_relat_1(A,B) = k3_xboole_0(B,k2_zfmisc_1(k1_relat_1(B),A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t124_relat_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t138_relat_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_42,plain,(
    ! [A_37] :
      ( r2_hidden('#skF_1'(A_37),A_37)
      | v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_231,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(k1_tarski(A_78),B_79)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_241,plain,(
    ! [A_80] :
      ( k1_tarski(A_80) = k1_xboole_0
      | ~ r2_hidden(A_80,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_231,c_6])).

tff(c_246,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_42,c_241])).

tff(c_247,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_362,plain,(
    ! [B_96,A_97] :
      ( k3_xboole_0(B_96,k2_zfmisc_1(k1_relat_1(B_96),A_97)) = k8_relat_1(A_97,B_96)
      | ~ v1_relat_1(B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_248,plain,(
    ! [A_81,B_82] : k5_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k4_xboole_0(A_81,B_82) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_100,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_116,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_10])).

tff(c_255,plain,(
    ! [B_82] : k4_xboole_0(k1_xboole_0,B_82) = k3_xboole_0(k1_xboole_0,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_248,c_116])).

tff(c_267,plain,(
    ! [B_82] : k3_xboole_0(k1_xboole_0,B_82) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_255])).

tff(c_369,plain,(
    ! [A_97] :
      ( k8_relat_1(A_97,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_267])).

tff(c_382,plain,(
    ! [A_97] : k8_relat_1(A_97,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_369])).

tff(c_46,plain,(
    k8_relat_1('#skF_4',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_388,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_46])).

tff(c_389,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_30,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_420,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_389,c_30])).

tff(c_434,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_389,c_8,c_420])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:17:59 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.33  
% 2.01/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.33  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k8_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.31/1.33  
% 2.31/1.33  %Foreground sorts:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Background operators:
% 2.31/1.33  
% 2.31/1.33  
% 2.31/1.33  %Foreground operators:
% 2.31/1.33  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.33  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.31/1.33  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.31/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.31/1.33  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.31/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.33  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.33  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.31/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.31/1.33  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.31/1.33  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.31/1.33  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.31/1.33  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.33  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.33  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.33  tff('#skF_4', type, '#skF_4': $i).
% 2.31/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.33  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.31/1.33  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.31/1.33  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.31/1.33  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.33  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.31/1.33  
% 2.31/1.34  tff(f_74, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.31/1.34  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.31/1.34  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.31/1.34  tff(f_78, axiom, (![A, B]: (v1_relat_1(B) => (k8_relat_1(A, B) = k3_xboole_0(B, k2_zfmisc_1(k1_relat_1(B), A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t124_relat_1)).
% 2.31/1.34  tff(f_35, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.31/1.34  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.31/1.34  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.31/1.34  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.31/1.34  tff(f_81, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t138_relat_1)).
% 2.31/1.34  tff(f_60, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.31/1.34  tff(c_42, plain, (![A_37]: (r2_hidden('#skF_1'(A_37), A_37) | v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.31/1.34  tff(c_231, plain, (![A_78, B_79]: (r1_tarski(k1_tarski(A_78), B_79) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.31/1.34  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.31/1.34  tff(c_241, plain, (![A_80]: (k1_tarski(A_80)=k1_xboole_0 | ~r2_hidden(A_80, k1_xboole_0))), inference(resolution, [status(thm)], [c_231, c_6])).
% 2.31/1.34  tff(c_246, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_42, c_241])).
% 2.31/1.34  tff(c_247, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_246])).
% 2.31/1.34  tff(c_362, plain, (![B_96, A_97]: (k3_xboole_0(B_96, k2_zfmisc_1(k1_relat_1(B_96), A_97))=k8_relat_1(A_97, B_96) | ~v1_relat_1(B_96))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.31/1.34  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.31/1.34  tff(c_248, plain, (![A_81, B_82]: (k5_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k4_xboole_0(A_81, B_82))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.31/1.34  tff(c_100, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.31/1.34  tff(c_10, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.31/1.34  tff(c_116, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_100, c_10])).
% 2.31/1.34  tff(c_255, plain, (![B_82]: (k4_xboole_0(k1_xboole_0, B_82)=k3_xboole_0(k1_xboole_0, B_82))), inference(superposition, [status(thm), theory('equality')], [c_248, c_116])).
% 2.31/1.34  tff(c_267, plain, (![B_82]: (k3_xboole_0(k1_xboole_0, B_82)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_255])).
% 2.31/1.34  tff(c_369, plain, (![A_97]: (k8_relat_1(A_97, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_362, c_267])).
% 2.31/1.34  tff(c_382, plain, (![A_97]: (k8_relat_1(A_97, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_247, c_369])).
% 2.31/1.34  tff(c_46, plain, (k8_relat_1('#skF_4', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.31/1.34  tff(c_388, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_382, c_46])).
% 2.31/1.34  tff(c_389, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_246])).
% 2.31/1.34  tff(c_30, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.31/1.34  tff(c_420, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_389, c_30])).
% 2.31/1.34  tff(c_434, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_389, c_8, c_420])).
% 2.31/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.34  
% 2.31/1.34  Inference rules
% 2.31/1.34  ----------------------
% 2.31/1.34  #Ref     : 0
% 2.31/1.34  #Sup     : 85
% 2.31/1.34  #Fact    : 0
% 2.31/1.34  #Define  : 0
% 2.31/1.34  #Split   : 1
% 2.31/1.34  #Chain   : 0
% 2.31/1.34  #Close   : 0
% 2.31/1.34  
% 2.31/1.34  Ordering : KBO
% 2.31/1.34  
% 2.31/1.34  Simplification rules
% 2.31/1.34  ----------------------
% 2.31/1.34  #Subsume      : 0
% 2.31/1.34  #Demod        : 24
% 2.31/1.34  #Tautology    : 67
% 2.31/1.34  #SimpNegUnit  : 1
% 2.31/1.34  #BackRed      : 3
% 2.31/1.34  
% 2.31/1.34  #Partial instantiations: 0
% 2.31/1.34  #Strategies tried      : 1
% 2.31/1.34  
% 2.31/1.34  Timing (in seconds)
% 2.31/1.34  ----------------------
% 2.31/1.35  Preprocessing        : 0.34
% 2.31/1.35  Parsing              : 0.18
% 2.31/1.35  CNF conversion       : 0.02
% 2.31/1.35  Main loop            : 0.19
% 2.31/1.35  Inferencing          : 0.07
% 2.31/1.35  Reduction            : 0.06
% 2.31/1.35  Demodulation         : 0.05
% 2.31/1.35  BG Simplification    : 0.02
% 2.31/1.35  Subsumption          : 0.02
% 2.31/1.35  Abstraction          : 0.01
% 2.31/1.35  MUC search           : 0.00
% 2.31/1.35  Cooper               : 0.00
% 2.31/1.35  Total                : 0.55
% 2.31/1.35  Index Insertion      : 0.00
% 2.31/1.35  Index Deletion       : 0.00
% 2.31/1.35  Index Matching       : 0.00
% 2.31/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
