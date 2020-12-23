%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:39 EST 2020

% Result     : Theorem 2.25s
% Output     : CNFRefutation 2.25s
% Verified   : 
% Statistics : Number of formulae       :   61 (  87 expanded)
%              Number of leaves         :   38 (  47 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 ( 101 expanded)
%              Number of equality atoms :   30 (  47 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_33,axiom,(
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

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_265,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_274,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_265])).

tff(c_277,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_274])).

tff(c_36,plain,(
    ! [A_34] :
      ( r2_hidden('#skF_1'(A_34),A_34)
      | v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_121,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k1_tarski(A_68),B_69)
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_70] :
      ( k1_tarski(A_70) = k1_xboole_0
      | ~ r2_hidden(A_70,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_121,c_6])).

tff(c_136,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_36,c_131])).

tff(c_138,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_42,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_38,plain,(
    ! [A_52] : k7_relat_1(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_192,plain,(
    ! [B_82,A_83] :
      ( k2_relat_1(k7_relat_1(B_82,A_83)) = k9_relat_1(B_82,A_83)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_201,plain,(
    ! [A_52] :
      ( k9_relat_1(k1_xboole_0,A_52) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_192])).

tff(c_205,plain,(
    ! [A_52] : k9_relat_1(k1_xboole_0,A_52) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_42,c_201])).

tff(c_46,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_46])).

tff(c_218,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_233,plain,(
    ! [B_87] : k4_xboole_0(k1_tarski(B_87),k1_tarski(B_87)) != k1_tarski(B_87) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_236,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_218,c_233])).

tff(c_240,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_218,c_218,c_236])).

tff(c_286,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_240])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.25/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.29  
% 2.25/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.29  %$ r2_hidden > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.25/1.29  
% 2.25/1.29  %Foreground sorts:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Background operators:
% 2.25/1.29  
% 2.25/1.29  
% 2.25/1.29  %Foreground operators:
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.25/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.25/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.25/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.25/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.25/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.25/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.25/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.25/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.25/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.25/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.25/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.25/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.25/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.25/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.25/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.25/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.25/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.25/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.25/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.25/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.25/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.25/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.25/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.25/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.25/1.29  
% 2.25/1.31  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.25/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.25/1.31  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.25/1.31  tff(f_68, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.25/1.31  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.25/1.31  tff(f_33, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.25/1.31  tff(f_77, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.25/1.31  tff(f_70, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.25/1.31  tff(f_74, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.25/1.31  tff(f_80, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.25/1.31  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.25/1.31  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.25/1.31  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.25/1.31  tff(c_265, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.25/1.31  tff(c_274, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_265])).
% 2.25/1.31  tff(c_277, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_274])).
% 2.25/1.31  tff(c_36, plain, (![A_34]: (r2_hidden('#skF_1'(A_34), A_34) | v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.25/1.31  tff(c_121, plain, (![A_68, B_69]: (r1_tarski(k1_tarski(A_68), B_69) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.25/1.31  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.25/1.31  tff(c_131, plain, (![A_70]: (k1_tarski(A_70)=k1_xboole_0 | ~r2_hidden(A_70, k1_xboole_0))), inference(resolution, [status(thm)], [c_121, c_6])).
% 2.25/1.31  tff(c_136, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_36, c_131])).
% 2.25/1.31  tff(c_138, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_136])).
% 2.25/1.31  tff(c_42, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.25/1.31  tff(c_38, plain, (![A_52]: (k7_relat_1(k1_xboole_0, A_52)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.25/1.31  tff(c_192, plain, (![B_82, A_83]: (k2_relat_1(k7_relat_1(B_82, A_83))=k9_relat_1(B_82, A_83) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.25/1.31  tff(c_201, plain, (![A_52]: (k9_relat_1(k1_xboole_0, A_52)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_192])).
% 2.25/1.31  tff(c_205, plain, (![A_52]: (k9_relat_1(k1_xboole_0, A_52)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_138, c_42, c_201])).
% 2.25/1.31  tff(c_46, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.25/1.31  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_205, c_46])).
% 2.25/1.31  tff(c_218, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_136])).
% 2.25/1.31  tff(c_233, plain, (![B_87]: (k4_xboole_0(k1_tarski(B_87), k1_tarski(B_87))!=k1_tarski(B_87))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.25/1.31  tff(c_236, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_218, c_233])).
% 2.25/1.31  tff(c_240, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_218, c_218, c_236])).
% 2.25/1.31  tff(c_286, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_240])).
% 2.25/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.25/1.31  
% 2.25/1.31  Inference rules
% 2.25/1.31  ----------------------
% 2.25/1.31  #Ref     : 0
% 2.25/1.31  #Sup     : 53
% 2.25/1.31  #Fact    : 0
% 2.25/1.31  #Define  : 0
% 2.25/1.31  #Split   : 1
% 2.25/1.31  #Chain   : 0
% 2.25/1.31  #Close   : 0
% 2.25/1.31  
% 2.25/1.31  Ordering : KBO
% 2.25/1.31  
% 2.25/1.31  Simplification rules
% 2.25/1.31  ----------------------
% 2.25/1.31  #Subsume      : 1
% 2.25/1.31  #Demod        : 15
% 2.25/1.31  #Tautology    : 41
% 2.25/1.31  #SimpNegUnit  : 4
% 2.25/1.31  #BackRed      : 5
% 2.25/1.31  
% 2.25/1.31  #Partial instantiations: 0
% 2.25/1.31  #Strategies tried      : 1
% 2.25/1.31  
% 2.25/1.31  Timing (in seconds)
% 2.25/1.31  ----------------------
% 2.25/1.31  Preprocessing        : 0.34
% 2.25/1.31  Parsing              : 0.18
% 2.25/1.31  CNF conversion       : 0.02
% 2.25/1.31  Main loop            : 0.17
% 2.25/1.31  Inferencing          : 0.06
% 2.25/1.31  Reduction            : 0.05
% 2.25/1.31  Demodulation         : 0.04
% 2.25/1.31  BG Simplification    : 0.01
% 2.25/1.31  Subsumption          : 0.02
% 2.25/1.31  Abstraction          : 0.01
% 2.25/1.31  MUC search           : 0.00
% 2.25/1.31  Cooper               : 0.00
% 2.25/1.31  Total                : 0.54
% 2.25/1.31  Index Insertion      : 0.00
% 2.25/1.31  Index Deletion       : 0.00
% 2.25/1.31  Index Matching       : 0.00
% 2.25/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
