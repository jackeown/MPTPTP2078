%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:02 EST 2020

% Result     : Theorem 2.36s
% Output     : CNFRefutation 2.36s
% Verified   : 
% Statistics : Number of formulae       :   53 (  53 expanded)
%              Number of leaves         :   36 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  34 expanded)
%              Number of equality atoms :   18 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k3_xboole_0(B,k2_zfmisc_1(A,k2_relat_1(B))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t96_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_73,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_34,plain,(
    ! [A_40] :
      ( r2_hidden('#skF_1'(A_40),A_40)
      | v1_relat_1(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_183,plain,(
    ! [A_74,B_75] :
      ( ~ r2_hidden(A_74,B_75)
      | ~ r1_xboole_0(k1_tarski(A_74),B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_198,plain,(
    ! [A_78] : ~ r2_hidden(A_78,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_183])).

tff(c_203,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_34,c_198])).

tff(c_270,plain,(
    ! [B_86,A_87] :
      ( k3_xboole_0(B_86,k2_zfmisc_1(A_87,k2_relat_1(B_86))) = k7_relat_1(B_86,A_87)
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_5] : k4_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_204,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_65,plain,(
    ! [B_64,A_65] : k5_xboole_0(B_64,A_65) = k5_xboole_0(A_65,B_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_81,plain,(
    ! [A_65] : k5_xboole_0(k1_xboole_0,A_65) = A_65 ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_8])).

tff(c_211,plain,(
    ! [B_80] : k4_xboole_0(k1_xboole_0,B_80) = k3_xboole_0(k1_xboole_0,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_81])).

tff(c_223,plain,(
    ! [B_80] : k3_xboole_0(k1_xboole_0,B_80) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_211])).

tff(c_277,plain,(
    ! [A_87] :
      ( k7_relat_1(k1_xboole_0,A_87) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_270,c_223])).

tff(c_290,plain,(
    ! [A_87] : k7_relat_1(k1_xboole_0,A_87) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_277])).

tff(c_38,plain,(
    k7_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_296,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_290,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:18:12 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.36/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.43  
% 2.36/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.43  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.36/1.43  
% 2.36/1.43  %Foreground sorts:
% 2.36/1.43  
% 2.36/1.43  
% 2.36/1.43  %Background operators:
% 2.36/1.43  
% 2.36/1.43  
% 2.36/1.43  %Foreground operators:
% 2.36/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.36/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.36/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.36/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.36/1.43  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.36/1.43  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.36/1.43  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.36/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.36/1.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.36/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.36/1.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.36/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.36/1.43  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.36/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.36/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.36/1.43  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.36/1.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.36/1.43  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.36/1.43  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.36/1.43  tff('#skF_4', type, '#skF_4': $i).
% 2.36/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.36/1.43  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.36/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.36/1.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.36/1.43  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.36/1.43  
% 2.36/1.44  tff(f_66, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 2.36/1.44  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.36/1.44  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.36/1.44  tff(f_70, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k3_xboole_0(B, k2_zfmisc_1(A, k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t96_relat_1)).
% 2.36/1.44  tff(f_31, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.36/1.44  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.36/1.44  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 2.36/1.44  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.36/1.44  tff(f_73, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 2.36/1.44  tff(c_34, plain, (![A_40]: (r2_hidden('#skF_1'(A_40), A_40) | v1_relat_1(A_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.36/1.44  tff(c_10, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.36/1.44  tff(c_183, plain, (![A_74, B_75]: (~r2_hidden(A_74, B_75) | ~r1_xboole_0(k1_tarski(A_74), B_75))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.36/1.44  tff(c_198, plain, (![A_78]: (~r2_hidden(A_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_183])).
% 2.36/1.44  tff(c_203, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_34, c_198])).
% 2.36/1.44  tff(c_270, plain, (![B_86, A_87]: (k3_xboole_0(B_86, k2_zfmisc_1(A_87, k2_relat_1(B_86)))=k7_relat_1(B_86, A_87) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.36/1.44  tff(c_6, plain, (![A_5]: (k4_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.36/1.44  tff(c_204, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.36/1.44  tff(c_65, plain, (![B_64, A_65]: (k5_xboole_0(B_64, A_65)=k5_xboole_0(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.36/1.44  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.36/1.44  tff(c_81, plain, (![A_65]: (k5_xboole_0(k1_xboole_0, A_65)=A_65)), inference(superposition, [status(thm), theory('equality')], [c_65, c_8])).
% 2.36/1.44  tff(c_211, plain, (![B_80]: (k4_xboole_0(k1_xboole_0, B_80)=k3_xboole_0(k1_xboole_0, B_80))), inference(superposition, [status(thm), theory('equality')], [c_204, c_81])).
% 2.36/1.44  tff(c_223, plain, (![B_80]: (k3_xboole_0(k1_xboole_0, B_80)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_211])).
% 2.36/1.44  tff(c_277, plain, (![A_87]: (k7_relat_1(k1_xboole_0, A_87)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_270, c_223])).
% 2.36/1.44  tff(c_290, plain, (![A_87]: (k7_relat_1(k1_xboole_0, A_87)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_277])).
% 2.36/1.44  tff(c_38, plain, (k7_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.36/1.44  tff(c_296, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_290, c_38])).
% 2.36/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.36/1.44  
% 2.36/1.44  Inference rules
% 2.36/1.44  ----------------------
% 2.36/1.44  #Ref     : 0
% 2.36/1.44  #Sup     : 57
% 2.36/1.44  #Fact    : 0
% 2.36/1.44  #Define  : 0
% 2.36/1.44  #Split   : 0
% 2.36/1.44  #Chain   : 0
% 2.36/1.44  #Close   : 0
% 2.36/1.44  
% 2.36/1.44  Ordering : KBO
% 2.36/1.44  
% 2.36/1.44  Simplification rules
% 2.36/1.44  ----------------------
% 2.36/1.44  #Subsume      : 0
% 2.36/1.44  #Demod        : 22
% 2.36/1.44  #Tautology    : 48
% 2.36/1.45  #SimpNegUnit  : 0
% 2.36/1.45  #BackRed      : 1
% 2.36/1.45  
% 2.36/1.45  #Partial instantiations: 0
% 2.36/1.45  #Strategies tried      : 1
% 2.36/1.45  
% 2.36/1.45  Timing (in seconds)
% 2.36/1.45  ----------------------
% 2.36/1.45  Preprocessing        : 0.41
% 2.36/1.45  Parsing              : 0.22
% 2.36/1.45  CNF conversion       : 0.02
% 2.36/1.45  Main loop            : 0.19
% 2.36/1.45  Inferencing          : 0.08
% 2.36/1.45  Reduction            : 0.07
% 2.36/1.45  Demodulation         : 0.05
% 2.36/1.45  BG Simplification    : 0.02
% 2.36/1.45  Subsumption          : 0.02
% 2.36/1.45  Abstraction          : 0.02
% 2.36/1.45  MUC search           : 0.00
% 2.36/1.45  Cooper               : 0.00
% 2.36/1.45  Total                : 0.64
% 2.36/1.45  Index Insertion      : 0.00
% 2.36/1.45  Index Deletion       : 0.00
% 2.36/1.45  Index Matching       : 0.00
% 2.36/1.45  BG Taut test         : 0.00
%------------------------------------------------------------------------------
