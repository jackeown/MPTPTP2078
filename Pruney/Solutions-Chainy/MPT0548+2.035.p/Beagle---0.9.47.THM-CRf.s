%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 2.23s
% Output     : CNFRefutation 2.23s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 111 expanded)
%              Number of leaves         :   40 (  55 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 ( 142 expanded)
%              Number of equality atoms :   35 (  64 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_70,axiom,(
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

tff(f_31,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_79,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_72,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_82,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(c_38,plain,(
    ! [A_41] :
      ( r2_hidden('#skF_1'(A_41),A_41)
      | v1_relat_1(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_122,plain,(
    ! [A_76,B_77] :
      ( r1_tarski(k1_tarski(A_76),B_77)
      | ~ r2_hidden(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_128,plain,(
    ! [A_78] :
      ( k1_tarski(A_78) = k1_xboole_0
      | ~ r2_hidden(A_78,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_122,c_4])).

tff(c_133,plain,
    ( k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0
    | v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_38,c_128])).

tff(c_139,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_133])).

tff(c_44,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    ! [A_59] : k7_relat_1(k1_xboole_0,A_59) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_214,plain,(
    ! [B_91,A_92] :
      ( k2_relat_1(k7_relat_1(B_91,A_92)) = k9_relat_1(B_91,A_92)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_223,plain,(
    ! [A_59] :
      ( k9_relat_1(k1_xboole_0,A_59) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_214])).

tff(c_227,plain,(
    ! [A_59] : k9_relat_1(k1_xboole_0,A_59) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_44,c_223])).

tff(c_48,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_230,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_48])).

tff(c_231,plain,(
    k1_tarski('#skF_1'(k1_xboole_0)) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_133])).

tff(c_28,plain,(
    ! [B_38] : k4_xboole_0(k1_tarski(B_38),k1_tarski(B_38)) != k1_tarski(B_38) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_242,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) != k1_tarski('#skF_1'(k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_28])).

tff(c_248,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_231,c_242])).

tff(c_8,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_287,plain,(
    ! [A_97,B_98] : k3_xboole_0(k1_tarski(A_97),k2_tarski(A_97,B_98)) = k1_tarski(A_97) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_293,plain,(
    ! [A_97,B_98] : k5_xboole_0(k1_tarski(A_97),k1_tarski(A_97)) = k4_xboole_0(k1_tarski(A_97),k2_tarski(A_97,B_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_2])).

tff(c_307,plain,(
    ! [A_99,B_100] : k4_xboole_0(k1_tarski(A_99),k2_tarski(A_99,B_100)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_293])).

tff(c_321,plain,(
    ! [A_101] : k4_xboole_0(k1_tarski(A_101),k1_tarski(A_101)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_307])).

tff(c_328,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_1'(k1_xboole_0))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_231,c_321])).

tff(c_334,plain,(
    k4_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_231,c_328])).

tff(c_336,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_248,c_334])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n015.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:34:38 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.23/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  
% 2.23/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.29  %$ r2_hidden > r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k7_relat_1 > k5_xboole_0 > k4_xboole_0 > k4_tarski > k3_xboole_0 > k2_tarski > #nlpp > k2_relat_1 > k1_tarski > k1_setfam_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.23/1.29  
% 2.23/1.29  %Foreground sorts:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Background operators:
% 2.23/1.29  
% 2.23/1.29  
% 2.23/1.29  %Foreground operators:
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.23/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.23/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.23/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.23/1.29  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.23/1.29  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.23/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.23/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.23/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.23/1.29  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.23/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.23/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.23/1.29  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.23/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.23/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.23/1.29  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.23/1.29  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.23/1.29  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.23/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.23/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.23/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.23/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.23/1.29  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.23/1.29  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.23/1.29  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.23/1.29  
% 2.23/1.30  tff(f_70, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.23/1.30  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.23/1.30  tff(f_31, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.23/1.30  tff(f_79, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.23/1.30  tff(f_72, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 2.23/1.30  tff(f_76, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 2.23/1.30  tff(f_82, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 2.23/1.30  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.23/1.30  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.23/1.30  tff(f_33, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.23/1.30  tff(f_53, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.23/1.30  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.23/1.30  tff(c_38, plain, (![A_41]: (r2_hidden('#skF_1'(A_41), A_41) | v1_relat_1(A_41))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.23/1.30  tff(c_122, plain, (![A_76, B_77]: (r1_tarski(k1_tarski(A_76), B_77) | ~r2_hidden(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.23/1.30  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.23/1.30  tff(c_128, plain, (![A_78]: (k1_tarski(A_78)=k1_xboole_0 | ~r2_hidden(A_78, k1_xboole_0))), inference(resolution, [status(thm)], [c_122, c_4])).
% 2.23/1.30  tff(c_133, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0 | v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_38, c_128])).
% 2.23/1.30  tff(c_139, plain, (v1_relat_1(k1_xboole_0)), inference(splitLeft, [status(thm)], [c_133])).
% 2.23/1.30  tff(c_44, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.23/1.30  tff(c_40, plain, (![A_59]: (k7_relat_1(k1_xboole_0, A_59)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.23/1.30  tff(c_214, plain, (![B_91, A_92]: (k2_relat_1(k7_relat_1(B_91, A_92))=k9_relat_1(B_91, A_92) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.23/1.30  tff(c_223, plain, (![A_59]: (k9_relat_1(k1_xboole_0, A_59)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_40, c_214])).
% 2.23/1.30  tff(c_227, plain, (![A_59]: (k9_relat_1(k1_xboole_0, A_59)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_139, c_44, c_223])).
% 2.23/1.30  tff(c_48, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.23/1.30  tff(c_230, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_227, c_48])).
% 2.23/1.30  tff(c_231, plain, (k1_tarski('#skF_1'(k1_xboole_0))=k1_xboole_0), inference(splitRight, [status(thm)], [c_133])).
% 2.23/1.30  tff(c_28, plain, (![B_38]: (k4_xboole_0(k1_tarski(B_38), k1_tarski(B_38))!=k1_tarski(B_38))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.23/1.30  tff(c_242, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))!=k1_tarski('#skF_1'(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_231, c_28])).
% 2.23/1.30  tff(c_248, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_231, c_231, c_242])).
% 2.23/1.30  tff(c_8, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.23/1.30  tff(c_6, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.23/1.30  tff(c_287, plain, (![A_97, B_98]: (k3_xboole_0(k1_tarski(A_97), k2_tarski(A_97, B_98))=k1_tarski(A_97))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.23/1.30  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.23/1.30  tff(c_293, plain, (![A_97, B_98]: (k5_xboole_0(k1_tarski(A_97), k1_tarski(A_97))=k4_xboole_0(k1_tarski(A_97), k2_tarski(A_97, B_98)))), inference(superposition, [status(thm), theory('equality')], [c_287, c_2])).
% 2.23/1.30  tff(c_307, plain, (![A_99, B_100]: (k4_xboole_0(k1_tarski(A_99), k2_tarski(A_99, B_100))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_293])).
% 2.23/1.30  tff(c_321, plain, (![A_101]: (k4_xboole_0(k1_tarski(A_101), k1_tarski(A_101))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_307])).
% 2.23/1.30  tff(c_328, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_1'(k1_xboole_0)))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_231, c_321])).
% 2.23/1.30  tff(c_334, plain, (k4_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_231, c_328])).
% 2.23/1.30  tff(c_336, plain, $false, inference(negUnitSimplification, [status(thm)], [c_248, c_334])).
% 2.23/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.23/1.30  
% 2.23/1.30  Inference rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Ref     : 0
% 2.23/1.30  #Sup     : 69
% 2.23/1.30  #Fact    : 0
% 2.23/1.30  #Define  : 0
% 2.23/1.30  #Split   : 1
% 2.23/1.30  #Chain   : 0
% 2.23/1.30  #Close   : 0
% 2.23/1.30  
% 2.23/1.30  Ordering : KBO
% 2.23/1.30  
% 2.23/1.30  Simplification rules
% 2.23/1.30  ----------------------
% 2.23/1.30  #Subsume      : 1
% 2.23/1.30  #Demod        : 17
% 2.23/1.30  #Tautology    : 46
% 2.23/1.30  #SimpNegUnit  : 3
% 2.23/1.30  #BackRed      : 4
% 2.23/1.30  
% 2.23/1.30  #Partial instantiations: 0
% 2.23/1.30  #Strategies tried      : 1
% 2.23/1.30  
% 2.23/1.30  Timing (in seconds)
% 2.23/1.30  ----------------------
% 2.23/1.31  Preprocessing        : 0.34
% 2.23/1.31  Parsing              : 0.18
% 2.23/1.31  CNF conversion       : 0.02
% 2.23/1.31  Main loop            : 0.18
% 2.23/1.31  Inferencing          : 0.07
% 2.23/1.31  Reduction            : 0.06
% 2.23/1.31  Demodulation         : 0.04
% 2.23/1.31  BG Simplification    : 0.02
% 2.23/1.31  Subsumption          : 0.02
% 2.23/1.31  Abstraction          : 0.01
% 2.23/1.31  MUC search           : 0.00
% 2.23/1.31  Cooper               : 0.00
% 2.23/1.31  Total                : 0.55
% 2.23/1.31  Index Insertion      : 0.00
% 2.23/1.31  Index Deletion       : 0.00
% 2.23/1.31  Index Matching       : 0.00
% 2.23/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
