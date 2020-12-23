%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 32.23s
% Output     : CNFRefutation 32.23s
% Verified   : 
% Statistics : Number of formulae       :   44 (  51 expanded)
%              Number of leaves         :   28 (  32 expanded)
%              Depth                    :    6
%              Number of atoms          :   44 (  52 expanded)
%              Number of equality atoms :   17 (  24 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_46,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_521,plain,(
    ! [B_95,A_96] :
      ( k7_relat_1(B_95,A_96) = B_95
      | ~ r1_tarski(k1_relat_1(B_95),A_96)
      | ~ v1_relat_1(B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_526,plain,(
    ! [B_95] :
      ( k7_relat_1(B_95,k1_relat_1(B_95)) = B_95
      | ~ v1_relat_1(B_95) ) ),
    inference(resolution,[status(thm)],[c_8,c_521])).

tff(c_30,plain,(
    ! [A_40,B_41] : k6_subset_1(A_40,B_41) = k4_xboole_0(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    ! [C_48,A_46,B_47] :
      ( k6_subset_1(k7_relat_1(C_48,A_46),k7_relat_1(C_48,B_47)) = k7_relat_1(C_48,k6_subset_1(A_46,B_47))
      | ~ v1_relat_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_1262,plain,(
    ! [C_131,A_132,B_133] :
      ( k4_xboole_0(k7_relat_1(C_131,A_132),k7_relat_1(C_131,B_133)) = k7_relat_1(C_131,k4_xboole_0(A_132,B_133))
      | ~ v1_relat_1(C_131) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_36])).

tff(c_12249,plain,(
    ! [B_277,B_278] :
      ( k7_relat_1(B_277,k4_xboole_0(k1_relat_1(B_277),B_278)) = k4_xboole_0(B_277,k7_relat_1(B_277,B_278))
      | ~ v1_relat_1(B_277)
      | ~ v1_relat_1(B_277) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_526,c_1262])).

tff(c_16,plain,(
    ! [A_11,B_12] : r1_tarski(k4_xboole_0(A_11,B_12),A_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_771,plain,(
    ! [B_110,A_111] :
      ( k1_relat_1(k7_relat_1(B_110,A_111)) = A_111
      | ~ r1_tarski(A_111,k1_relat_1(B_110))
      | ~ v1_relat_1(B_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_794,plain,(
    ! [B_110,B_12] :
      ( k1_relat_1(k7_relat_1(B_110,k4_xboole_0(k1_relat_1(B_110),B_12))) = k4_xboole_0(k1_relat_1(B_110),B_12)
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_16,c_771])).

tff(c_80442,plain,(
    ! [B_572,B_573] :
      ( k1_relat_1(k4_xboole_0(B_572,k7_relat_1(B_572,B_573))) = k4_xboole_0(k1_relat_1(B_572),B_573)
      | ~ v1_relat_1(B_572)
      | ~ v1_relat_1(B_572)
      | ~ v1_relat_1(B_572) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12249,c_794])).

tff(c_44,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_47,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_30,c_44])).

tff(c_80910,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_80442,c_47])).

tff(c_80960,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_80910])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:27:31 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 32.23/21.79  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.23/21.79  
% 32.23/21.79  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.23/21.80  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 32.23/21.80  
% 32.23/21.80  %Foreground sorts:
% 32.23/21.80  
% 32.23/21.80  
% 32.23/21.80  %Background operators:
% 32.23/21.80  
% 32.23/21.80  
% 32.23/21.80  %Foreground operators:
% 32.23/21.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 32.23/21.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 32.23/21.80  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 32.23/21.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 32.23/21.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 32.23/21.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 32.23/21.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 32.23/21.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 32.23/21.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 32.23/21.80  tff('#skF_2', type, '#skF_2': $i).
% 32.23/21.80  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 32.23/21.80  tff('#skF_1', type, '#skF_1': $i).
% 32.23/21.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 32.23/21.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 32.23/21.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 32.23/21.80  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 32.23/21.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 32.23/21.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 32.23/21.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 32.23/21.80  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 32.23/21.80  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 32.23/21.80  
% 32.23/21.81  tff(f_88, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 32.23/21.81  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 32.23/21.81  tff(f_83, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 32.23/21.81  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 32.23/21.81  tff(f_67, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 32.23/21.81  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 32.23/21.81  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 32.23/21.81  tff(c_46, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 32.23/21.81  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 32.23/21.81  tff(c_521, plain, (![B_95, A_96]: (k7_relat_1(B_95, A_96)=B_95 | ~r1_tarski(k1_relat_1(B_95), A_96) | ~v1_relat_1(B_95))), inference(cnfTransformation, [status(thm)], [f_83])).
% 32.23/21.81  tff(c_526, plain, (![B_95]: (k7_relat_1(B_95, k1_relat_1(B_95))=B_95 | ~v1_relat_1(B_95))), inference(resolution, [status(thm)], [c_8, c_521])).
% 32.23/21.81  tff(c_30, plain, (![A_40, B_41]: (k6_subset_1(A_40, B_41)=k4_xboole_0(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_57])).
% 32.23/21.81  tff(c_36, plain, (![C_48, A_46, B_47]: (k6_subset_1(k7_relat_1(C_48, A_46), k7_relat_1(C_48, B_47))=k7_relat_1(C_48, k6_subset_1(A_46, B_47)) | ~v1_relat_1(C_48))), inference(cnfTransformation, [status(thm)], [f_67])).
% 32.23/21.81  tff(c_1262, plain, (![C_131, A_132, B_133]: (k4_xboole_0(k7_relat_1(C_131, A_132), k7_relat_1(C_131, B_133))=k7_relat_1(C_131, k4_xboole_0(A_132, B_133)) | ~v1_relat_1(C_131))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_36])).
% 32.23/21.81  tff(c_12249, plain, (![B_277, B_278]: (k7_relat_1(B_277, k4_xboole_0(k1_relat_1(B_277), B_278))=k4_xboole_0(B_277, k7_relat_1(B_277, B_278)) | ~v1_relat_1(B_277) | ~v1_relat_1(B_277))), inference(superposition, [status(thm), theory('equality')], [c_526, c_1262])).
% 32.23/21.81  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(k4_xboole_0(A_11, B_12), A_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 32.23/21.81  tff(c_771, plain, (![B_110, A_111]: (k1_relat_1(k7_relat_1(B_110, A_111))=A_111 | ~r1_tarski(A_111, k1_relat_1(B_110)) | ~v1_relat_1(B_110))), inference(cnfTransformation, [status(thm)], [f_77])).
% 32.23/21.81  tff(c_794, plain, (![B_110, B_12]: (k1_relat_1(k7_relat_1(B_110, k4_xboole_0(k1_relat_1(B_110), B_12)))=k4_xboole_0(k1_relat_1(B_110), B_12) | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_16, c_771])).
% 32.23/21.81  tff(c_80442, plain, (![B_572, B_573]: (k1_relat_1(k4_xboole_0(B_572, k7_relat_1(B_572, B_573)))=k4_xboole_0(k1_relat_1(B_572), B_573) | ~v1_relat_1(B_572) | ~v1_relat_1(B_572) | ~v1_relat_1(B_572))), inference(superposition, [status(thm), theory('equality')], [c_12249, c_794])).
% 32.23/21.81  tff(c_44, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 32.23/21.81  tff(c_47, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_30, c_44])).
% 32.23/21.81  tff(c_80910, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_80442, c_47])).
% 32.23/21.81  tff(c_80960, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_46, c_80910])).
% 32.23/21.81  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 32.23/21.81  
% 32.23/21.81  Inference rules
% 32.23/21.81  ----------------------
% 32.23/21.81  #Ref     : 0
% 32.23/21.81  #Sup     : 21805
% 32.23/21.81  #Fact    : 0
% 32.23/21.81  #Define  : 0
% 32.23/21.81  #Split   : 0
% 32.23/21.81  #Chain   : 0
% 32.23/21.81  #Close   : 0
% 32.23/21.81  
% 32.23/21.81  Ordering : KBO
% 32.23/21.81  
% 32.23/21.81  Simplification rules
% 32.23/21.81  ----------------------
% 32.23/21.81  #Subsume      : 2766
% 32.23/21.81  #Demod        : 30877
% 32.23/21.81  #Tautology    : 4336
% 32.23/21.81  #SimpNegUnit  : 0
% 32.23/21.81  #BackRed      : 2
% 32.23/21.81  
% 32.23/21.81  #Partial instantiations: 0
% 32.23/21.81  #Strategies tried      : 1
% 32.23/21.81  
% 32.23/21.81  Timing (in seconds)
% 32.23/21.81  ----------------------
% 32.23/21.81  Preprocessing        : 0.32
% 32.23/21.81  Parsing              : 0.17
% 32.23/21.81  CNF conversion       : 0.02
% 32.23/21.81  Main loop            : 20.72
% 32.23/21.81  Inferencing          : 2.30
% 32.23/21.81  Reduction            : 12.58
% 32.23/21.81  Demodulation         : 11.76
% 32.23/21.81  BG Simplification    : 0.46
% 32.23/21.81  Subsumption          : 4.78
% 32.23/21.81  Abstraction          : 0.90
% 32.23/21.81  MUC search           : 0.00
% 32.23/21.81  Cooper               : 0.00
% 32.23/21.81  Total                : 21.07
% 32.23/21.81  Index Insertion      : 0.00
% 32.23/21.81  Index Deletion       : 0.00
% 32.23/21.81  Index Matching       : 0.00
% 32.23/21.81  BG Taut test         : 0.00
%------------------------------------------------------------------------------
