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
% DateTime   : Thu Dec  3 10:02:29 EST 2020

% Result     : Theorem 3.16s
% Output     : CNFRefutation 3.16s
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

tff(f_82,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => k1_relat_1(k6_subset_1(B,k7_relat_1(B,A))) = k6_subset_1(k1_relat_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t212_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k7_relat_1(B,A) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t97_relat_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(C,k6_subset_1(A,B)) = k6_subset_1(k7_relat_1(C,A),k7_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t109_relat_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_264,plain,(
    ! [B_81,A_82] :
      ( k7_relat_1(B_81,A_82) = B_81
      | ~ r1_tarski(k1_relat_1(B_81),A_82)
      | ~ v1_relat_1(B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_269,plain,(
    ! [B_81] :
      ( k7_relat_1(B_81,k1_relat_1(B_81)) = B_81
      | ~ v1_relat_1(B_81) ) ),
    inference(resolution,[status(thm)],[c_6,c_264])).

tff(c_26,plain,(
    ! [A_36,B_37] : k6_subset_1(A_36,B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_32,plain,(
    ! [C_44,A_42,B_43] :
      ( k6_subset_1(k7_relat_1(C_44,A_42),k7_relat_1(C_44,B_43)) = k7_relat_1(C_44,k6_subset_1(A_42,B_43))
      | ~ v1_relat_1(C_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_470,plain,(
    ! [C_104,A_105,B_106] :
      ( k4_xboole_0(k7_relat_1(C_104,A_105),k7_relat_1(C_104,B_106)) = k7_relat_1(C_104,k4_xboole_0(A_105,B_106))
      | ~ v1_relat_1(C_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_32])).

tff(c_782,plain,(
    ! [B_135,B_136] :
      ( k7_relat_1(B_135,k4_xboole_0(k1_relat_1(B_135),B_136)) = k4_xboole_0(B_135,k7_relat_1(B_135,B_136))
      | ~ v1_relat_1(B_135)
      | ~ v1_relat_1(B_135) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_470])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_319,plain,(
    ! [B_86,A_87] :
      ( k1_relat_1(k7_relat_1(B_86,A_87)) = A_87
      | ~ r1_tarski(A_87,k1_relat_1(B_86))
      | ~ v1_relat_1(B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_328,plain,(
    ! [B_86,B_6] :
      ( k1_relat_1(k7_relat_1(B_86,k4_xboole_0(k1_relat_1(B_86),B_6))) = k4_xboole_0(k1_relat_1(B_86),B_6)
      | ~ v1_relat_1(B_86) ) ),
    inference(resolution,[status(thm)],[c_10,c_319])).

tff(c_909,plain,(
    ! [B_142,B_143] :
      ( k1_relat_1(k4_xboole_0(B_142,k7_relat_1(B_142,B_143))) = k4_xboole_0(k1_relat_1(B_142),B_143)
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(B_142)
      | ~ v1_relat_1(B_142) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_782,c_328])).

tff(c_40,plain,(
    k1_relat_1(k6_subset_1('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k6_subset_1(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_43,plain,(
    k1_relat_1(k4_xboole_0('#skF_2',k7_relat_1('#skF_2','#skF_1'))) != k4_xboole_0(k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_26,c_40])).

tff(c_969,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_909,c_43])).

tff(c_986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_969])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 15:41:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.16/1.51  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  
% 3.16/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.51  %$ r1_tarski > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k7_relat_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.16/1.51  
% 3.16/1.51  %Foreground sorts:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Background operators:
% 3.16/1.51  
% 3.16/1.51  
% 3.16/1.51  %Foreground operators:
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.16/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 3.16/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.16/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.16/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.16/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.16/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.16/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.16/1.51  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.16/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.16/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.16/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.16/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.16/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.16/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.16/1.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.16/1.51  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.16/1.51  
% 3.16/1.52  tff(f_82, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (k1_relat_1(k6_subset_1(B, k7_relat_1(B, A))) = k6_subset_1(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t212_relat_1)).
% 3.16/1.52  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.16/1.52  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k7_relat_1(B, A) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t97_relat_1)).
% 3.16/1.52  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.16/1.52  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(C, k6_subset_1(A, B)) = k6_subset_1(k7_relat_1(C, A), k7_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t109_relat_1)).
% 3.16/1.52  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.16/1.52  tff(f_71, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 3.16/1.52  tff(c_42, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.52  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.16/1.52  tff(c_264, plain, (![B_81, A_82]: (k7_relat_1(B_81, A_82)=B_81 | ~r1_tarski(k1_relat_1(B_81), A_82) | ~v1_relat_1(B_81))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.16/1.52  tff(c_269, plain, (![B_81]: (k7_relat_1(B_81, k1_relat_1(B_81))=B_81 | ~v1_relat_1(B_81))), inference(resolution, [status(thm)], [c_6, c_264])).
% 3.16/1.52  tff(c_26, plain, (![A_36, B_37]: (k6_subset_1(A_36, B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.16/1.52  tff(c_32, plain, (![C_44, A_42, B_43]: (k6_subset_1(k7_relat_1(C_44, A_42), k7_relat_1(C_44, B_43))=k7_relat_1(C_44, k6_subset_1(A_42, B_43)) | ~v1_relat_1(C_44))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.16/1.52  tff(c_470, plain, (![C_104, A_105, B_106]: (k4_xboole_0(k7_relat_1(C_104, A_105), k7_relat_1(C_104, B_106))=k7_relat_1(C_104, k4_xboole_0(A_105, B_106)) | ~v1_relat_1(C_104))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_32])).
% 3.16/1.52  tff(c_782, plain, (![B_135, B_136]: (k7_relat_1(B_135, k4_xboole_0(k1_relat_1(B_135), B_136))=k4_xboole_0(B_135, k7_relat_1(B_135, B_136)) | ~v1_relat_1(B_135) | ~v1_relat_1(B_135))), inference(superposition, [status(thm), theory('equality')], [c_269, c_470])).
% 3.16/1.52  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.16/1.52  tff(c_319, plain, (![B_86, A_87]: (k1_relat_1(k7_relat_1(B_86, A_87))=A_87 | ~r1_tarski(A_87, k1_relat_1(B_86)) | ~v1_relat_1(B_86))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.16/1.52  tff(c_328, plain, (![B_86, B_6]: (k1_relat_1(k7_relat_1(B_86, k4_xboole_0(k1_relat_1(B_86), B_6)))=k4_xboole_0(k1_relat_1(B_86), B_6) | ~v1_relat_1(B_86))), inference(resolution, [status(thm)], [c_10, c_319])).
% 3.16/1.52  tff(c_909, plain, (![B_142, B_143]: (k1_relat_1(k4_xboole_0(B_142, k7_relat_1(B_142, B_143)))=k4_xboole_0(k1_relat_1(B_142), B_143) | ~v1_relat_1(B_142) | ~v1_relat_1(B_142) | ~v1_relat_1(B_142))), inference(superposition, [status(thm), theory('equality')], [c_782, c_328])).
% 3.16/1.52  tff(c_40, plain, (k1_relat_1(k6_subset_1('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k6_subset_1(k1_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.16/1.52  tff(c_43, plain, (k1_relat_1(k4_xboole_0('#skF_2', k7_relat_1('#skF_2', '#skF_1')))!=k4_xboole_0(k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_26, c_40])).
% 3.16/1.52  tff(c_969, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_909, c_43])).
% 3.16/1.52  tff(c_986, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_969])).
% 3.16/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.16/1.52  
% 3.16/1.52  Inference rules
% 3.16/1.52  ----------------------
% 3.16/1.52  #Ref     : 0
% 3.16/1.52  #Sup     : 261
% 3.16/1.52  #Fact    : 0
% 3.16/1.52  #Define  : 0
% 3.16/1.52  #Split   : 0
% 3.16/1.52  #Chain   : 0
% 3.16/1.52  #Close   : 0
% 3.16/1.52  
% 3.16/1.52  Ordering : KBO
% 3.16/1.52  
% 3.16/1.52  Simplification rules
% 3.16/1.52  ----------------------
% 3.16/1.52  #Subsume      : 20
% 3.16/1.52  #Demod        : 17
% 3.16/1.52  #Tautology    : 87
% 3.16/1.52  #SimpNegUnit  : 0
% 3.16/1.52  #BackRed      : 0
% 3.16/1.52  
% 3.16/1.52  #Partial instantiations: 0
% 3.16/1.52  #Strategies tried      : 1
% 3.16/1.52  
% 3.16/1.52  Timing (in seconds)
% 3.16/1.52  ----------------------
% 3.16/1.53  Preprocessing        : 0.33
% 3.16/1.53  Parsing              : 0.18
% 3.16/1.53  CNF conversion       : 0.02
% 3.16/1.53  Main loop            : 0.38
% 3.16/1.53  Inferencing          : 0.15
% 3.16/1.53  Reduction            : 0.11
% 3.16/1.53  Demodulation         : 0.08
% 3.16/1.53  BG Simplification    : 0.03
% 3.16/1.53  Subsumption          : 0.07
% 3.16/1.53  Abstraction          : 0.03
% 3.16/1.53  MUC search           : 0.00
% 3.16/1.53  Cooper               : 0.00
% 3.16/1.53  Total                : 0.73
% 3.16/1.53  Index Insertion      : 0.00
% 3.16/1.53  Index Deletion       : 0.00
% 3.16/1.53  Index Matching       : 0.00
% 3.16/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------
