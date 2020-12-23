%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   45 (  54 expanded)
%              Number of leaves         :   27 (  31 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  49 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_45,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(A,k1_zfmisc_1(k3_tarski(A))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_58,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_47,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_18,plain,(
    ! [A_14] : k3_tarski(k1_tarski(A_14)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(A_13,k1_zfmisc_1(k3_tarski(A_13))) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_100,plain,(
    ! [A_34,B_35] :
      ( r2_hidden(A_34,B_35)
      | ~ r1_tarski(k1_tarski(A_34),B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_110,plain,(
    ! [A_34] : r2_hidden(A_34,k1_zfmisc_1(k3_tarski(k1_tarski(A_34)))) ),
    inference(resolution,[status(thm)],[c_16,c_100])).

tff(c_115,plain,(
    ! [A_36] : r2_hidden(A_36,k1_zfmisc_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_119,plain,(
    ! [A_36] : ~ v1_xboole_0(k1_zfmisc_1(A_36)) ),
    inference(resolution,[status(thm)],[c_115,c_2])).

tff(c_114,plain,(
    ! [A_34] : r2_hidden(A_34,k1_zfmisc_1(A_34)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_110])).

tff(c_22,plain,(
    ! [A_16] : k9_setfam_1(A_16) = k1_zfmisc_1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    ! [A_18] : k2_yellow_1(k9_setfam_1(A_18)) = k3_yellow_1(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_29,plain,(
    ! [A_18] : k2_yellow_1(k1_zfmisc_1(A_18)) = k3_yellow_1(A_18) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_20,plain,(
    ! [A_15] : k3_tarski(k1_zfmisc_1(A_15)) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_131,plain,(
    ! [A_41] :
      ( k4_yellow_0(k2_yellow_1(A_41)) = k3_tarski(A_41)
      | ~ r2_hidden(k3_tarski(A_41),A_41)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_137,plain,(
    ! [A_15] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_15))) = k3_tarski(k1_zfmisc_1(A_15))
      | ~ r2_hidden(A_15,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_131])).

tff(c_140,plain,(
    ! [A_15] :
      ( k4_yellow_0(k3_yellow_1(A_15)) = A_15
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_29,c_20,c_137])).

tff(c_141,plain,(
    ! [A_15] : k4_yellow_0(k3_yellow_1(A_15)) = A_15 ),
    inference(negUnitSimplification,[status(thm)],[c_119,c_140])).

tff(c_28,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:42:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.58  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.58  
% 2.13/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.59  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2
% 2.13/1.59  
% 2.13/1.59  %Foreground sorts:
% 2.13/1.59  
% 2.13/1.59  
% 2.13/1.59  %Background operators:
% 2.13/1.59  
% 2.13/1.59  
% 2.13/1.59  %Foreground operators:
% 2.13/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.13/1.59  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.13/1.59  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.59  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.13/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.59  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.13/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.59  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.59  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.59  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.13/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.59  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.59  
% 2.13/1.60  tff(f_45, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 2.13/1.60  tff(f_43, axiom, (![A]: r1_tarski(A, k1_zfmisc_1(k3_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_zfmisc_1)).
% 2.13/1.60  tff(f_41, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.13/1.60  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.13/1.60  tff(f_49, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.13/1.60  tff(f_58, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.13/1.60  tff(f_47, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.13/1.60  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.13/1.60  tff(f_61, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.13/1.60  tff(c_18, plain, (![A_14]: (k3_tarski(k1_tarski(A_14))=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.13/1.60  tff(c_16, plain, (![A_13]: (r1_tarski(A_13, k1_zfmisc_1(k3_tarski(A_13))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.60  tff(c_100, plain, (![A_34, B_35]: (r2_hidden(A_34, B_35) | ~r1_tarski(k1_tarski(A_34), B_35))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.13/1.60  tff(c_110, plain, (![A_34]: (r2_hidden(A_34, k1_zfmisc_1(k3_tarski(k1_tarski(A_34)))))), inference(resolution, [status(thm)], [c_16, c_100])).
% 2.13/1.60  tff(c_115, plain, (![A_36]: (r2_hidden(A_36, k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_110])).
% 2.13/1.60  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.13/1.60  tff(c_119, plain, (![A_36]: (~v1_xboole_0(k1_zfmisc_1(A_36)))), inference(resolution, [status(thm)], [c_115, c_2])).
% 2.13/1.60  tff(c_114, plain, (![A_34]: (r2_hidden(A_34, k1_zfmisc_1(A_34)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_110])).
% 2.13/1.60  tff(c_22, plain, (![A_16]: (k9_setfam_1(A_16)=k1_zfmisc_1(A_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.60  tff(c_26, plain, (![A_18]: (k2_yellow_1(k9_setfam_1(A_18))=k3_yellow_1(A_18))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.60  tff(c_29, plain, (![A_18]: (k2_yellow_1(k1_zfmisc_1(A_18))=k3_yellow_1(A_18))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 2.13/1.60  tff(c_20, plain, (![A_15]: (k3_tarski(k1_zfmisc_1(A_15))=A_15)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.13/1.60  tff(c_131, plain, (![A_41]: (k4_yellow_0(k2_yellow_1(A_41))=k3_tarski(A_41) | ~r2_hidden(k3_tarski(A_41), A_41) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.13/1.60  tff(c_137, plain, (![A_15]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_15)))=k3_tarski(k1_zfmisc_1(A_15)) | ~r2_hidden(A_15, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_131])).
% 2.13/1.60  tff(c_140, plain, (![A_15]: (k4_yellow_0(k3_yellow_1(A_15))=A_15 | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_29, c_20, c_137])).
% 2.13/1.60  tff(c_141, plain, (![A_15]: (k4_yellow_0(k3_yellow_1(A_15))=A_15)), inference(negUnitSimplification, [status(thm)], [c_119, c_140])).
% 2.13/1.60  tff(c_28, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.13/1.60  tff(c_144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_141, c_28])).
% 2.13/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.60  
% 2.13/1.60  Inference rules
% 2.13/1.60  ----------------------
% 2.13/1.60  #Ref     : 0
% 2.13/1.60  #Sup     : 23
% 2.13/1.60  #Fact    : 0
% 2.13/1.60  #Define  : 0
% 2.13/1.60  #Split   : 0
% 2.13/1.60  #Chain   : 0
% 2.13/1.60  #Close   : 0
% 2.13/1.60  
% 2.13/1.60  Ordering : KBO
% 2.13/1.60  
% 2.13/1.60  Simplification rules
% 2.13/1.60  ----------------------
% 2.13/1.60  #Subsume      : 0
% 2.13/1.60  #Demod        : 8
% 2.13/1.60  #Tautology    : 17
% 2.13/1.60  #SimpNegUnit  : 1
% 2.13/1.60  #BackRed      : 1
% 2.13/1.60  
% 2.13/1.60  #Partial instantiations: 0
% 2.13/1.60  #Strategies tried      : 1
% 2.13/1.60  
% 2.13/1.60  Timing (in seconds)
% 2.13/1.60  ----------------------
% 2.13/1.61  Preprocessing        : 0.44
% 2.13/1.61  Parsing              : 0.23
% 2.13/1.61  CNF conversion       : 0.03
% 2.13/1.61  Main loop            : 0.19
% 2.13/1.61  Inferencing          : 0.08
% 2.13/1.61  Reduction            : 0.06
% 2.13/1.61  Demodulation         : 0.05
% 2.13/1.61  BG Simplification    : 0.02
% 2.13/1.61  Subsumption          : 0.02
% 2.13/1.61  Abstraction          : 0.02
% 2.13/1.61  MUC search           : 0.00
% 2.13/1.61  Cooper               : 0.00
% 2.13/1.61  Total                : 0.68
% 2.13/1.61  Index Insertion      : 0.00
% 2.13/1.61  Index Deletion       : 0.00
% 2.13/1.61  Index Matching       : 0.00
% 2.13/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
