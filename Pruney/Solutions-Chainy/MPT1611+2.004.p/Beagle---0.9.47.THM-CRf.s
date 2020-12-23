%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:32 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   24 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  43 expanded)
%              Number of equality atoms :   16 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_42,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_63,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_61,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_66,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_14,plain,(
    ! [A_8] : ~ v1_xboole_0(k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_7] : k3_tarski(k1_zfmisc_1(A_7)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_22,plain,(
    ! [A_13] : k9_setfam_1(A_13) = k1_zfmisc_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_26,plain,(
    ! [A_15] : k2_yellow_1(k9_setfam_1(A_15)) = k3_yellow_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_29,plain,(
    ! [A_15] : k2_yellow_1(k1_zfmisc_1(A_15)) = k3_yellow_1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_26])).

tff(c_20,plain,(
    ! [A_11,B_12] :
      ( m1_subset_1(A_11,k1_zfmisc_1(B_12))
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_16,plain,(
    ! [A_9,B_10] :
      ( r2_hidden(A_9,B_10)
      | v1_xboole_0(B_10)
      | ~ m1_subset_1(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_84,plain,(
    ! [A_32] :
      ( k4_yellow_0(k2_yellow_1(A_32)) = k3_tarski(A_32)
      | ~ r2_hidden(k3_tarski(A_32),A_32)
      | v1_xboole_0(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_111,plain,(
    ! [B_35] :
      ( k4_yellow_0(k2_yellow_1(B_35)) = k3_tarski(B_35)
      | v1_xboole_0(B_35)
      | ~ m1_subset_1(k3_tarski(B_35),B_35) ) ),
    inference(resolution,[status(thm)],[c_16,c_84])).

tff(c_115,plain,(
    ! [B_12] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(B_12))) = k3_tarski(k1_zfmisc_1(B_12))
      | v1_xboole_0(k1_zfmisc_1(B_12))
      | ~ r1_tarski(k3_tarski(k1_zfmisc_1(B_12)),B_12) ) ),
    inference(resolution,[status(thm)],[c_20,c_111])).

tff(c_121,plain,(
    ! [B_12] :
      ( k4_yellow_0(k3_yellow_1(B_12)) = B_12
      | v1_xboole_0(k1_zfmisc_1(B_12)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_29,c_12,c_115])).

tff(c_122,plain,(
    ! [B_12] : k4_yellow_0(k3_yellow_1(B_12)) = B_12 ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_121])).

tff(c_28,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_122,c_28])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.26  
% 1.92/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.26  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > #skF_1 > #skF_2
% 2.01/1.26  
% 2.01/1.26  %Foreground sorts:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Background operators:
% 2.01/1.26  
% 2.01/1.26  
% 2.01/1.26  %Foreground operators:
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.26  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.01/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.01/1.26  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.01/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.26  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.01/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.01/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.26  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.01/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.01/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.01/1.26  
% 2.01/1.27  tff(f_42, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.01/1.27  tff(f_37, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.01/1.27  tff(f_39, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.01/1.27  tff(f_54, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.01/1.27  tff(f_63, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.01/1.27  tff(f_52, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.01/1.27  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.01/1.27  tff(f_61, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.01/1.27  tff(f_66, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.01/1.27  tff(c_14, plain, (![A_8]: (~v1_xboole_0(k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.01/1.27  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.01/1.27  tff(c_12, plain, (![A_7]: (k3_tarski(k1_zfmisc_1(A_7))=A_7)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.01/1.27  tff(c_22, plain, (![A_13]: (k9_setfam_1(A_13)=k1_zfmisc_1(A_13))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.01/1.27  tff(c_26, plain, (![A_15]: (k2_yellow_1(k9_setfam_1(A_15))=k3_yellow_1(A_15))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.01/1.27  tff(c_29, plain, (![A_15]: (k2_yellow_1(k1_zfmisc_1(A_15))=k3_yellow_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_26])).
% 2.01/1.27  tff(c_20, plain, (![A_11, B_12]: (m1_subset_1(A_11, k1_zfmisc_1(B_12)) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.01/1.27  tff(c_16, plain, (![A_9, B_10]: (r2_hidden(A_9, B_10) | v1_xboole_0(B_10) | ~m1_subset_1(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.27  tff(c_84, plain, (![A_32]: (k4_yellow_0(k2_yellow_1(A_32))=k3_tarski(A_32) | ~r2_hidden(k3_tarski(A_32), A_32) | v1_xboole_0(A_32))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.01/1.27  tff(c_111, plain, (![B_35]: (k4_yellow_0(k2_yellow_1(B_35))=k3_tarski(B_35) | v1_xboole_0(B_35) | ~m1_subset_1(k3_tarski(B_35), B_35))), inference(resolution, [status(thm)], [c_16, c_84])).
% 2.01/1.27  tff(c_115, plain, (![B_12]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(B_12)))=k3_tarski(k1_zfmisc_1(B_12)) | v1_xboole_0(k1_zfmisc_1(B_12)) | ~r1_tarski(k3_tarski(k1_zfmisc_1(B_12)), B_12))), inference(resolution, [status(thm)], [c_20, c_111])).
% 2.01/1.27  tff(c_121, plain, (![B_12]: (k4_yellow_0(k3_yellow_1(B_12))=B_12 | v1_xboole_0(k1_zfmisc_1(B_12)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_29, c_12, c_115])).
% 2.01/1.27  tff(c_122, plain, (![B_12]: (k4_yellow_0(k3_yellow_1(B_12))=B_12)), inference(negUnitSimplification, [status(thm)], [c_14, c_121])).
% 2.01/1.27  tff(c_28, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.01/1.27  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_122, c_28])).
% 2.01/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.01/1.27  
% 2.01/1.27  Inference rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Ref     : 0
% 2.01/1.27  #Sup     : 16
% 2.01/1.27  #Fact    : 0
% 2.01/1.27  #Define  : 0
% 2.01/1.27  #Split   : 0
% 2.01/1.27  #Chain   : 0
% 2.01/1.27  #Close   : 0
% 2.01/1.27  
% 2.01/1.27  Ordering : KBO
% 2.01/1.27  
% 2.01/1.27  Simplification rules
% 2.01/1.27  ----------------------
% 2.01/1.27  #Subsume      : 1
% 2.01/1.27  #Demod        : 15
% 2.01/1.27  #Tautology    : 13
% 2.01/1.27  #SimpNegUnit  : 4
% 2.01/1.27  #BackRed      : 1
% 2.01/1.27  
% 2.01/1.27  #Partial instantiations: 0
% 2.01/1.27  #Strategies tried      : 1
% 2.01/1.27  
% 2.01/1.27  Timing (in seconds)
% 2.01/1.27  ----------------------
% 2.01/1.27  Preprocessing        : 0.34
% 2.01/1.27  Parsing              : 0.17
% 2.01/1.27  CNF conversion       : 0.02
% 2.01/1.28  Main loop            : 0.11
% 2.01/1.28  Inferencing          : 0.04
% 2.01/1.28  Reduction            : 0.04
% 2.01/1.28  Demodulation         : 0.03
% 2.01/1.28  BG Simplification    : 0.01
% 2.01/1.28  Subsumption          : 0.02
% 2.01/1.28  Abstraction          : 0.01
% 2.01/1.28  MUC search           : 0.00
% 2.01/1.28  Cooper               : 0.00
% 2.01/1.28  Total                : 0.48
% 2.01/1.28  Index Insertion      : 0.00
% 2.01/1.28  Index Deletion       : 0.00
% 2.01/1.28  Index Matching       : 0.00
% 2.01/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
