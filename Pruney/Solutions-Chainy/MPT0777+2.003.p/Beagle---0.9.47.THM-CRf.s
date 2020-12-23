%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:38 EST 2020

% Result     : Theorem 6.50s
% Output     : CNFRefutation 6.83s
% Verified   : 
% Statistics : Number of formulae       :   32 (  38 expanded)
%              Number of leaves         :   17 (  21 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  48 expanded)
%              Number of equality atoms :   14 (  20 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => k2_wellord1(k2_wellord1(C,A),B) = k2_wellord1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_wellord1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_29,axiom,(
    ! [A,B,C,D] : k2_zfmisc_1(k3_xboole_0(A,B),k3_xboole_0(C,D)) = k3_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t123_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_45,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,k2_zfmisc_1(B_23,B_23)) = k2_wellord1(A_22,B_23)
      | ~ v1_relat_1(A_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_8,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k3_xboole_0(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_58,plain,(
    ! [A_22,B_23] :
      ( v1_relat_1(k2_wellord1(A_22,B_23))
      | ~ v1_relat_1(A_22)
      | ~ v1_relat_1(A_22) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_8])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5,D_7] : k3_xboole_0(k2_zfmisc_1(A_4,C_6),k2_zfmisc_1(B_5,D_7)) = k2_zfmisc_1(k3_xboole_0(A_4,B_5),k3_xboole_0(C_6,D_7)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k3_xboole_0(k3_xboole_0(A_1,B_2),C_3) = k3_xboole_0(A_1,k3_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_40,B_41,C_42] :
      ( k3_xboole_0(A_40,k3_xboole_0(k2_zfmisc_1(B_41,B_41),C_42)) = k3_xboole_0(k2_wellord1(A_40,B_41),C_42)
      | ~ v1_relat_1(A_40) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_45,c_2])).

tff(c_1376,plain,(
    ! [A_159,C_160,B_161,D_162] :
      ( k3_xboole_0(A_159,k2_zfmisc_1(k3_xboole_0(C_160,B_161),k3_xboole_0(C_160,D_162))) = k3_xboole_0(k2_wellord1(A_159,C_160),k2_zfmisc_1(B_161,D_162))
      | ~ v1_relat_1(A_159) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_132])).

tff(c_10,plain,(
    ! [A_12,B_14] :
      ( k3_xboole_0(A_12,k2_zfmisc_1(B_14,B_14)) = k2_wellord1(A_12,B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1610,plain,(
    ! [A_163,C_164,D_165] :
      ( k3_xboole_0(k2_wellord1(A_163,C_164),k2_zfmisc_1(D_165,D_165)) = k2_wellord1(A_163,k3_xboole_0(C_164,D_165))
      | ~ v1_relat_1(A_163)
      | ~ v1_relat_1(A_163) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1376,c_10])).

tff(c_5284,plain,(
    ! [A_312,C_313,D_314] :
      ( k2_wellord1(k2_wellord1(A_312,C_313),D_314) = k2_wellord1(A_312,k3_xboole_0(C_313,D_314))
      | ~ v1_relat_1(k2_wellord1(A_312,C_313))
      | ~ v1_relat_1(A_312)
      | ~ v1_relat_1(A_312) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1610,c_10])).

tff(c_5320,plain,(
    ! [A_315,B_316,D_317] :
      ( k2_wellord1(k2_wellord1(A_315,B_316),D_317) = k2_wellord1(A_315,k3_xboole_0(B_316,D_317))
      | ~ v1_relat_1(A_315) ) ),
    inference(resolution,[status(thm)],[c_58,c_5284])).

tff(c_12,plain,(
    k2_wellord1(k2_wellord1('#skF_3','#skF_1'),'#skF_2') != k2_wellord1('#skF_3',k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_5447,plain,(
    ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5320,c_12])).

tff(c_5458,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_5447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n013.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:06:39 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.50/2.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.49  
% 6.50/2.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.49  %$ v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_3 > #skF_1
% 6.83/2.49  
% 6.83/2.49  %Foreground sorts:
% 6.83/2.49  
% 6.83/2.49  
% 6.83/2.49  %Background operators:
% 6.83/2.49  
% 6.83/2.49  
% 6.83/2.49  %Foreground operators:
% 6.83/2.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.83/2.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.83/2.49  tff('#skF_2', type, '#skF_2': $i).
% 6.83/2.49  tff('#skF_3', type, '#skF_3': $i).
% 6.83/2.49  tff('#skF_1', type, '#skF_1': $i).
% 6.83/2.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.83/2.49  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.83/2.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.83/2.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.83/2.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.83/2.49  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 6.83/2.49  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 6.83/2.49  
% 6.83/2.50  tff(f_45, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (k2_wellord1(k2_wellord1(C, A), B) = k2_wellord1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_wellord1)).
% 6.83/2.50  tff(f_40, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 6.83/2.50  tff(f_35, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 6.83/2.50  tff(f_29, axiom, (![A, B, C, D]: (k2_zfmisc_1(k3_xboole_0(A, B), k3_xboole_0(C, D)) = k3_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t123_zfmisc_1)).
% 6.83/2.50  tff(f_27, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.83/2.50  tff(c_14, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.83/2.50  tff(c_45, plain, (![A_22, B_23]: (k3_xboole_0(A_22, k2_zfmisc_1(B_23, B_23))=k2_wellord1(A_22, B_23) | ~v1_relat_1(A_22))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.83/2.50  tff(c_8, plain, (![A_10, B_11]: (v1_relat_1(k3_xboole_0(A_10, B_11)) | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.83/2.50  tff(c_58, plain, (![A_22, B_23]: (v1_relat_1(k2_wellord1(A_22, B_23)) | ~v1_relat_1(A_22) | ~v1_relat_1(A_22))), inference(superposition, [status(thm), theory('equality')], [c_45, c_8])).
% 6.83/2.50  tff(c_4, plain, (![A_4, C_6, B_5, D_7]: (k3_xboole_0(k2_zfmisc_1(A_4, C_6), k2_zfmisc_1(B_5, D_7))=k2_zfmisc_1(k3_xboole_0(A_4, B_5), k3_xboole_0(C_6, D_7)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.83/2.50  tff(c_2, plain, (![A_1, B_2, C_3]: (k3_xboole_0(k3_xboole_0(A_1, B_2), C_3)=k3_xboole_0(A_1, k3_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.83/2.50  tff(c_132, plain, (![A_40, B_41, C_42]: (k3_xboole_0(A_40, k3_xboole_0(k2_zfmisc_1(B_41, B_41), C_42))=k3_xboole_0(k2_wellord1(A_40, B_41), C_42) | ~v1_relat_1(A_40))), inference(superposition, [status(thm), theory('equality')], [c_45, c_2])).
% 6.83/2.50  tff(c_1376, plain, (![A_159, C_160, B_161, D_162]: (k3_xboole_0(A_159, k2_zfmisc_1(k3_xboole_0(C_160, B_161), k3_xboole_0(C_160, D_162)))=k3_xboole_0(k2_wellord1(A_159, C_160), k2_zfmisc_1(B_161, D_162)) | ~v1_relat_1(A_159))), inference(superposition, [status(thm), theory('equality')], [c_4, c_132])).
% 6.83/2.50  tff(c_10, plain, (![A_12, B_14]: (k3_xboole_0(A_12, k2_zfmisc_1(B_14, B_14))=k2_wellord1(A_12, B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.83/2.50  tff(c_1610, plain, (![A_163, C_164, D_165]: (k3_xboole_0(k2_wellord1(A_163, C_164), k2_zfmisc_1(D_165, D_165))=k2_wellord1(A_163, k3_xboole_0(C_164, D_165)) | ~v1_relat_1(A_163) | ~v1_relat_1(A_163))), inference(superposition, [status(thm), theory('equality')], [c_1376, c_10])).
% 6.83/2.50  tff(c_5284, plain, (![A_312, C_313, D_314]: (k2_wellord1(k2_wellord1(A_312, C_313), D_314)=k2_wellord1(A_312, k3_xboole_0(C_313, D_314)) | ~v1_relat_1(k2_wellord1(A_312, C_313)) | ~v1_relat_1(A_312) | ~v1_relat_1(A_312))), inference(superposition, [status(thm), theory('equality')], [c_1610, c_10])).
% 6.83/2.50  tff(c_5320, plain, (![A_315, B_316, D_317]: (k2_wellord1(k2_wellord1(A_315, B_316), D_317)=k2_wellord1(A_315, k3_xboole_0(B_316, D_317)) | ~v1_relat_1(A_315))), inference(resolution, [status(thm)], [c_58, c_5284])).
% 6.83/2.50  tff(c_12, plain, (k2_wellord1(k2_wellord1('#skF_3', '#skF_1'), '#skF_2')!=k2_wellord1('#skF_3', k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.83/2.50  tff(c_5447, plain, (~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5320, c_12])).
% 6.83/2.50  tff(c_5458, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_5447])).
% 6.83/2.50  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.83/2.50  
% 6.83/2.50  Inference rules
% 6.83/2.50  ----------------------
% 6.83/2.50  #Ref     : 0
% 6.83/2.50  #Sup     : 1573
% 6.83/2.50  #Fact    : 0
% 6.83/2.50  #Define  : 0
% 6.83/2.50  #Split   : 0
% 6.83/2.50  #Chain   : 0
% 6.83/2.50  #Close   : 0
% 6.83/2.50  
% 6.83/2.50  Ordering : KBO
% 6.83/2.50  
% 6.83/2.50  Simplification rules
% 6.83/2.50  ----------------------
% 6.83/2.50  #Subsume      : 223
% 6.83/2.50  #Demod        : 246
% 6.83/2.50  #Tautology    : 44
% 6.83/2.50  #SimpNegUnit  : 0
% 6.83/2.50  #BackRed      : 0
% 6.83/2.50  
% 6.83/2.50  #Partial instantiations: 0
% 6.83/2.50  #Strategies tried      : 1
% 6.83/2.50  
% 6.83/2.50  Timing (in seconds)
% 6.83/2.50  ----------------------
% 6.83/2.50  Preprocessing        : 0.34
% 6.83/2.50  Parsing              : 0.19
% 6.83/2.50  CNF conversion       : 0.02
% 6.83/2.50  Main loop            : 1.28
% 6.83/2.50  Inferencing          : 0.46
% 6.83/2.50  Reduction            : 0.31
% 6.83/2.51  Demodulation         : 0.22
% 6.83/2.51  BG Simplification    : 0.08
% 6.83/2.51  Subsumption          : 0.36
% 6.83/2.51  Abstraction          : 0.08
% 6.83/2.51  MUC search           : 0.00
% 6.83/2.51  Cooper               : 0.00
% 6.83/2.51  Total                : 1.65
% 6.83/2.51  Index Insertion      : 0.00
% 6.83/2.51  Index Deletion       : 0.00
% 6.83/2.51  Index Matching       : 0.00
% 6.83/2.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
