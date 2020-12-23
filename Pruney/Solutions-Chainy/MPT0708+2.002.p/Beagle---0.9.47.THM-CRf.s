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
% DateTime   : Thu Dec  3 10:05:23 EST 2020

% Result     : Theorem 6.06s
% Output     : CNFRefutation 6.06s
% Verified   : 
% Statistics : Number of formulae       :   35 (  38 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  58 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_relat_1(C)
          & v1_funct_1(C) )
       => ( ( r1_tarski(A,k1_relat_1(C))
            & r1_tarski(k9_relat_1(C,A),B) )
         => r1_tarski(A,k10_relat_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t163_funct_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => r1_tarski(A,k10_relat_1(B,k9_relat_1(B,A))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_funct_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k10_relat_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t175_relat_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_12,plain,(
    ~ r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_20,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    r1_tarski('#skF_1',k1_relat_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,k10_relat_1(B_12,k9_relat_1(B_12,A_11)))
      | ~ r1_tarski(A_11,k1_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    r1_tarski(k9_relat_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_54,plain,(
    ! [A_15,B_16] :
      ( k2_xboole_0(A_15,B_16) = B_16
      | ~ r1_tarski(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    k2_xboole_0(k9_relat_1('#skF_3','#skF_1'),'#skF_2') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_54])).

tff(c_217,plain,(
    ! [C_29,A_30,B_31] :
      ( k2_xboole_0(k10_relat_1(C_29,A_30),k10_relat_1(C_29,B_31)) = k10_relat_1(C_29,k2_xboole_0(A_30,B_31))
      | ~ v1_relat_1(C_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_90,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,k2_xboole_0(C_18,B_19))
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_17,B_2,A_1] :
      ( r1_tarski(A_17,k2_xboole_0(B_2,A_1))
      | ~ r1_tarski(A_17,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_90])).

tff(c_2268,plain,(
    ! [A_101,C_102,A_103,B_104] :
      ( r1_tarski(A_101,k10_relat_1(C_102,k2_xboole_0(A_103,B_104)))
      | ~ r1_tarski(A_101,k10_relat_1(C_102,A_103))
      | ~ v1_relat_1(C_102) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_105])).

tff(c_4125,plain,(
    ! [A_191,C_192] :
      ( r1_tarski(A_191,k10_relat_1(C_192,'#skF_2'))
      | ~ r1_tarski(A_191,k10_relat_1(C_192,k9_relat_1('#skF_3','#skF_1')))
      | ~ v1_relat_1(C_192) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_2268])).

tff(c_4133,plain,
    ( r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2'))
    | ~ r1_tarski('#skF_1',k1_relat_1('#skF_3'))
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_4125])).

tff(c_4139,plain,(
    r1_tarski('#skF_1',k10_relat_1('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_16,c_4133])).

tff(c_4141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_4139])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:15:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.06/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.17  
% 6.06/2.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.17  %$ r1_tarski > v1_relat_1 > v1_funct_1 > k9_relat_1 > k2_xboole_0 > k10_relat_1 > #nlpp > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 6.06/2.17  
% 6.06/2.17  %Foreground sorts:
% 6.06/2.17  
% 6.06/2.17  
% 6.06/2.17  %Background operators:
% 6.06/2.17  
% 6.06/2.17  
% 6.06/2.17  %Foreground operators:
% 6.06/2.17  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.06/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.06/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.06/2.17  tff('#skF_2', type, '#skF_2': $i).
% 6.06/2.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 6.06/2.17  tff('#skF_3', type, '#skF_3': $i).
% 6.06/2.17  tff('#skF_1', type, '#skF_1': $i).
% 6.06/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.06/2.17  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 6.06/2.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.06/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.06/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.06/2.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.06/2.17  
% 6.06/2.18  tff(f_56, negated_conjecture, ~(![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => ((r1_tarski(A, k1_relat_1(C)) & r1_tarski(k9_relat_1(C, A), B)) => r1_tarski(A, k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t163_funct_1)).
% 6.06/2.18  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => r1_tarski(A, k10_relat_1(B, k9_relat_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_funct_1)).
% 6.06/2.18  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 6.06/2.18  tff(f_39, axiom, (![A, B, C]: (v1_relat_1(C) => (k10_relat_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t175_relat_1)).
% 6.06/2.18  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.06/2.18  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 6.06/2.18  tff(c_12, plain, (~r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.06/2.18  tff(c_20, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.06/2.18  tff(c_16, plain, (r1_tarski('#skF_1', k1_relat_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.06/2.18  tff(c_10, plain, (![A_11, B_12]: (r1_tarski(A_11, k10_relat_1(B_12, k9_relat_1(B_12, A_11))) | ~r1_tarski(A_11, k1_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.06/2.18  tff(c_14, plain, (r1_tarski(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.06/2.18  tff(c_54, plain, (![A_15, B_16]: (k2_xboole_0(A_15, B_16)=B_16 | ~r1_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.06/2.18  tff(c_61, plain, (k2_xboole_0(k9_relat_1('#skF_3', '#skF_1'), '#skF_2')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_54])).
% 6.06/2.18  tff(c_217, plain, (![C_29, A_30, B_31]: (k2_xboole_0(k10_relat_1(C_29, A_30), k10_relat_1(C_29, B_31))=k10_relat_1(C_29, k2_xboole_0(A_30, B_31)) | ~v1_relat_1(C_29))), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.06/2.18  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.06/2.18  tff(c_90, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, k2_xboole_0(C_18, B_19)) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.06/2.18  tff(c_105, plain, (![A_17, B_2, A_1]: (r1_tarski(A_17, k2_xboole_0(B_2, A_1)) | ~r1_tarski(A_17, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_90])).
% 6.06/2.18  tff(c_2268, plain, (![A_101, C_102, A_103, B_104]: (r1_tarski(A_101, k10_relat_1(C_102, k2_xboole_0(A_103, B_104))) | ~r1_tarski(A_101, k10_relat_1(C_102, A_103)) | ~v1_relat_1(C_102))), inference(superposition, [status(thm), theory('equality')], [c_217, c_105])).
% 6.06/2.18  tff(c_4125, plain, (![A_191, C_192]: (r1_tarski(A_191, k10_relat_1(C_192, '#skF_2')) | ~r1_tarski(A_191, k10_relat_1(C_192, k9_relat_1('#skF_3', '#skF_1'))) | ~v1_relat_1(C_192))), inference(superposition, [status(thm), theory('equality')], [c_61, c_2268])).
% 6.06/2.18  tff(c_4133, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2')) | ~r1_tarski('#skF_1', k1_relat_1('#skF_3')) | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_4125])).
% 6.06/2.18  tff(c_4139, plain, (r1_tarski('#skF_1', k10_relat_1('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_16, c_4133])).
% 6.06/2.18  tff(c_4141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_4139])).
% 6.06/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.06/2.18  
% 6.06/2.18  Inference rules
% 6.06/2.18  ----------------------
% 6.06/2.18  #Ref     : 0
% 6.06/2.18  #Sup     : 1295
% 6.06/2.18  #Fact    : 0
% 6.06/2.18  #Define  : 0
% 6.06/2.18  #Split   : 6
% 6.06/2.18  #Chain   : 0
% 6.06/2.18  #Close   : 0
% 6.06/2.18  
% 6.06/2.18  Ordering : KBO
% 6.06/2.18  
% 6.06/2.18  Simplification rules
% 6.06/2.18  ----------------------
% 6.06/2.18  #Subsume      : 453
% 6.06/2.18  #Demod        : 122
% 6.06/2.18  #Tautology    : 153
% 6.06/2.18  #SimpNegUnit  : 1
% 6.06/2.18  #BackRed      : 0
% 6.06/2.18  
% 6.06/2.18  #Partial instantiations: 0
% 6.06/2.18  #Strategies tried      : 1
% 6.06/2.18  
% 6.06/2.18  Timing (in seconds)
% 6.06/2.18  ----------------------
% 6.06/2.18  Preprocessing        : 0.26
% 6.06/2.18  Parsing              : 0.15
% 6.06/2.18  CNF conversion       : 0.02
% 6.06/2.18  Main loop            : 1.17
% 6.06/2.18  Inferencing          : 0.33
% 6.06/2.18  Reduction            : 0.36
% 6.06/2.18  Demodulation         : 0.28
% 6.06/2.18  BG Simplification    : 0.04
% 6.06/2.18  Subsumption          : 0.36
% 6.06/2.18  Abstraction          : 0.05
% 6.06/2.18  MUC search           : 0.00
% 6.06/2.18  Cooper               : 0.00
% 6.06/2.18  Total                : 1.46
% 6.06/2.18  Index Insertion      : 0.00
% 6.06/2.18  Index Deletion       : 0.00
% 6.06/2.18  Index Matching       : 0.00
% 6.06/2.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
