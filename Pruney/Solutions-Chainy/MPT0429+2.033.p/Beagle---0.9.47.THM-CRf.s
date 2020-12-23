%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:10 EST 2020

% Result     : Theorem 2.99s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   39 (  43 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  39 expanded)
%              Number of equality atoms :   19 (  23 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_42,axiom,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_44,axiom,(
    ! [A,B] : k1_zfmisc_1(k3_xboole_0(A,B)) = k3_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_51,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_172,plain,(
    ! [A_37,B_38] : k4_xboole_0(A_37,k4_xboole_0(A_37,B_38)) = k3_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_12,plain,(
    ! [A_9] : k4_xboole_0(k1_xboole_0,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_193,plain,(
    ! [B_38] : k3_xboole_0(k1_xboole_0,B_38) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_12])).

tff(c_246,plain,(
    ! [A_44,B_45] : k3_xboole_0(k1_zfmisc_1(A_44),k1_zfmisc_1(B_45)) = k1_zfmisc_1(k3_xboole_0(A_44,B_45)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_260,plain,(
    ! [B_45] : k3_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_45)) = k1_zfmisc_1(k3_xboole_0(k1_xboole_0,B_45)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_246])).

tff(c_266,plain,(
    ! [B_45] : k3_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_45)) = k1_tarski(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_193,c_260])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( k1_xboole_0 = A_5
      | ~ r1_tarski(A_5,k4_xboole_0(B_6,A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1087,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(A_74,B_75),k3_xboole_0(A_74,B_75)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_172,c_8])).

tff(c_1126,plain,(
    ! [B_45] :
      ( k4_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_45)) = k1_xboole_0
      | ~ r1_tarski(k4_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_45)),k1_tarski(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_1087])).

tff(c_1168,plain,(
    ! [B_45] : k4_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1(B_45)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1126])).

tff(c_126,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | k4_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_19,B_20] :
      ( m1_subset_1(A_19,k1_zfmisc_1(B_20))
      | ~ r1_tarski(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_24,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ~ r1_tarski(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_49,c_24])).

tff(c_144,plain,(
    k4_xboole_0(k1_tarski(k1_xboole_0),k1_zfmisc_1('#skF_1')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_126,c_56])).

tff(c_1186,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1168,c_144])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:48:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.99/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.58  
% 2.99/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.58  %$ r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.99/1.58  
% 2.99/1.58  %Foreground sorts:
% 2.99/1.58  
% 2.99/1.58  
% 2.99/1.58  %Background operators:
% 2.99/1.58  
% 2.99/1.58  
% 2.99/1.58  %Foreground operators:
% 2.99/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.99/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.99/1.58  tff('#skF_1', type, '#skF_1': $i).
% 2.99/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.58  
% 2.99/1.59  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.99/1.59  tff(f_42, axiom, (k1_zfmisc_1(k1_xboole_0) = k1_tarski(k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_zfmisc_1)).
% 2.99/1.59  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.99/1.59  tff(f_39, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 2.99/1.59  tff(f_44, axiom, (![A, B]: (k1_zfmisc_1(k3_xboole_0(A, B)) = k3_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 2.99/1.59  tff(f_35, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.99/1.59  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.99/1.59  tff(f_48, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.99/1.59  tff(f_51, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.99/1.59  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.99/1.59  tff(c_16, plain, (k1_zfmisc_1(k1_xboole_0)=k1_tarski(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.99/1.59  tff(c_172, plain, (![A_37, B_38]: (k4_xboole_0(A_37, k4_xboole_0(A_37, B_38))=k3_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.59  tff(c_12, plain, (![A_9]: (k4_xboole_0(k1_xboole_0, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.59  tff(c_193, plain, (![B_38]: (k3_xboole_0(k1_xboole_0, B_38)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_172, c_12])).
% 2.99/1.59  tff(c_246, plain, (![A_44, B_45]: (k3_xboole_0(k1_zfmisc_1(A_44), k1_zfmisc_1(B_45))=k1_zfmisc_1(k3_xboole_0(A_44, B_45)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.99/1.59  tff(c_260, plain, (![B_45]: (k3_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_45))=k1_zfmisc_1(k3_xboole_0(k1_xboole_0, B_45)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_246])).
% 2.99/1.59  tff(c_266, plain, (![B_45]: (k3_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_45))=k1_tarski(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_193, c_260])).
% 2.99/1.59  tff(c_8, plain, (![A_5, B_6]: (k1_xboole_0=A_5 | ~r1_tarski(A_5, k4_xboole_0(B_6, A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.99/1.59  tff(c_1087, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k1_xboole_0 | ~r1_tarski(k4_xboole_0(A_74, B_75), k3_xboole_0(A_74, B_75)))), inference(superposition, [status(thm), theory('equality')], [c_172, c_8])).
% 2.99/1.59  tff(c_1126, plain, (![B_45]: (k4_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_45))=k1_xboole_0 | ~r1_tarski(k4_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_45)), k1_tarski(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_266, c_1087])).
% 2.99/1.59  tff(c_1168, plain, (![B_45]: (k4_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1(B_45))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1126])).
% 2.99/1.59  tff(c_126, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | k4_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.59  tff(c_49, plain, (![A_19, B_20]: (m1_subset_1(A_19, k1_zfmisc_1(B_20)) | ~r1_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.99/1.59  tff(c_24, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.99/1.59  tff(c_56, plain, (~r1_tarski(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_49, c_24])).
% 2.99/1.59  tff(c_144, plain, (k4_xboole_0(k1_tarski(k1_xboole_0), k1_zfmisc_1('#skF_1'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_126, c_56])).
% 2.99/1.60  tff(c_1186, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1168, c_144])).
% 2.99/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.60  
% 2.99/1.60  Inference rules
% 2.99/1.60  ----------------------
% 2.99/1.60  #Ref     : 0
% 2.99/1.60  #Sup     : 308
% 2.99/1.60  #Fact    : 0
% 2.99/1.60  #Define  : 0
% 2.99/1.60  #Split   : 0
% 2.99/1.60  #Chain   : 0
% 2.99/1.60  #Close   : 0
% 2.99/1.60  
% 2.99/1.60  Ordering : KBO
% 2.99/1.60  
% 2.99/1.60  Simplification rules
% 2.99/1.60  ----------------------
% 2.99/1.60  #Subsume      : 18
% 2.99/1.60  #Demod        : 255
% 2.99/1.60  #Tautology    : 203
% 2.99/1.60  #SimpNegUnit  : 0
% 2.99/1.60  #BackRed      : 2
% 2.99/1.60  
% 2.99/1.60  #Partial instantiations: 0
% 2.99/1.60  #Strategies tried      : 1
% 2.99/1.60  
% 2.99/1.60  Timing (in seconds)
% 2.99/1.60  ----------------------
% 2.99/1.60  Preprocessing        : 0.35
% 2.99/1.60  Parsing              : 0.20
% 2.99/1.60  CNF conversion       : 0.02
% 2.99/1.60  Main loop            : 0.43
% 2.99/1.60  Inferencing          : 0.16
% 2.99/1.60  Reduction            : 0.16
% 2.99/1.60  Demodulation         : 0.12
% 2.99/1.60  BG Simplification    : 0.02
% 2.99/1.60  Subsumption          : 0.07
% 2.99/1.60  Abstraction          : 0.02
% 2.99/1.60  MUC search           : 0.00
% 2.99/1.60  Cooper               : 0.00
% 2.99/1.60  Total                : 0.81
% 2.99/1.60  Index Insertion      : 0.00
% 2.99/1.60  Index Deletion       : 0.00
% 2.99/1.60  Index Matching       : 0.00
% 2.99/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
