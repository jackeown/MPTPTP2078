%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:25 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   46 (  46 expanded)
%              Number of leaves         :   31 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  37 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_35,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_69,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k10_relat_1(B,A),k1_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t167_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_28] :
      ( r2_hidden('#skF_1'(A_28),A_28)
      | v1_relat_1(A_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_10,plain,(
    ! [A_4] : r1_xboole_0(A_4,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_61,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden(A_53,B_54)
      | ~ r1_xboole_0(k1_tarski(A_53),B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_68,plain,(
    ! [A_58] : ~ r2_hidden(A_58,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_61])).

tff(c_73,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_68])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_83,plain,(
    ! [B_61,A_62] :
      ( r1_tarski(k10_relat_1(B_61,A_62),k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_86,plain,(
    ! [A_62] :
      ( r1_tarski(k10_relat_1(k1_xboole_0,A_62),k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_83])).

tff(c_88,plain,(
    ! [A_62] : r1_tarski(k10_relat_1(k1_xboole_0,A_62),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_86])).

tff(c_90,plain,(
    ! [B_64,A_65] :
      ( B_64 = A_65
      | ~ r1_tarski(B_64,A_65)
      | ~ r1_tarski(A_65,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_62] :
      ( k10_relat_1(k1_xboole_0,A_62) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,k10_relat_1(k1_xboole_0,A_62)) ) ),
    inference(resolution,[status(thm)],[c_88,c_90])).

tff(c_101,plain,(
    ! [A_62] : k10_relat_1(k1_xboole_0,A_62) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_92])).

tff(c_38,plain,(
    k10_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:46:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  
% 1.70/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.15  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.70/1.15  
% 1.70/1.15  %Foreground sorts:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Background operators:
% 1.70/1.15  
% 1.70/1.15  
% 1.70/1.15  %Foreground operators:
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.70/1.15  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.70/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.70/1.15  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.70/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.70/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.70/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.70/1.15  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.15  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.70/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.70/1.15  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.15  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.15  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.70/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.70/1.15  
% 1.70/1.16  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.70/1.16  tff(f_62, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.70/1.16  tff(f_35, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.70/1.16  tff(f_52, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.70/1.16  tff(f_69, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.70/1.16  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k10_relat_1(B, A), k1_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t167_relat_1)).
% 1.70/1.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.70/1.16  tff(f_72, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_relat_1)).
% 1.70/1.16  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.70/1.16  tff(c_30, plain, (![A_28]: (r2_hidden('#skF_1'(A_28), A_28) | v1_relat_1(A_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.70/1.16  tff(c_10, plain, (![A_4]: (r1_xboole_0(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.70/1.16  tff(c_61, plain, (![A_53, B_54]: (~r2_hidden(A_53, B_54) | ~r1_xboole_0(k1_tarski(A_53), B_54))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.70/1.16  tff(c_68, plain, (![A_58]: (~r2_hidden(A_58, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_61])).
% 1.70/1.16  tff(c_73, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_30, c_68])).
% 1.70/1.16  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.70/1.16  tff(c_83, plain, (![B_61, A_62]: (r1_tarski(k10_relat_1(B_61, A_62), k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.70/1.16  tff(c_86, plain, (![A_62]: (r1_tarski(k10_relat_1(k1_xboole_0, A_62), k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_36, c_83])).
% 1.70/1.16  tff(c_88, plain, (![A_62]: (r1_tarski(k10_relat_1(k1_xboole_0, A_62), k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_86])).
% 1.70/1.16  tff(c_90, plain, (![B_64, A_65]: (B_64=A_65 | ~r1_tarski(B_64, A_65) | ~r1_tarski(A_65, B_64))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.16  tff(c_92, plain, (![A_62]: (k10_relat_1(k1_xboole_0, A_62)=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k10_relat_1(k1_xboole_0, A_62)))), inference(resolution, [status(thm)], [c_88, c_90])).
% 1.70/1.16  tff(c_101, plain, (![A_62]: (k10_relat_1(k1_xboole_0, A_62)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_92])).
% 1.70/1.16  tff(c_38, plain, (k10_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.70/1.16  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_101, c_38])).
% 1.70/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  Inference rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Ref     : 0
% 1.70/1.16  #Sup     : 15
% 1.70/1.16  #Fact    : 0
% 1.70/1.16  #Define  : 0
% 1.70/1.16  #Split   : 0
% 1.70/1.16  #Chain   : 0
% 1.70/1.16  #Close   : 0
% 1.70/1.16  
% 1.70/1.16  Ordering : KBO
% 1.70/1.16  
% 1.70/1.16  Simplification rules
% 1.70/1.16  ----------------------
% 1.70/1.16  #Subsume      : 0
% 1.70/1.16  #Demod        : 7
% 1.70/1.16  #Tautology    : 11
% 1.70/1.16  #SimpNegUnit  : 0
% 1.70/1.16  #BackRed      : 2
% 1.70/1.16  
% 1.70/1.16  #Partial instantiations: 0
% 1.70/1.16  #Strategies tried      : 1
% 1.70/1.16  
% 1.70/1.16  Timing (in seconds)
% 1.70/1.16  ----------------------
% 1.70/1.17  Preprocessing        : 0.30
% 1.70/1.17  Parsing              : 0.16
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.10
% 1.70/1.17  Inferencing          : 0.03
% 1.70/1.17  Reduction            : 0.03
% 1.70/1.17  Demodulation         : 0.03
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.01
% 1.70/1.17  Abstraction          : 0.01
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.17  Total                : 0.43
% 1.70/1.17  Index Insertion      : 0.00
% 1.70/1.17  Index Deletion       : 0.00
% 1.70/1.17  Index Matching       : 0.00
% 1.70/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
