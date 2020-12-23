%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:25 EST 2020

% Result     : Theorem 1.96s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   37 (  42 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  45 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_50,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : v1_relat_1(k2_tarski(k4_tarski(A,B),k4_tarski(C,D))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_relat_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k8_relat_1(A,B),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t117_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A] : k8_relat_1(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_relat_1)).

tff(c_12,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_69,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_73,plain,(
    ! [A_6] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_74,plain,(
    ! [A_6] : ~ v1_relat_1(A_6) ),
    inference(splitLeft,[status(thm)],[c_73])).

tff(c_18,plain,(
    ! [A_13,B_14,C_15,D_16] : v1_relat_1(k2_tarski(k4_tarski(A_13,B_14),k4_tarski(C_15,D_16))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_18])).

tff(c_78,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_73])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r1_tarski(k8_relat_1(A_17,B_18),B_18)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,(
    ! [B_30,A_31] :
      ( B_30 = A_31
      | ~ r1_tarski(B_30,A_31)
      | ~ r1_tarski(A_31,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_51,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ r1_tarski(A_32,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_38])).

tff(c_64,plain,(
    ! [A_17] :
      ( k8_relat_1(A_17,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_51])).

tff(c_80,plain,(
    ! [A_17] : k8_relat_1(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_64])).

tff(c_22,plain,(
    k8_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_83,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n010.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:08:29 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.96/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.43  
% 1.96/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.96/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > k8_relat_1 > k4_tarski > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 1.96/1.45  
% 1.96/1.45  %Foreground sorts:
% 1.96/1.45  
% 1.96/1.45  
% 1.96/1.45  %Background operators:
% 1.96/1.45  
% 1.96/1.45  
% 1.96/1.45  %Foreground operators:
% 1.96/1.45  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 1.96/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.96/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.96/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.96/1.45  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.96/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.96/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.96/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.96/1.45  tff('#skF_1', type, '#skF_1': $i).
% 1.96/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.96/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.96/1.45  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.96/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.96/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.96/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.96/1.45  
% 2.11/1.46  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.11/1.46  tff(f_50, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.11/1.46  tff(f_52, axiom, (![A, B, C, D]: v1_relat_1(k2_tarski(k4_tarski(A, B), k4_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc7_relat_1)).
% 2.11/1.46  tff(f_56, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k8_relat_1(A, B), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t117_relat_1)).
% 2.11/1.46  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.11/1.46  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.11/1.46  tff(f_59, negated_conjecture, ~(![A]: (k8_relat_1(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_relat_1)).
% 2.11/1.46  tff(c_12, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.46  tff(c_69, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.11/1.46  tff(c_73, plain, (![A_6]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_12, c_69])).
% 2.11/1.46  tff(c_74, plain, (![A_6]: (~v1_relat_1(A_6))), inference(splitLeft, [status(thm)], [c_73])).
% 2.11/1.46  tff(c_18, plain, (![A_13, B_14, C_15, D_16]: (v1_relat_1(k2_tarski(k4_tarski(A_13, B_14), k4_tarski(C_15, D_16))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.11/1.46  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_18])).
% 2.11/1.46  tff(c_78, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_73])).
% 2.11/1.46  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k8_relat_1(A_17, B_18), B_18) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.46  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.11/1.46  tff(c_38, plain, (![B_30, A_31]: (B_30=A_31 | ~r1_tarski(B_30, A_31) | ~r1_tarski(A_31, B_30))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.46  tff(c_51, plain, (![A_32]: (k1_xboole_0=A_32 | ~r1_tarski(A_32, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_38])).
% 2.11/1.46  tff(c_64, plain, (![A_17]: (k8_relat_1(A_17, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_51])).
% 2.11/1.46  tff(c_80, plain, (![A_17]: (k8_relat_1(A_17, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_78, c_64])).
% 2.11/1.46  tff(c_22, plain, (k8_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.46  tff(c_83, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_22])).
% 2.11/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.46  
% 2.11/1.46  Inference rules
% 2.11/1.46  ----------------------
% 2.11/1.46  #Ref     : 0
% 2.11/1.46  #Sup     : 9
% 2.11/1.46  #Fact    : 0
% 2.11/1.46  #Define  : 0
% 2.11/1.46  #Split   : 1
% 2.11/1.46  #Chain   : 0
% 2.11/1.46  #Close   : 0
% 2.11/1.46  
% 2.11/1.46  Ordering : KBO
% 2.11/1.46  
% 2.11/1.46  Simplification rules
% 2.11/1.46  ----------------------
% 2.11/1.46  #Subsume      : 2
% 2.11/1.46  #Demod        : 4
% 2.11/1.46  #Tautology    : 6
% 2.11/1.46  #SimpNegUnit  : 2
% 2.11/1.46  #BackRed      : 2
% 2.11/1.46  
% 2.11/1.46  #Partial instantiations: 0
% 2.11/1.46  #Strategies tried      : 1
% 2.11/1.46  
% 2.11/1.46  Timing (in seconds)
% 2.11/1.46  ----------------------
% 2.11/1.47  Preprocessing        : 0.40
% 2.11/1.47  Parsing              : 0.22
% 2.11/1.47  CNF conversion       : 0.03
% 2.11/1.47  Main loop            : 0.16
% 2.11/1.47  Inferencing          : 0.05
% 2.11/1.47  Reduction            : 0.05
% 2.11/1.47  Demodulation         : 0.03
% 2.11/1.47  BG Simplification    : 0.01
% 2.11/1.47  Subsumption          : 0.03
% 2.11/1.47  Abstraction          : 0.01
% 2.11/1.47  MUC search           : 0.00
% 2.11/1.47  Cooper               : 0.00
% 2.11/1.47  Total                : 0.61
% 2.11/1.47  Index Insertion      : 0.00
% 2.11/1.47  Index Deletion       : 0.00
% 2.11/1.47  Index Matching       : 0.00
% 2.11/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
