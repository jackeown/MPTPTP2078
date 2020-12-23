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
% DateTime   : Thu Dec  3 10:00:01 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.80s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   36 (  46 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_53,axiom,(
    ? [A] :
      ( ~ v1_xboole_0(A)
      & v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_relat_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_10,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_28,plain,(
    ! [B_18,A_19] :
      ( v1_relat_1(B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_19))
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_32,plain,(
    ! [A_4] :
      ( v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_4) ) ),
    inference(resolution,[status(thm)],[c_10,c_28])).

tff(c_33,plain,(
    ! [A_4] : ~ v1_relat_1(A_4) ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_16])).

tff(c_50,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_20,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_51,plain,(
    ! [B_22,A_23] :
      ( B_22 = A_23
      | ~ r1_tarski(B_22,A_23)
      | ~ r1_tarski(A_23,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_64,plain,(
    ! [A_24] :
      ( k1_xboole_0 = A_24
      | ~ r1_tarski(A_24,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_51])).

tff(c_68,plain,(
    ! [A_11] :
      ( k7_relat_1(k1_xboole_0,A_11) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_79,plain,(
    ! [A_11] : k7_relat_1(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_68])).

tff(c_22,plain,(
    k7_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_86,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:33:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.17  
% 1.80/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.18  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.80/1.18  
% 1.80/1.18  %Foreground sorts:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Background operators:
% 1.80/1.18  
% 1.80/1.18  
% 1.80/1.18  %Foreground operators:
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.80/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.80/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.80/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.80/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.80/1.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.80/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.18  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.80/1.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.80/1.18  
% 1.80/1.19  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.80/1.19  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 1.80/1.19  tff(f_53, axiom, (?[A]: (~v1_xboole_0(A) & v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_relat_1)).
% 1.80/1.19  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_relat_1)).
% 1.80/1.19  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.80/1.19  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.80/1.19  tff(f_60, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.80/1.19  tff(c_10, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.80/1.19  tff(c_28, plain, (![B_18, A_19]: (v1_relat_1(B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_19)) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.80/1.19  tff(c_32, plain, (![A_4]: (v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_4))), inference(resolution, [status(thm)], [c_10, c_28])).
% 1.80/1.19  tff(c_33, plain, (![A_4]: (~v1_relat_1(A_4))), inference(splitLeft, [status(thm)], [c_32])).
% 1.80/1.19  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.80/1.19  tff(c_49, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_16])).
% 1.80/1.19  tff(c_50, plain, (v1_relat_1(k1_xboole_0)), inference(splitRight, [status(thm)], [c_32])).
% 1.80/1.19  tff(c_20, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.80/1.19  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.80/1.19  tff(c_51, plain, (![B_22, A_23]: (B_22=A_23 | ~r1_tarski(B_22, A_23) | ~r1_tarski(A_23, B_22))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.80/1.19  tff(c_64, plain, (![A_24]: (k1_xboole_0=A_24 | ~r1_tarski(A_24, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_51])).
% 1.80/1.19  tff(c_68, plain, (![A_11]: (k7_relat_1(k1_xboole_0, A_11)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_64])).
% 1.80/1.19  tff(c_79, plain, (![A_11]: (k7_relat_1(k1_xboole_0, A_11)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_50, c_68])).
% 1.80/1.19  tff(c_22, plain, (k7_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.80/1.19  tff(c_86, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79, c_22])).
% 1.80/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  Inference rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Ref     : 0
% 1.80/1.19  #Sup     : 10
% 1.80/1.19  #Fact    : 0
% 1.80/1.19  #Define  : 0
% 1.80/1.19  #Split   : 1
% 1.80/1.19  #Chain   : 0
% 1.80/1.19  #Close   : 0
% 1.80/1.19  
% 1.80/1.19  Ordering : KBO
% 1.80/1.19  
% 1.80/1.19  Simplification rules
% 1.80/1.19  ----------------------
% 1.80/1.19  #Subsume      : 2
% 1.80/1.19  #Demod        : 5
% 1.80/1.19  #Tautology    : 5
% 1.80/1.19  #SimpNegUnit  : 2
% 1.80/1.19  #BackRed      : 2
% 1.80/1.19  
% 1.80/1.19  #Partial instantiations: 0
% 1.80/1.19  #Strategies tried      : 1
% 1.80/1.19  
% 1.80/1.19  Timing (in seconds)
% 1.80/1.19  ----------------------
% 1.80/1.20  Preprocessing        : 0.29
% 1.80/1.20  Parsing              : 0.16
% 1.80/1.20  CNF conversion       : 0.02
% 1.80/1.20  Main loop            : 0.11
% 1.80/1.20  Inferencing          : 0.04
% 1.80/1.20  Reduction            : 0.03
% 1.80/1.20  Demodulation         : 0.02
% 1.80/1.20  BG Simplification    : 0.01
% 1.80/1.20  Subsumption          : 0.02
% 1.80/1.20  Abstraction          : 0.00
% 1.80/1.20  MUC search           : 0.00
% 1.80/1.20  Cooper               : 0.00
% 1.80/1.20  Total                : 0.43
% 1.80/1.20  Index Insertion      : 0.00
% 1.80/1.20  Index Deletion       : 0.00
% 1.80/1.20  Index Matching       : 0.00
% 1.80/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
