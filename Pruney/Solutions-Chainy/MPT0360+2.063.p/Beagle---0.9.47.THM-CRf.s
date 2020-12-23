%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:27 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   34 (  37 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  50 expanded)
%              Number of equality atoms :    8 (  11 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_12,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(A_15,B_16) = k3_subset_1(A_15,B_16)
      | ~ m1_subset_1(B_16,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_28,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_24])).

tff(c_19,plain,(
    ! [A_12,C_13,B_14] :
      ( r1_xboole_0(A_12,k4_xboole_0(C_13,B_14))
      | ~ r1_tarski(A_12,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( ~ r1_xboole_0(B_3,A_2)
      | ~ r1_tarski(B_3,A_2)
      | v1_xboole_0(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_41,plain,(
    ! [A_18,C_19,B_20] :
      ( ~ r1_tarski(A_18,k4_xboole_0(C_19,B_20))
      | v1_xboole_0(A_18)
      | ~ r1_tarski(A_18,B_20) ) ),
    inference(resolution,[status(thm)],[c_19,c_4])).

tff(c_45,plain,(
    ! [A_21] :
      ( ~ r1_tarski(A_21,k3_subset_1('#skF_1','#skF_3'))
      | v1_xboole_0(A_21)
      | ~ r1_tarski(A_21,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_41])).

tff(c_48,plain,
    ( v1_xboole_0('#skF_2')
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_12,c_45])).

tff(c_51,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_51,c_2])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:18:38 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.21  
% 1.64/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.21  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.64/1.21  
% 1.64/1.21  %Foreground sorts:
% 1.64/1.21  
% 1.64/1.21  
% 1.64/1.21  %Background operators:
% 1.64/1.21  
% 1.64/1.21  
% 1.64/1.21  %Foreground operators:
% 1.64/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.21  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.64/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.21  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.21  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.64/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.64/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.64/1.21  
% 1.64/1.22  tff(f_54, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 1.64/1.22  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 1.64/1.22  tff(f_41, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.64/1.22  tff(f_37, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 1.64/1.22  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.64/1.22  tff(c_10, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.22  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.22  tff(c_12, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.22  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.64/1.22  tff(c_24, plain, (![A_15, B_16]: (k4_xboole_0(A_15, B_16)=k3_subset_1(A_15, B_16) | ~m1_subset_1(B_16, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.64/1.22  tff(c_28, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_24])).
% 1.64/1.22  tff(c_19, plain, (![A_12, C_13, B_14]: (r1_xboole_0(A_12, k4_xboole_0(C_13, B_14)) | ~r1_tarski(A_12, B_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.22  tff(c_4, plain, (![B_3, A_2]: (~r1_xboole_0(B_3, A_2) | ~r1_tarski(B_3, A_2) | v1_xboole_0(B_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.64/1.22  tff(c_41, plain, (![A_18, C_19, B_20]: (~r1_tarski(A_18, k4_xboole_0(C_19, B_20)) | v1_xboole_0(A_18) | ~r1_tarski(A_18, B_20))), inference(resolution, [status(thm)], [c_19, c_4])).
% 1.64/1.22  tff(c_45, plain, (![A_21]: (~r1_tarski(A_21, k3_subset_1('#skF_1', '#skF_3')) | v1_xboole_0(A_21) | ~r1_tarski(A_21, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_41])).
% 1.64/1.22  tff(c_48, plain, (v1_xboole_0('#skF_2') | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_12, c_45])).
% 1.64/1.22  tff(c_51, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 1.64/1.22  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.22  tff(c_54, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_51, c_2])).
% 1.64/1.22  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_54])).
% 1.64/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.22  
% 1.64/1.22  Inference rules
% 1.64/1.22  ----------------------
% 1.64/1.22  #Ref     : 0
% 1.64/1.22  #Sup     : 9
% 1.64/1.22  #Fact    : 0
% 1.64/1.22  #Define  : 0
% 1.64/1.22  #Split   : 0
% 1.64/1.22  #Chain   : 0
% 1.64/1.22  #Close   : 0
% 1.64/1.22  
% 1.64/1.22  Ordering : KBO
% 1.64/1.22  
% 1.64/1.22  Simplification rules
% 1.64/1.22  ----------------------
% 1.64/1.22  #Subsume      : 0
% 1.64/1.22  #Demod        : 1
% 1.64/1.22  #Tautology    : 2
% 1.64/1.22  #SimpNegUnit  : 1
% 1.64/1.22  #BackRed      : 0
% 1.64/1.22  
% 1.64/1.22  #Partial instantiations: 0
% 1.64/1.22  #Strategies tried      : 1
% 1.64/1.22  
% 1.64/1.22  Timing (in seconds)
% 1.64/1.22  ----------------------
% 1.64/1.22  Preprocessing        : 0.27
% 1.64/1.22  Parsing              : 0.14
% 1.64/1.22  CNF conversion       : 0.01
% 1.64/1.22  Main loop            : 0.08
% 1.64/1.22  Inferencing          : 0.04
% 1.64/1.22  Reduction            : 0.02
% 1.64/1.22  Demodulation         : 0.02
% 1.64/1.22  BG Simplification    : 0.01
% 1.64/1.22  Subsumption          : 0.01
% 1.64/1.22  Abstraction          : 0.00
% 1.64/1.22  MUC search           : 0.00
% 1.64/1.22  Cooper               : 0.00
% 1.64/1.22  Total                : 0.37
% 1.64/1.22  Index Insertion      : 0.00
% 1.64/1.22  Index Deletion       : 0.00
% 1.64/1.22  Index Matching       : 0.00
% 1.64/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
