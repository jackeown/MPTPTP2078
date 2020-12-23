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
% DateTime   : Thu Dec  3 10:17:06 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   35 ( 114 expanded)
%              Number of leaves         :   17 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :   51 ( 283 expanded)
%              Number of equality atoms :   22 ( 112 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k3_partfun1,type,(
    k3_partfun1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_partfun1,type,(
    k5_partfun1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => k5_partfun1(A,A,k3_partfun1(B,A,A)) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_2)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k5_partfun1(A,B,k3_partfun1(C,A,B)) = k1_tarski(C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t161_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_16,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) != k1_tarski('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_14,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_54,plain,(
    ! [B_12,A_13,C_14] :
      ( k1_xboole_0 = B_12
      | k5_partfun1(A_13,B_12,k3_partfun1(C_14,A_13,B_12)) = k1_tarski(C_14)
      | ~ m1_subset_1(C_14,k1_zfmisc_1(k2_zfmisc_1(A_13,B_12)))
      | ~ v1_funct_2(C_14,A_13,B_12)
      | ~ v1_funct_1(C_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) = k1_tarski('#skF_2')
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_14,c_54])).

tff(c_63,plain,
    ( k1_xboole_0 = '#skF_1'
    | k5_partfun1('#skF_1','#skF_1',k3_partfun1('#skF_2','#skF_1','#skF_1')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_16,c_56])).

tff(c_64,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_63])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_69,plain,(
    ! [B_2] : k2_zfmisc_1('#skF_1',B_2) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_6])).

tff(c_75,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_14])).

tff(c_8,plain,(
    ! [B_4,C_5] :
      ( k5_partfun1(k1_xboole_0,B_4,k3_partfun1(C_5,k1_xboole_0,B_4)) = k1_tarski(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_4)))
      | ~ v1_funct_2(C_5,k1_xboole_0,B_4)
      | ~ v1_funct_1(C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_19,plain,(
    ! [B_4,C_5] :
      ( k5_partfun1(k1_xboole_0,B_4,k3_partfun1(C_5,k1_xboole_0,B_4)) = k1_tarski(C_5)
      | ~ m1_subset_1(C_5,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_2(C_5,k1_xboole_0,B_4)
      | ~ v1_funct_1(C_5) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_109,plain,(
    ! [B_19,C_20] :
      ( k5_partfun1('#skF_1',B_19,k3_partfun1(C_20,'#skF_1',B_19)) = k1_tarski(C_20)
      | ~ m1_subset_1(C_20,k1_zfmisc_1('#skF_1'))
      | ~ v1_funct_2(C_20,'#skF_1',B_19)
      | ~ v1_funct_1(C_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_64,c_64,c_64,c_19])).

tff(c_111,plain,(
    ! [B_19] :
      ( k5_partfun1('#skF_1',B_19,k3_partfun1('#skF_2','#skF_1',B_19)) = k1_tarski('#skF_2')
      | ~ v1_funct_2('#skF_2','#skF_1',B_19)
      | ~ v1_funct_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_75,c_109])).

tff(c_121,plain,(
    ! [B_24] :
      ( k5_partfun1('#skF_1',B_24,k3_partfun1('#skF_2','#skF_1',B_24)) = k1_tarski('#skF_2')
      | ~ v1_funct_2('#skF_2','#skF_1',B_24) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_111])).

tff(c_127,plain,(
    ~ v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_12])).

tff(c_135,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:56:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.14  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  %$ v1_funct_2 > m1_subset_1 > v1_funct_1 > k5_partfun1 > k3_partfun1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.67/1.14  
% 1.67/1.14  %Foreground sorts:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Background operators:
% 1.67/1.14  
% 1.67/1.14  
% 1.67/1.14  %Foreground operators:
% 1.67/1.14  tff(k3_partfun1, type, k3_partfun1: ($i * $i * $i) > $i).
% 1.67/1.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.67/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.67/1.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.67/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.67/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.14  tff(k5_partfun1, type, k5_partfun1: ($i * $i * $i) > $i).
% 1.67/1.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.67/1.14  
% 1.83/1.15  tff(f_52, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => (k5_partfun1(A, A, k3_partfun1(B, A, A)) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_2)).
% 1.83/1.15  tff(f_43, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k5_partfun1(A, B, k3_partfun1(C, A, B)) = k1_tarski(C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t161_funct_2)).
% 1.83/1.15  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.83/1.15  tff(c_16, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.83/1.15  tff(c_18, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.83/1.15  tff(c_12, plain, (k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))!=k1_tarski('#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.83/1.15  tff(c_14, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.83/1.15  tff(c_54, plain, (![B_12, A_13, C_14]: (k1_xboole_0=B_12 | k5_partfun1(A_13, B_12, k3_partfun1(C_14, A_13, B_12))=k1_tarski(C_14) | ~m1_subset_1(C_14, k1_zfmisc_1(k2_zfmisc_1(A_13, B_12))) | ~v1_funct_2(C_14, A_13, B_12) | ~v1_funct_1(C_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.15  tff(c_56, plain, (k1_xboole_0='#skF_1' | k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))=k1_tarski('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_14, c_54])).
% 1.83/1.15  tff(c_63, plain, (k1_xboole_0='#skF_1' | k5_partfun1('#skF_1', '#skF_1', k3_partfun1('#skF_2', '#skF_1', '#skF_1'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_16, c_56])).
% 1.83/1.15  tff(c_64, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_12, c_63])).
% 1.83/1.15  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.83/1.15  tff(c_69, plain, (![B_2]: (k2_zfmisc_1('#skF_1', B_2)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_6])).
% 1.83/1.15  tff(c_75, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_69, c_14])).
% 1.83/1.15  tff(c_8, plain, (![B_4, C_5]: (k5_partfun1(k1_xboole_0, B_4, k3_partfun1(C_5, k1_xboole_0, B_4))=k1_tarski(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_4))) | ~v1_funct_2(C_5, k1_xboole_0, B_4) | ~v1_funct_1(C_5))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.15  tff(c_19, plain, (![B_4, C_5]: (k5_partfun1(k1_xboole_0, B_4, k3_partfun1(C_5, k1_xboole_0, B_4))=k1_tarski(C_5) | ~m1_subset_1(C_5, k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(C_5, k1_xboole_0, B_4) | ~v1_funct_1(C_5))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 1.83/1.15  tff(c_109, plain, (![B_19, C_20]: (k5_partfun1('#skF_1', B_19, k3_partfun1(C_20, '#skF_1', B_19))=k1_tarski(C_20) | ~m1_subset_1(C_20, k1_zfmisc_1('#skF_1')) | ~v1_funct_2(C_20, '#skF_1', B_19) | ~v1_funct_1(C_20))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_64, c_64, c_64, c_19])).
% 1.83/1.15  tff(c_111, plain, (![B_19]: (k5_partfun1('#skF_1', B_19, k3_partfun1('#skF_2', '#skF_1', B_19))=k1_tarski('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', B_19) | ~v1_funct_1('#skF_2'))), inference(resolution, [status(thm)], [c_75, c_109])).
% 1.83/1.15  tff(c_121, plain, (![B_24]: (k5_partfun1('#skF_1', B_24, k3_partfun1('#skF_2', '#skF_1', B_24))=k1_tarski('#skF_2') | ~v1_funct_2('#skF_2', '#skF_1', B_24))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_111])).
% 1.83/1.15  tff(c_127, plain, (~v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_121, c_12])).
% 1.83/1.15  tff(c_135, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_127])).
% 1.83/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.15  
% 1.83/1.15  Inference rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Ref     : 0
% 1.83/1.15  #Sup     : 27
% 1.83/1.15  #Fact    : 0
% 1.83/1.15  #Define  : 0
% 1.83/1.15  #Split   : 0
% 1.83/1.15  #Chain   : 0
% 1.83/1.15  #Close   : 0
% 1.83/1.15  
% 1.83/1.15  Ordering : KBO
% 1.83/1.15  
% 1.83/1.15  Simplification rules
% 1.83/1.15  ----------------------
% 1.83/1.15  #Subsume      : 2
% 1.83/1.15  #Demod        : 18
% 1.83/1.15  #Tautology    : 21
% 1.83/1.15  #SimpNegUnit  : 1
% 1.83/1.15  #BackRed      : 6
% 1.83/1.15  
% 1.83/1.15  #Partial instantiations: 0
% 1.83/1.15  #Strategies tried      : 1
% 1.83/1.15  
% 1.83/1.15  Timing (in seconds)
% 1.83/1.15  ----------------------
% 1.83/1.16  Preprocessing        : 0.27
% 1.83/1.16  Parsing              : 0.15
% 1.83/1.16  CNF conversion       : 0.02
% 1.83/1.16  Main loop            : 0.14
% 1.83/1.16  Inferencing          : 0.05
% 1.83/1.16  Reduction            : 0.04
% 1.83/1.16  Demodulation         : 0.03
% 1.83/1.16  BG Simplification    : 0.01
% 1.83/1.16  Subsumption          : 0.03
% 1.83/1.16  Abstraction          : 0.01
% 1.83/1.16  MUC search           : 0.00
% 1.83/1.16  Cooper               : 0.00
% 1.83/1.16  Total                : 0.44
% 1.83/1.16  Index Insertion      : 0.00
% 1.83/1.16  Index Deletion       : 0.00
% 1.83/1.16  Index Matching       : 0.00
% 1.83/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
