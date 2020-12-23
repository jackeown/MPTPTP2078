%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:18 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   28 (  66 expanded)
%              Number of leaves         :   15 (  33 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 ( 153 expanded)
%              Number of equality atoms :    6 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_funct_2,type,(
    k1_funct_2: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_funct_1(B)
          & v1_funct_2(B,A,A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(A,A))) )
       => r2_hidden(B,k1_funct_2(A,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_funct_2)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => r2_hidden(C,k1_funct_2(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_funct_2)).

tff(c_6,plain,(
    ~ r2_hidden('#skF_2',k1_funct_2('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_12,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    v1_funct_2('#skF_2','#skF_1','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_14,plain,(
    ! [B_6,C_7,A_8] :
      ( k1_xboole_0 = B_6
      | r2_hidden(C_7,k1_funct_2(A_8,B_6))
      | ~ m1_subset_1(C_7,k1_zfmisc_1(k2_zfmisc_1(A_8,B_6)))
      | ~ v1_funct_2(C_7,A_8,B_6)
      | ~ v1_funct_1(C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_17,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2',k1_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_14])).

tff(c_20,plain,
    ( k1_xboole_0 = '#skF_1'
    | r2_hidden('#skF_2',k1_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_17])).

tff(c_21,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_20])).

tff(c_2,plain,(
    ! [C_3,B_2] :
      ( r2_hidden(C_3,k1_funct_2(k1_xboole_0,B_2))
      | ~ m1_subset_1(C_3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_2)))
      | ~ v1_funct_2(C_3,k1_xboole_0,B_2)
      | ~ v1_funct_1(C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_28,plain,(
    ! [C_9,B_10] :
      ( r2_hidden(C_9,k1_funct_2('#skF_1',B_10))
      | ~ m1_subset_1(C_9,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_10)))
      | ~ v1_funct_2(C_9,'#skF_1',B_10)
      | ~ v1_funct_1(C_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_21,c_21,c_21,c_2])).

tff(c_31,plain,
    ( r2_hidden('#skF_2',k1_funct_2('#skF_1','#skF_1'))
    | ~ v1_funct_2('#skF_2','#skF_1','#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_28])).

tff(c_34,plain,(
    r2_hidden('#skF_2',k1_funct_2('#skF_1','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_31])).

tff(c_36,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:42:49 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k2_zfmisc_1 > k1_funct_2 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.10  
% 1.63/1.10  %Foreground sorts:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Background operators:
% 1.63/1.10  
% 1.63/1.10  
% 1.63/1.10  %Foreground operators:
% 1.63/1.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.63/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.63/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.63/1.10  tff(k1_funct_2, type, k1_funct_2: ($i * $i) > $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.63/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.63/1.10  
% 1.63/1.11  tff(f_46, negated_conjecture, ~(![A, B]: (((v1_funct_1(B) & v1_funct_2(B, A, A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(A, A)))) => r2_hidden(B, k1_funct_2(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_funct_2)).
% 1.63/1.11  tff(f_37, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => r2_hidden(C, k1_funct_2(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_funct_2)).
% 1.63/1.11  tff(c_6, plain, (~r2_hidden('#skF_2', k1_funct_2('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.11  tff(c_12, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.11  tff(c_10, plain, (v1_funct_2('#skF_2', '#skF_1', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.11  tff(c_8, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.11  tff(c_14, plain, (![B_6, C_7, A_8]: (k1_xboole_0=B_6 | r2_hidden(C_7, k1_funct_2(A_8, B_6)) | ~m1_subset_1(C_7, k1_zfmisc_1(k2_zfmisc_1(A_8, B_6))) | ~v1_funct_2(C_7, A_8, B_6) | ~v1_funct_1(C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.11  tff(c_17, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', k1_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_14])).
% 1.63/1.11  tff(c_20, plain, (k1_xboole_0='#skF_1' | r2_hidden('#skF_2', k1_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_17])).
% 1.63/1.11  tff(c_21, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_6, c_20])).
% 1.63/1.11  tff(c_2, plain, (![C_3, B_2]: (r2_hidden(C_3, k1_funct_2(k1_xboole_0, B_2)) | ~m1_subset_1(C_3, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_2))) | ~v1_funct_2(C_3, k1_xboole_0, B_2) | ~v1_funct_1(C_3))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.63/1.11  tff(c_28, plain, (![C_9, B_10]: (r2_hidden(C_9, k1_funct_2('#skF_1', B_10)) | ~m1_subset_1(C_9, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_10))) | ~v1_funct_2(C_9, '#skF_1', B_10) | ~v1_funct_1(C_9))), inference(demodulation, [status(thm), theory('equality')], [c_21, c_21, c_21, c_2])).
% 1.63/1.11  tff(c_31, plain, (r2_hidden('#skF_2', k1_funct_2('#skF_1', '#skF_1')) | ~v1_funct_2('#skF_2', '#skF_1', '#skF_1') | ~v1_funct_1('#skF_2')), inference(resolution, [status(thm)], [c_8, c_28])).
% 1.63/1.11  tff(c_34, plain, (r2_hidden('#skF_2', k1_funct_2('#skF_1', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_31])).
% 1.63/1.11  tff(c_36, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_34])).
% 1.63/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.11  
% 1.63/1.11  Inference rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Ref     : 0
% 1.63/1.11  #Sup     : 4
% 1.63/1.11  #Fact    : 0
% 1.63/1.11  #Define  : 0
% 1.63/1.11  #Split   : 0
% 1.63/1.11  #Chain   : 0
% 1.63/1.11  #Close   : 0
% 1.63/1.11  
% 1.63/1.11  Ordering : KBO
% 1.63/1.11  
% 1.63/1.11  Simplification rules
% 1.63/1.11  ----------------------
% 1.63/1.11  #Subsume      : 0
% 1.63/1.11  #Demod        : 8
% 1.63/1.11  #Tautology    : 2
% 1.63/1.11  #SimpNegUnit  : 2
% 1.63/1.11  #BackRed      : 2
% 1.63/1.11  
% 1.63/1.11  #Partial instantiations: 0
% 1.63/1.11  #Strategies tried      : 1
% 1.63/1.11  
% 1.63/1.11  Timing (in seconds)
% 1.63/1.11  ----------------------
% 1.63/1.11  Preprocessing        : 0.26
% 1.63/1.11  Parsing              : 0.14
% 1.63/1.11  CNF conversion       : 0.01
% 1.63/1.11  Main loop            : 0.08
% 1.63/1.11  Inferencing          : 0.04
% 1.63/1.11  Reduction            : 0.02
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.01
% 1.63/1.11  Abstraction          : 0.00
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.37
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
