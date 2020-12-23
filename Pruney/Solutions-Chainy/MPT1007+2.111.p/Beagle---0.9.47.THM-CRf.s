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
% DateTime   : Thu Dec  3 10:14:25 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.71s
% Verified   : 
% Statistics : Number of formulae       :   34 (  38 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   42 (  62 expanded)
%              Number of equality atoms :    7 (  11 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_35,axiom,(
    ! [A] : r2_hidden(k4_tarski(A,k1_tarski(A)),k2_zfmisc_1(k1_tarski(A),k4_tarski(A,k1_tarski(A)))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t153_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_16,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_14,plain,(
    ~ r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_22,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_20,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_34,plain,(
    ! [A_20] : r2_hidden(k4_tarski(A_20,k1_tarski(A_20)),k2_zfmisc_1(k1_tarski(A_20),k4_tarski(A_20,k1_tarski(A_20)))) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_2,C_4,B_3,D_5] :
      ( r2_hidden(A_2,C_4)
      | ~ r2_hidden(k4_tarski(A_2,B_3),k2_zfmisc_1(C_4,D_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_41,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(resolution,[status(thm)],[c_34,c_8])).

tff(c_54,plain,(
    ! [D_27,C_28,B_29,A_30] :
      ( r2_hidden(k1_funct_1(D_27,C_28),B_29)
      | k1_xboole_0 = B_29
      | ~ r2_hidden(C_28,A_30)
      | ~ m1_subset_1(D_27,k1_zfmisc_1(k2_zfmisc_1(A_30,B_29)))
      | ~ v1_funct_2(D_27,A_30,B_29)
      | ~ v1_funct_1(D_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_67,plain,(
    ! [D_31,A_32,B_33] :
      ( r2_hidden(k1_funct_1(D_31,A_32),B_33)
      | k1_xboole_0 = B_33
      | ~ m1_subset_1(D_31,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_32),B_33)))
      | ~ v1_funct_2(D_31,k1_tarski(A_32),B_33)
      | ~ v1_funct_1(D_31) ) ),
    inference(resolution,[status(thm)],[c_41,c_54])).

tff(c_70,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2'
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_67])).

tff(c_73,plain,
    ( r2_hidden(k1_funct_1('#skF_3','#skF_1'),'#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20,c_70])).

tff(c_75,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_14,c_73])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:37:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.12  
% 1.71/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.13  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k4_tarski > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.71/1.13  
% 1.71/1.13  %Foreground sorts:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Background operators:
% 1.71/1.13  
% 1.71/1.13  
% 1.71/1.13  %Foreground operators:
% 1.71/1.13  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.71/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.71/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.71/1.13  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.71/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.71/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.71/1.13  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 1.71/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.71/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.71/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.71/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.71/1.13  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.71/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.71/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.71/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.71/1.13  
% 1.71/1.14  tff(f_59, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 1.71/1.14  tff(f_35, axiom, (![A]: r2_hidden(k4_tarski(A, k1_tarski(A)), k2_zfmisc_1(k1_tarski(A), k4_tarski(A, k1_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t153_zfmisc_1)).
% 1.71/1.14  tff(f_33, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.71/1.14  tff(f_47, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 1.71/1.14  tff(c_16, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.14  tff(c_14, plain, (~r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.14  tff(c_22, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.14  tff(c_20, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.14  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.71/1.14  tff(c_34, plain, (![A_20]: (r2_hidden(k4_tarski(A_20, k1_tarski(A_20)), k2_zfmisc_1(k1_tarski(A_20), k4_tarski(A_20, k1_tarski(A_20)))))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.71/1.14  tff(c_8, plain, (![A_2, C_4, B_3, D_5]: (r2_hidden(A_2, C_4) | ~r2_hidden(k4_tarski(A_2, B_3), k2_zfmisc_1(C_4, D_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.71/1.14  tff(c_41, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(resolution, [status(thm)], [c_34, c_8])).
% 1.71/1.14  tff(c_54, plain, (![D_27, C_28, B_29, A_30]: (r2_hidden(k1_funct_1(D_27, C_28), B_29) | k1_xboole_0=B_29 | ~r2_hidden(C_28, A_30) | ~m1_subset_1(D_27, k1_zfmisc_1(k2_zfmisc_1(A_30, B_29))) | ~v1_funct_2(D_27, A_30, B_29) | ~v1_funct_1(D_27))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.71/1.14  tff(c_67, plain, (![D_31, A_32, B_33]: (r2_hidden(k1_funct_1(D_31, A_32), B_33) | k1_xboole_0=B_33 | ~m1_subset_1(D_31, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_32), B_33))) | ~v1_funct_2(D_31, k1_tarski(A_32), B_33) | ~v1_funct_1(D_31))), inference(resolution, [status(thm)], [c_41, c_54])).
% 1.71/1.14  tff(c_70, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2' | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_18, c_67])).
% 1.71/1.14  tff(c_73, plain, (r2_hidden(k1_funct_1('#skF_3', '#skF_1'), '#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20, c_70])).
% 1.71/1.14  tff(c_75, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_14, c_73])).
% 1.71/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.14  
% 1.71/1.14  Inference rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Ref     : 0
% 1.71/1.14  #Sup     : 11
% 1.71/1.14  #Fact    : 0
% 1.71/1.14  #Define  : 0
% 1.71/1.14  #Split   : 0
% 1.71/1.14  #Chain   : 0
% 1.71/1.14  #Close   : 0
% 1.71/1.14  
% 1.71/1.14  Ordering : KBO
% 1.71/1.14  
% 1.71/1.14  Simplification rules
% 1.71/1.14  ----------------------
% 1.71/1.14  #Subsume      : 0
% 1.71/1.14  #Demod        : 2
% 1.71/1.14  #Tautology    : 4
% 1.71/1.14  #SimpNegUnit  : 1
% 1.71/1.14  #BackRed      : 0
% 1.71/1.14  
% 1.71/1.14  #Partial instantiations: 0
% 1.71/1.14  #Strategies tried      : 1
% 1.71/1.14  
% 1.71/1.14  Timing (in seconds)
% 1.71/1.14  ----------------------
% 1.71/1.14  Preprocessing        : 0.28
% 1.71/1.14  Parsing              : 0.15
% 1.71/1.14  CNF conversion       : 0.02
% 1.71/1.14  Main loop            : 0.11
% 1.71/1.14  Inferencing          : 0.04
% 1.71/1.14  Reduction            : 0.03
% 1.71/1.14  Demodulation         : 0.03
% 1.71/1.14  BG Simplification    : 0.01
% 1.71/1.14  Subsumption          : 0.02
% 1.71/1.14  Abstraction          : 0.01
% 1.71/1.14  MUC search           : 0.00
% 1.71/1.14  Cooper               : 0.00
% 1.71/1.14  Total                : 0.41
% 1.71/1.14  Index Insertion      : 0.00
% 1.71/1.14  Index Deletion       : 0.00
% 1.71/1.14  Index Matching       : 0.00
% 1.71/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
