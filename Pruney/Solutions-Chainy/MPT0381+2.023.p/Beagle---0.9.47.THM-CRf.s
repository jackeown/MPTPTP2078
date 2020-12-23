%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:04 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   42 (  53 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    8
%              Number of atoms          :   46 (  63 expanded)
%              Number of equality atoms :    9 (   9 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_33,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_41,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,A)
     => ( A != k1_xboole_0
       => m1_subset_1(k1_tarski(B),k1_zfmisc_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_subset_1)).

tff(c_6,plain,(
    v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ! [B_22,A_23] :
      ( ~ r2_hidden(B_22,A_23)
      | ~ v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_40])).

tff(c_96,plain,(
    ! [B_35,A_36] :
      ( m1_subset_1(B_35,A_36)
      | ~ r2_hidden(B_35,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_105,plain,
    ( m1_subset_1('#skF_4','#skF_5')
    | v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_30,c_96])).

tff(c_110,plain,(
    m1_subset_1('#skF_4','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_105])).

tff(c_45,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_3'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_50,plain,(
    ! [A_25] :
      ( ~ v1_xboole_0(A_25)
      | k1_xboole_0 = A_25 ) ),
    inference(resolution,[status(thm)],[c_45,c_2])).

tff(c_54,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_6,c_50])).

tff(c_26,plain,(
    ! [B_20,A_19] :
      ( m1_subset_1(k1_tarski(B_20),k1_zfmisc_1(A_19))
      | k1_xboole_0 = A_19
      | ~ m1_subset_1(B_20,A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_145,plain,(
    ! [B_44,A_45] :
      ( m1_subset_1(k1_tarski(B_44),k1_zfmisc_1(A_45))
      | A_45 = '#skF_2'
      | ~ m1_subset_1(B_44,A_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_26])).

tff(c_28,plain,(
    ~ m1_subset_1(k1_tarski('#skF_4'),k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_151,plain,
    ( '#skF_5' = '#skF_2'
    | ~ m1_subset_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_145,c_28])).

tff(c_155,plain,(
    '#skF_5' = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_151])).

tff(c_158,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_155,c_44])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n003.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:17:57 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.95/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.95/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.95/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.95/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.95/1.23  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.95/1.23  
% 1.95/1.24  tff(f_33, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.95/1.24  tff(f_74, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 1.95/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.95/1.24  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 1.95/1.24  tff(f_41, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.95/1.24  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, A) => (~(A = k1_xboole_0) => m1_subset_1(k1_tarski(B), k1_zfmisc_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_subset_1)).
% 1.95/1.24  tff(c_6, plain, (v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.95/1.24  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.24  tff(c_40, plain, (![B_22, A_23]: (~r2_hidden(B_22, A_23) | ~v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.24  tff(c_44, plain, (~v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_40])).
% 1.95/1.24  tff(c_96, plain, (![B_35, A_36]: (m1_subset_1(B_35, A_36) | ~r2_hidden(B_35, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.95/1.24  tff(c_105, plain, (m1_subset_1('#skF_4', '#skF_5') | v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_30, c_96])).
% 1.95/1.24  tff(c_110, plain, (m1_subset_1('#skF_4', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_105])).
% 1.95/1.24  tff(c_45, plain, (![A_24]: (r2_hidden('#skF_3'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.95/1.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.24  tff(c_50, plain, (![A_25]: (~v1_xboole_0(A_25) | k1_xboole_0=A_25)), inference(resolution, [status(thm)], [c_45, c_2])).
% 1.95/1.24  tff(c_54, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_6, c_50])).
% 1.95/1.24  tff(c_26, plain, (![B_20, A_19]: (m1_subset_1(k1_tarski(B_20), k1_zfmisc_1(A_19)) | k1_xboole_0=A_19 | ~m1_subset_1(B_20, A_19))), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.95/1.24  tff(c_145, plain, (![B_44, A_45]: (m1_subset_1(k1_tarski(B_44), k1_zfmisc_1(A_45)) | A_45='#skF_2' | ~m1_subset_1(B_44, A_45))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_26])).
% 1.95/1.24  tff(c_28, plain, (~m1_subset_1(k1_tarski('#skF_4'), k1_zfmisc_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 1.95/1.24  tff(c_151, plain, ('#skF_5'='#skF_2' | ~m1_subset_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_145, c_28])).
% 1.95/1.24  tff(c_155, plain, ('#skF_5'='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_110, c_151])).
% 1.95/1.24  tff(c_158, plain, (~v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_155, c_44])).
% 1.95/1.24  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_158])).
% 1.95/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  Inference rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Ref     : 0
% 1.95/1.24  #Sup     : 26
% 1.95/1.24  #Fact    : 0
% 1.95/1.24  #Define  : 0
% 1.95/1.24  #Split   : 1
% 1.95/1.24  #Chain   : 0
% 1.95/1.24  #Close   : 0
% 1.95/1.24  
% 1.95/1.24  Ordering : KBO
% 1.95/1.24  
% 1.95/1.24  Simplification rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Subsume      : 3
% 1.95/1.24  #Demod        : 10
% 1.95/1.24  #Tautology    : 14
% 1.95/1.24  #SimpNegUnit  : 1
% 1.95/1.24  #BackRed      : 7
% 1.95/1.24  
% 1.95/1.24  #Partial instantiations: 0
% 1.95/1.24  #Strategies tried      : 1
% 1.95/1.24  
% 1.95/1.24  Timing (in seconds)
% 1.95/1.24  ----------------------
% 1.95/1.24  Preprocessing        : 0.31
% 1.95/1.24  Parsing              : 0.16
% 1.95/1.24  CNF conversion       : 0.02
% 1.95/1.24  Main loop            : 0.15
% 1.95/1.24  Inferencing          : 0.06
% 1.95/1.24  Reduction            : 0.04
% 1.95/1.24  Demodulation         : 0.03
% 1.95/1.24  BG Simplification    : 0.02
% 1.95/1.25  Subsumption          : 0.03
% 1.95/1.25  Abstraction          : 0.01
% 1.95/1.25  MUC search           : 0.00
% 1.95/1.25  Cooper               : 0.00
% 1.95/1.25  Total                : 0.48
% 1.95/1.25  Index Insertion      : 0.00
% 1.95/1.25  Index Deletion       : 0.00
% 1.95/1.25  Index Matching       : 0.00
% 1.95/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
