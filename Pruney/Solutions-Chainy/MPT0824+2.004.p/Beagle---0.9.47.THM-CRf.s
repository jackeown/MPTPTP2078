%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:13 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.56s
% Verified   : 
% Statistics : Number of formulae       :   15 (  15 expanded)
%              Number of leaves         :   12 (  12 expanded)
%              Depth                    :    2
%              Number of atoms          :    5 (   5 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_36,negated_conjecture,(
    ~ ! [A,B] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relset_1)).

tff(c_2,plain,(
    ! [A_1] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:19:54 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.04  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.47/1.04  
% 1.47/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.06  %$ r2_hidden > m1_subset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.56/1.06  
% 1.56/1.06  %Foreground sorts:
% 1.56/1.06  
% 1.56/1.06  
% 1.56/1.06  %Background operators:
% 1.56/1.06  
% 1.56/1.06  
% 1.56/1.06  %Foreground operators:
% 1.56/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.56/1.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.56/1.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.56/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.56/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.56/1.06  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.56/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.56/1.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.56/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.56/1.06  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.56/1.06  
% 1.56/1.06  tff(f_27, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 1.56/1.06  tff(f_36, negated_conjecture, ~(![A, B]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relset_1)).
% 1.56/1.06  tff(c_2, plain, (![A_1]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.56/1.06  tff(c_6, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.56/1.06  tff(c_8, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.56/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.56/1.06  
% 1.56/1.06  Inference rules
% 1.56/1.06  ----------------------
% 1.56/1.06  #Ref     : 0
% 1.56/1.06  #Sup     : 0
% 1.56/1.06  #Fact    : 0
% 1.56/1.06  #Define  : 0
% 1.56/1.06  #Split   : 0
% 1.56/1.06  #Chain   : 0
% 1.56/1.06  #Close   : 0
% 1.56/1.06  
% 1.56/1.06  Ordering : KBO
% 1.56/1.06  
% 1.56/1.06  Simplification rules
% 1.56/1.06  ----------------------
% 1.56/1.06  #Subsume      : 2
% 1.56/1.06  #Demod        : 1
% 1.56/1.06  #Tautology    : 0
% 1.56/1.06  #SimpNegUnit  : 0
% 1.56/1.06  #BackRed      : 0
% 1.56/1.06  
% 1.56/1.06  #Partial instantiations: 0
% 1.56/1.06  #Strategies tried      : 1
% 1.56/1.06  
% 1.56/1.06  Timing (in seconds)
% 1.56/1.06  ----------------------
% 1.56/1.07  Preprocessing        : 0.23
% 1.56/1.07  Parsing              : 0.12
% 1.56/1.07  CNF conversion       : 0.01
% 1.56/1.07  Main loop            : 0.02
% 1.56/1.07  Inferencing          : 0.00
% 1.56/1.07  Reduction            : 0.01
% 1.56/1.07  Demodulation         : 0.01
% 1.56/1.07  BG Simplification    : 0.01
% 1.56/1.07  Subsumption          : 0.00
% 1.56/1.07  Abstraction          : 0.00
% 1.56/1.07  MUC search           : 0.00
% 1.56/1.07  Cooper               : 0.00
% 1.56/1.07  Total                : 0.28
% 1.56/1.07  Index Insertion      : 0.00
% 1.56/1.07  Index Deletion       : 0.00
% 1.56/1.07  Index Matching       : 0.00
% 1.56/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
