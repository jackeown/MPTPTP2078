%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:10 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   26 (  26 expanded)
%              Number of leaves         :   17 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_35,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(k1_tarski(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

tff(f_54,negated_conjecture,(
    ~ ! [A] : m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1(A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_setfam_1)).

tff(c_8,plain,(
    ! [A_4] : ~ v1_xboole_0(k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_55,plain,(
    ! [A_20,B_21] :
      ( r2_hidden(A_20,B_21)
      | v1_xboole_0(B_21)
      | ~ m1_subset_1(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k1_tarski(A_18),k1_zfmisc_1(B_19))
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_18,plain,(
    ~ m1_subset_1(k1_tarski(k1_xboole_0),k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_54,plain,(
    ~ r2_hidden(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_47,c_18])).

tff(c_58,plain,
    ( v1_xboole_0(k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_55,c_54])).

tff(c_61,plain,(
    v1_xboole_0(k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_58])).

tff(c_63,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:51:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.44  
% 2.09/1.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.44  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1
% 2.09/1.44  
% 2.09/1.44  %Foreground sorts:
% 2.09/1.44  
% 2.09/1.44  
% 2.09/1.44  %Background operators:
% 2.09/1.44  
% 2.09/1.44  
% 2.09/1.44  %Foreground operators:
% 2.09/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.44  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.44  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.09/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.09/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.09/1.44  
% 2.14/1.45  tff(f_33, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.14/1.45  tff(f_35, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.14/1.45  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.14/1.45  tff(f_39, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(k1_tarski(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_subset_1)).
% 2.14/1.45  tff(f_54, negated_conjecture, ~(![A]: m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_setfam_1)).
% 2.14/1.45  tff(c_8, plain, (![A_4]: (~v1_xboole_0(k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.45  tff(c_10, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.14/1.45  tff(c_55, plain, (![A_20, B_21]: (r2_hidden(A_20, B_21) | v1_xboole_0(B_21) | ~m1_subset_1(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.14/1.45  tff(c_47, plain, (![A_18, B_19]: (m1_subset_1(k1_tarski(A_18), k1_zfmisc_1(B_19)) | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.14/1.45  tff(c_18, plain, (~m1_subset_1(k1_tarski(k1_xboole_0), k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.14/1.45  tff(c_54, plain, (~r2_hidden(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_47, c_18])).
% 2.14/1.45  tff(c_58, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_55, c_54])).
% 2.14/1.45  tff(c_61, plain, (v1_xboole_0(k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_58])).
% 2.14/1.45  tff(c_63, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_61])).
% 2.14/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.45  
% 2.14/1.45  Inference rules
% 2.14/1.45  ----------------------
% 2.14/1.45  #Ref     : 0
% 2.14/1.45  #Sup     : 11
% 2.14/1.45  #Fact    : 0
% 2.14/1.45  #Define  : 0
% 2.14/1.45  #Split   : 0
% 2.14/1.46  #Chain   : 0
% 2.14/1.46  #Close   : 0
% 2.14/1.46  
% 2.14/1.46  Ordering : KBO
% 2.14/1.46  
% 2.14/1.46  Simplification rules
% 2.14/1.46  ----------------------
% 2.14/1.46  #Subsume      : 0
% 2.14/1.46  #Demod        : 1
% 2.14/1.46  #Tautology    : 6
% 2.14/1.46  #SimpNegUnit  : 1
% 2.14/1.46  #BackRed      : 0
% 2.14/1.46  
% 2.14/1.46  #Partial instantiations: 0
% 2.14/1.46  #Strategies tried      : 1
% 2.14/1.46  
% 2.14/1.46  Timing (in seconds)
% 2.14/1.46  ----------------------
% 2.14/1.46  Preprocessing        : 0.45
% 2.14/1.46  Parsing              : 0.23
% 2.14/1.46  CNF conversion       : 0.03
% 2.14/1.46  Main loop            : 0.15
% 2.14/1.46  Inferencing          : 0.07
% 2.14/1.46  Reduction            : 0.04
% 2.14/1.46  Demodulation         : 0.03
% 2.14/1.46  BG Simplification    : 0.01
% 2.14/1.46  Subsumption          : 0.01
% 2.14/1.46  Abstraction          : 0.01
% 2.14/1.46  MUC search           : 0.00
% 2.14/1.46  Cooper               : 0.00
% 2.14/1.46  Total                : 0.63
% 2.14/1.46  Index Insertion      : 0.00
% 2.14/1.46  Index Deletion       : 0.00
% 2.14/1.46  Index Matching       : 0.00
% 2.14/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
