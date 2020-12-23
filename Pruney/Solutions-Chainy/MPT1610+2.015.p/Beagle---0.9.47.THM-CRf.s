%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:31 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_yellow_0,type,(
    k3_yellow_0: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_37,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_49,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_58,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_56,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k1_xboole_0,A)
       => k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_yellow_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A] : k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_yellow_1)).

tff(c_16,plain,(
    ! [A_7] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_53,plain,(
    ! [A_22,B_23] :
      ( r1_tarski(A_22,B_23)
      | ~ m1_subset_1(A_22,k1_zfmisc_1(B_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_57,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(resolution,[status(thm)],[c_16,c_53])).

tff(c_4,plain,(
    ! [C_5,A_1] :
      ( r2_hidden(C_5,k1_zfmisc_1(A_1))
      | ~ r1_tarski(C_5,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_6] : ~ v1_xboole_0(k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_24,plain,(
    ! [A_13] : k9_setfam_1(A_13) = k1_zfmisc_1(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_15] : k2_yellow_1(k9_setfam_1(A_15)) = k3_yellow_1(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,(
    ! [A_15] : k2_yellow_1(k1_zfmisc_1(A_15)) = k3_yellow_1(A_15) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_28])).

tff(c_69,plain,(
    ! [A_29] :
      ( k3_yellow_0(k2_yellow_1(A_29)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,A_29)
      | v1_xboole_0(A_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_78,plain,(
    ! [A_15] :
      ( k3_yellow_0(k3_yellow_1(A_15)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_31,c_69])).

tff(c_82,plain,(
    ! [A_30] :
      ( k3_yellow_0(k3_yellow_1(A_30)) = k1_xboole_0
      | ~ r2_hidden(k1_xboole_0,k1_zfmisc_1(A_30)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_78])).

tff(c_86,plain,(
    ! [A_1] :
      ( k3_yellow_0(k3_yellow_1(A_1)) = k1_xboole_0
      | ~ r1_tarski(k1_xboole_0,A_1) ) ),
    inference(resolution,[status(thm)],[c_4,c_82])).

tff(c_89,plain,(
    ! [A_1] : k3_yellow_0(k3_yellow_1(A_1)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_57,c_86])).

tff(c_30,plain,(
    k3_yellow_0(k3_yellow_1('#skF_3')) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_89,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.13  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > #nlpp > k9_setfam_1 > k3_yellow_1 > k3_yellow_0 > k2_yellow_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.69/1.13  
% 1.69/1.13  %Foreground sorts:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Background operators:
% 1.69/1.13  
% 1.69/1.13  
% 1.69/1.13  %Foreground operators:
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.13  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 1.69/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.13  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 1.69/1.13  tff(k3_yellow_0, type, k3_yellow_0: $i > $i).
% 1.69/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.69/1.13  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 1.69/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.69/1.13  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.13  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.69/1.13  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.69/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.69/1.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.69/1.13  
% 1.69/1.14  tff(f_37, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 1.69/1.14  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 1.69/1.14  tff(f_32, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 1.69/1.14  tff(f_35, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 1.69/1.14  tff(f_49, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 1.69/1.14  tff(f_58, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 1.69/1.14  tff(f_56, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k1_xboole_0, A) => (k3_yellow_0(k2_yellow_1(A)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_yellow_1)).
% 1.69/1.14  tff(f_61, negated_conjecture, ~(![A]: (k3_yellow_0(k3_yellow_1(A)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_yellow_1)).
% 1.69/1.14  tff(c_16, plain, (![A_7]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.69/1.14  tff(c_53, plain, (![A_22, B_23]: (r1_tarski(A_22, B_23) | ~m1_subset_1(A_22, k1_zfmisc_1(B_23)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.69/1.14  tff(c_57, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(resolution, [status(thm)], [c_16, c_53])).
% 1.69/1.14  tff(c_4, plain, (![C_5, A_1]: (r2_hidden(C_5, k1_zfmisc_1(A_1)) | ~r1_tarski(C_5, A_1))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.69/1.14  tff(c_14, plain, (![A_6]: (~v1_xboole_0(k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.69/1.14  tff(c_24, plain, (![A_13]: (k9_setfam_1(A_13)=k1_zfmisc_1(A_13))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.69/1.14  tff(c_28, plain, (![A_15]: (k2_yellow_1(k9_setfam_1(A_15))=k3_yellow_1(A_15))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.69/1.14  tff(c_31, plain, (![A_15]: (k2_yellow_1(k1_zfmisc_1(A_15))=k3_yellow_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_28])).
% 1.69/1.14  tff(c_69, plain, (![A_29]: (k3_yellow_0(k2_yellow_1(A_29))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, A_29) | v1_xboole_0(A_29))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.14  tff(c_78, plain, (![A_15]: (k3_yellow_0(k3_yellow_1(A_15))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_31, c_69])).
% 1.69/1.14  tff(c_82, plain, (![A_30]: (k3_yellow_0(k3_yellow_1(A_30))=k1_xboole_0 | ~r2_hidden(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(negUnitSimplification, [status(thm)], [c_14, c_78])).
% 1.69/1.14  tff(c_86, plain, (![A_1]: (k3_yellow_0(k3_yellow_1(A_1))=k1_xboole_0 | ~r1_tarski(k1_xboole_0, A_1))), inference(resolution, [status(thm)], [c_4, c_82])).
% 1.69/1.14  tff(c_89, plain, (![A_1]: (k3_yellow_0(k3_yellow_1(A_1))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_57, c_86])).
% 1.69/1.14  tff(c_30, plain, (k3_yellow_0(k3_yellow_1('#skF_3'))!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.69/1.14  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_89, c_30])).
% 1.69/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  Inference rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Ref     : 0
% 1.69/1.14  #Sup     : 11
% 1.69/1.14  #Fact    : 0
% 1.69/1.14  #Define  : 0
% 1.69/1.14  #Split   : 0
% 1.69/1.14  #Chain   : 0
% 1.69/1.14  #Close   : 0
% 1.69/1.14  
% 1.69/1.14  Ordering : KBO
% 1.69/1.14  
% 1.69/1.14  Simplification rules
% 1.69/1.14  ----------------------
% 1.69/1.14  #Subsume      : 0
% 1.69/1.14  #Demod        : 4
% 1.69/1.14  #Tautology    : 9
% 1.69/1.14  #SimpNegUnit  : 1
% 1.69/1.14  #BackRed      : 1
% 1.69/1.14  
% 1.69/1.14  #Partial instantiations: 0
% 1.69/1.14  #Strategies tried      : 1
% 1.69/1.14  
% 1.69/1.14  Timing (in seconds)
% 1.69/1.14  ----------------------
% 1.69/1.14  Preprocessing        : 0.30
% 1.69/1.14  Parsing              : 0.16
% 1.69/1.14  CNF conversion       : 0.02
% 1.69/1.14  Main loop            : 0.09
% 1.69/1.14  Inferencing          : 0.04
% 1.69/1.14  Reduction            : 0.03
% 1.69/1.14  Demodulation         : 0.02
% 1.69/1.15  BG Simplification    : 0.01
% 1.69/1.15  Subsumption          : 0.01
% 1.69/1.15  Abstraction          : 0.01
% 1.69/1.15  MUC search           : 0.00
% 1.69/1.15  Cooper               : 0.00
% 1.69/1.15  Total                : 0.42
% 1.69/1.15  Index Insertion      : 0.00
% 1.69/1.15  Index Deletion       : 0.00
% 1.69/1.15  Index Matching       : 0.00
% 1.69/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
