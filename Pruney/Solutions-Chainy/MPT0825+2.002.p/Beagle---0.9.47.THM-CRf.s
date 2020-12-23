%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:13 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_27,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_38,negated_conjecture,(
    ~ ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).

tff(c_2,plain,(
    ! [A_1] : v1_relat_1(k6_relat_1(A_1)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_3] : k2_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3] : k1_relat_1(k6_relat_1(A_3)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    ! [A_7] :
      ( r1_tarski(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7)))
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_33,plain,(
    ! [A_3] :
      ( r1_tarski(k6_relat_1(A_3),k2_zfmisc_1(A_3,k2_relat_1(k6_relat_1(A_3))))
      | ~ v1_relat_1(k6_relat_1(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_30])).

tff(c_38,plain,(
    ! [A_3] : r1_tarski(k6_relat_1(A_3),k2_zfmisc_1(A_3,A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8,c_33])).

tff(c_10,plain,(
    ~ r1_tarski(k6_relat_1('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_43,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:54:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.12  
% 1.62/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.13  %$ r1_tarski > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 1.62/1.13  
% 1.62/1.13  %Foreground sorts:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Background operators:
% 1.62/1.13  
% 1.62/1.13  
% 1.62/1.13  %Foreground operators:
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.13  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.62/1.13  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.62/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.13  
% 1.62/1.14  tff(f_27, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 1.62/1.14  tff(f_35, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 1.62/1.14  tff(f_31, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.62/1.14  tff(f_38, negated_conjecture, ~(![A]: r1_tarski(k6_relat_1(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relset_1)).
% 1.62/1.14  tff(c_2, plain, (![A_1]: (v1_relat_1(k6_relat_1(A_1)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.14  tff(c_8, plain, (![A_3]: (k2_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.14  tff(c_6, plain, (![A_3]: (k1_relat_1(k6_relat_1(A_3))=A_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.62/1.14  tff(c_30, plain, (![A_7]: (r1_tarski(A_7, k2_zfmisc_1(k1_relat_1(A_7), k2_relat_1(A_7))) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.14  tff(c_33, plain, (![A_3]: (r1_tarski(k6_relat_1(A_3), k2_zfmisc_1(A_3, k2_relat_1(k6_relat_1(A_3)))) | ~v1_relat_1(k6_relat_1(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_30])).
% 1.62/1.14  tff(c_38, plain, (![A_3]: (r1_tarski(k6_relat_1(A_3), k2_zfmisc_1(A_3, A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8, c_33])).
% 1.62/1.14  tff(c_10, plain, (~r1_tarski(k6_relat_1('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.62/1.14  tff(c_43, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_10])).
% 1.62/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  Inference rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Ref     : 0
% 1.62/1.14  #Sup     : 6
% 1.62/1.14  #Fact    : 0
% 1.62/1.14  #Define  : 0
% 1.62/1.14  #Split   : 0
% 1.62/1.14  #Chain   : 0
% 1.62/1.14  #Close   : 0
% 1.62/1.14  
% 1.62/1.14  Ordering : KBO
% 1.62/1.14  
% 1.62/1.14  Simplification rules
% 1.62/1.14  ----------------------
% 1.62/1.14  #Subsume      : 0
% 1.62/1.14  #Demod        : 5
% 1.62/1.14  #Tautology    : 4
% 1.62/1.14  #SimpNegUnit  : 0
% 1.62/1.14  #BackRed      : 1
% 1.62/1.14  
% 1.62/1.14  #Partial instantiations: 0
% 1.62/1.14  #Strategies tried      : 1
% 1.62/1.14  
% 1.62/1.14  Timing (in seconds)
% 1.62/1.14  ----------------------
% 1.62/1.14  Preprocessing        : 0.25
% 1.62/1.14  Parsing              : 0.14
% 1.62/1.14  CNF conversion       : 0.01
% 1.62/1.14  Main loop            : 0.07
% 1.62/1.14  Inferencing          : 0.03
% 1.62/1.14  Reduction            : 0.02
% 1.62/1.14  Demodulation         : 0.02
% 1.62/1.14  BG Simplification    : 0.01
% 1.62/1.14  Subsumption          : 0.01
% 1.62/1.15  Abstraction          : 0.00
% 1.62/1.15  MUC search           : 0.00
% 1.62/1.15  Cooper               : 0.00
% 1.62/1.15  Total                : 0.35
% 1.62/1.15  Index Insertion      : 0.00
% 1.67/1.15  Index Deletion       : 0.00
% 1.67/1.15  Index Matching       : 0.00
% 1.67/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
