%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:13 EST 2020

% Result     : Theorem 1.47s
% Output     : CNFRefutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :    4 (   6 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v2_funct_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

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

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_33,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_40,negated_conjecture,(
    ~ ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_relset_1)).

tff(c_8,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_2] : k1_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_2] : k2_relat_1(k6_relat_1(A_2)) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_33,plain,(
    ! [A_8] :
      ( r1_tarski(A_8,k2_zfmisc_1(k1_relat_1(A_8),k2_relat_1(A_8)))
      | ~ v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_2] :
      ( r1_tarski(k6_relat_1(A_2),k2_zfmisc_1(k1_relat_1(k6_relat_1(A_2)),A_2))
      | ~ v1_relat_1(k6_relat_1(A_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_33])).

tff(c_41,plain,(
    ! [A_2] : r1_tarski(k6_relat_1(A_2),k2_zfmisc_1(A_2,A_2)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4,c_36])).

tff(c_12,plain,(
    ~ r1_tarski(k6_relat_1('#skF_1'),k2_zfmisc_1('#skF_1','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_46,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_41,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:54:59 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.47/1.03  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.03  
% 1.47/1.03  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.04  %$ r1_tarski > v2_funct_1 > v1_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_relat_1 > #skF_1
% 1.47/1.04  
% 1.47/1.04  %Foreground sorts:
% 1.47/1.04  
% 1.47/1.04  
% 1.47/1.04  %Background operators:
% 1.47/1.04  
% 1.47/1.04  
% 1.47/1.04  %Foreground operators:
% 1.47/1.04  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 1.47/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.47/1.04  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.47/1.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.47/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.47/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.47/1.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.47/1.04  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.47/1.04  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.47/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.47/1.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.47/1.04  
% 1.47/1.05  tff(f_37, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 1.47/1.05  tff(f_33, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 1.47/1.05  tff(f_29, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.47/1.05  tff(f_40, negated_conjecture, ~(![A]: r1_tarski(k6_relat_1(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_relset_1)).
% 1.47/1.05  tff(c_8, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.47/1.05  tff(c_4, plain, (![A_2]: (k1_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.47/1.05  tff(c_6, plain, (![A_2]: (k2_relat_1(k6_relat_1(A_2))=A_2)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.47/1.05  tff(c_33, plain, (![A_8]: (r1_tarski(A_8, k2_zfmisc_1(k1_relat_1(A_8), k2_relat_1(A_8))) | ~v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.47/1.05  tff(c_36, plain, (![A_2]: (r1_tarski(k6_relat_1(A_2), k2_zfmisc_1(k1_relat_1(k6_relat_1(A_2)), A_2)) | ~v1_relat_1(k6_relat_1(A_2)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_33])).
% 1.47/1.05  tff(c_41, plain, (![A_2]: (r1_tarski(k6_relat_1(A_2), k2_zfmisc_1(A_2, A_2)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4, c_36])).
% 1.47/1.05  tff(c_12, plain, (~r1_tarski(k6_relat_1('#skF_1'), k2_zfmisc_1('#skF_1', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.47/1.05  tff(c_46, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_41, c_12])).
% 1.47/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.47/1.05  
% 1.47/1.05  Inference rules
% 1.47/1.05  ----------------------
% 1.47/1.05  #Ref     : 0
% 1.47/1.05  #Sup     : 6
% 1.47/1.05  #Fact    : 0
% 1.47/1.05  #Define  : 0
% 1.47/1.05  #Split   : 0
% 1.47/1.05  #Chain   : 0
% 1.47/1.05  #Close   : 0
% 1.47/1.05  
% 1.47/1.05  Ordering : KBO
% 1.47/1.05  
% 1.47/1.05  Simplification rules
% 1.47/1.05  ----------------------
% 1.47/1.05  #Subsume      : 0
% 1.47/1.05  #Demod        : 5
% 1.47/1.05  #Tautology    : 4
% 1.47/1.05  #SimpNegUnit  : 0
% 1.47/1.05  #BackRed      : 1
% 1.47/1.05  
% 1.47/1.05  #Partial instantiations: 0
% 1.47/1.05  #Strategies tried      : 1
% 1.47/1.05  
% 1.47/1.05  Timing (in seconds)
% 1.47/1.05  ----------------------
% 1.47/1.05  Preprocessing        : 0.24
% 1.47/1.05  Parsing              : 0.14
% 1.47/1.05  CNF conversion       : 0.01
% 1.47/1.05  Main loop            : 0.06
% 1.47/1.05  Inferencing          : 0.03
% 1.47/1.05  Reduction            : 0.02
% 1.47/1.05  Demodulation         : 0.02
% 1.47/1.05  BG Simplification    : 0.01
% 1.47/1.05  Subsumption          : 0.01
% 1.47/1.05  Abstraction          : 0.00
% 1.47/1.05  MUC search           : 0.00
% 1.47/1.05  Cooper               : 0.00
% 1.47/1.05  Total                : 0.33
% 1.47/1.05  Index Insertion      : 0.00
% 1.47/1.05  Index Deletion       : 0.00
% 1.47/1.05  Index Matching       : 0.00
% 1.47/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------
