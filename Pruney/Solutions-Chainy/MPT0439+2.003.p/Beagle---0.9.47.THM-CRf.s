%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:18 EST 2020

% Result     : Theorem 1.50s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    5 (   6 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_38,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(c_8,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_10,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = A_1
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15,plain,(
    ! [A_7] :
      ( k3_xboole_0(A_7,k2_zfmisc_1(k1_relat_1(A_7),k2_relat_1(A_7))) = A_7
      | ~ v1_relat_1(A_7) ) ),
    inference(resolution,[status(thm)],[c_10,c_2])).

tff(c_6,plain,(
    k3_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_21,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_15,c_6])).

tff(c_29,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n015.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:59:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.50/1.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.05  
% 1.50/1.05  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.06  %$ r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > #skF_1
% 1.50/1.06  
% 1.50/1.06  %Foreground sorts:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Background operators:
% 1.50/1.06  
% 1.50/1.06  
% 1.50/1.06  %Foreground operators:
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.50/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.50/1.06  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.50/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.50/1.06  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.50/1.06  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.50/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.50/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.50/1.06  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.50/1.06  
% 1.50/1.06  tff(f_38, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 1.50/1.06  tff(f_33, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_relat_1)).
% 1.50/1.06  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.50/1.06  tff(c_8, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.50/1.06  tff(c_10, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.50/1.06  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=A_1 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.50/1.06  tff(c_15, plain, (![A_7]: (k3_xboole_0(A_7, k2_zfmisc_1(k1_relat_1(A_7), k2_relat_1(A_7)))=A_7 | ~v1_relat_1(A_7))), inference(resolution, [status(thm)], [c_10, c_2])).
% 1.50/1.06  tff(c_6, plain, (k3_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.50/1.06  tff(c_21, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_15, c_6])).
% 1.50/1.06  tff(c_29, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_21])).
% 1.50/1.06  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.50/1.06  
% 1.50/1.06  Inference rules
% 1.50/1.06  ----------------------
% 1.50/1.06  #Ref     : 0
% 1.50/1.06  #Sup     : 4
% 1.50/1.06  #Fact    : 0
% 1.50/1.06  #Define  : 0
% 1.50/1.06  #Split   : 0
% 1.50/1.06  #Chain   : 0
% 1.50/1.06  #Close   : 0
% 1.50/1.06  
% 1.50/1.06  Ordering : KBO
% 1.50/1.06  
% 1.50/1.06  Simplification rules
% 1.50/1.06  ----------------------
% 1.50/1.06  #Subsume      : 0
% 1.50/1.06  #Demod        : 1
% 1.50/1.06  #Tautology    : 1
% 1.50/1.06  #SimpNegUnit  : 0
% 1.50/1.06  #BackRed      : 0
% 1.50/1.06  
% 1.50/1.06  #Partial instantiations: 0
% 1.50/1.06  #Strategies tried      : 1
% 1.50/1.06  
% 1.50/1.06  Timing (in seconds)
% 1.50/1.06  ----------------------
% 1.50/1.07  Preprocessing        : 0.24
% 1.50/1.07  Parsing              : 0.14
% 1.50/1.07  CNF conversion       : 0.01
% 1.50/1.07  Main loop            : 0.07
% 1.50/1.07  Inferencing          : 0.04
% 1.50/1.07  Reduction            : 0.01
% 1.50/1.07  Demodulation         : 0.01
% 1.50/1.07  BG Simplification    : 0.01
% 1.50/1.07  Subsumption          : 0.00
% 1.50/1.07  Abstraction          : 0.00
% 1.50/1.07  MUC search           : 0.00
% 1.50/1.07  Cooper               : 0.00
% 1.50/1.07  Total                : 0.33
% 1.50/1.07  Index Insertion      : 0.00
% 1.50/1.07  Index Deletion       : 0.00
% 1.50/1.07  Index Matching       : 0.00
% 1.50/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------
