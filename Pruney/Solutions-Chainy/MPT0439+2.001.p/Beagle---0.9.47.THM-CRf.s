%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:17 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   28 (  29 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_42,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_6,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_73,plain,(
    ! [A_15] :
      ( r1_tarski(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15)))
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_94,plain,(
    ! [A_17] :
      ( k4_xboole_0(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17))) = k1_xboole_0
      | ~ v1_relat_1(A_17) ) ),
    inference(resolution,[status(thm)],[c_73,c_4])).

tff(c_8,plain,(
    ! [A_4,B_5] : k4_xboole_0(A_4,k4_xboole_0(A_4,B_5)) = k3_xboole_0(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_100,plain,(
    ! [A_17] :
      ( k3_xboole_0(A_17,k2_zfmisc_1(k1_relat_1(A_17),k2_relat_1(A_17))) = k4_xboole_0(A_17,k1_xboole_0)
      | ~ v1_relat_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_8])).

tff(c_133,plain,(
    ! [A_20] :
      ( k3_xboole_0(A_20,k2_zfmisc_1(k1_relat_1(A_20),k2_relat_1(A_20))) = A_20
      | ~ v1_relat_1(A_20) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_100])).

tff(c_12,plain,(
    k3_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_142,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_12])).

tff(c_151,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:06:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  %$ r1_tarski > v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.62/1.15  
% 1.62/1.15  %Foreground sorts:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Background operators:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Foreground operators:
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.62/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.62/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.62/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.62/1.15  
% 1.62/1.15  tff(f_42, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 1.62/1.15  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.62/1.15  tff(f_37, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 1.62/1.15  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.62/1.15  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.62/1.15  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.15  tff(c_6, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.62/1.15  tff(c_73, plain, (![A_15]: (r1_tarski(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15))) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.62/1.15  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.62/1.15  tff(c_94, plain, (![A_17]: (k4_xboole_0(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17)))=k1_xboole_0 | ~v1_relat_1(A_17))), inference(resolution, [status(thm)], [c_73, c_4])).
% 1.62/1.15  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, k4_xboole_0(A_4, B_5))=k3_xboole_0(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.62/1.15  tff(c_100, plain, (![A_17]: (k3_xboole_0(A_17, k2_zfmisc_1(k1_relat_1(A_17), k2_relat_1(A_17)))=k4_xboole_0(A_17, k1_xboole_0) | ~v1_relat_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_94, c_8])).
% 1.62/1.15  tff(c_133, plain, (![A_20]: (k3_xboole_0(A_20, k2_zfmisc_1(k1_relat_1(A_20), k2_relat_1(A_20)))=A_20 | ~v1_relat_1(A_20))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_100])).
% 1.62/1.15  tff(c_12, plain, (k3_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.15  tff(c_142, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_133, c_12])).
% 1.62/1.15  tff(c_151, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_142])).
% 1.62/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  Inference rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Ref     : 0
% 1.62/1.15  #Sup     : 33
% 1.62/1.15  #Fact    : 0
% 1.62/1.15  #Define  : 0
% 1.62/1.15  #Split   : 0
% 1.62/1.15  #Chain   : 0
% 1.62/1.15  #Close   : 0
% 1.62/1.15  
% 1.62/1.15  Ordering : KBO
% 1.62/1.15  
% 1.62/1.15  Simplification rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Subsume      : 0
% 1.62/1.15  #Demod        : 12
% 1.62/1.15  #Tautology    : 22
% 1.62/1.15  #SimpNegUnit  : 0
% 1.62/1.15  #BackRed      : 0
% 1.62/1.15  
% 1.62/1.15  #Partial instantiations: 0
% 1.62/1.15  #Strategies tried      : 1
% 1.62/1.15  
% 1.62/1.15  Timing (in seconds)
% 1.62/1.15  ----------------------
% 1.62/1.16  Preprocessing        : 0.26
% 1.62/1.16  Parsing              : 0.15
% 1.62/1.16  CNF conversion       : 0.02
% 1.62/1.16  Main loop            : 0.14
% 1.62/1.16  Inferencing          : 0.07
% 1.62/1.16  Reduction            : 0.04
% 1.62/1.16  Demodulation         : 0.03
% 1.62/1.16  BG Simplification    : 0.01
% 1.62/1.16  Subsumption          : 0.02
% 1.62/1.16  Abstraction          : 0.01
% 1.62/1.16  MUC search           : 0.00
% 1.62/1.16  Cooper               : 0.00
% 1.62/1.16  Total                : 0.43
% 1.62/1.16  Index Insertion      : 0.00
% 1.62/1.16  Index Deletion       : 0.00
% 1.62/1.16  Index Matching       : 0.00
% 1.62/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------
