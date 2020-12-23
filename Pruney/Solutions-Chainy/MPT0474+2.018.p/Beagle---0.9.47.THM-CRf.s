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
% DateTime   : Thu Dec  3 09:59:30 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   23 (  36 expanded)
%              Number of leaves         :   12 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   23 (  41 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :    4 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_39,negated_conjecture,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ( v1_xboole_0(k4_relat_1(A))
        & v1_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_15,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_11])).

tff(c_10,plain,(
    k4_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_17,plain,(
    k4_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_15,c_10])).

tff(c_29,plain,(
    ! [A_6] :
      ( v1_xboole_0(k4_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_15,c_2])).

tff(c_34,plain,(
    ! [A_7] :
      ( k4_relat_1(A_7) = '#skF_1'
      | ~ v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_29,c_16])).

tff(c_40,plain,(
    k4_relat_1('#skF_1') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_34])).

tff(c_45,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_17,c_40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:49:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.14  
% 1.55/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.14  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k4_relat_1 > k1_xboole_0 > #skF_1
% 1.55/1.14  
% 1.55/1.14  %Foreground sorts:
% 1.55/1.14  
% 1.55/1.14  
% 1.55/1.14  %Background operators:
% 1.55/1.14  
% 1.55/1.14  
% 1.55/1.14  %Foreground operators:
% 1.55/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.55/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.14  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.55/1.14  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 1.55/1.14  
% 1.55/1.15  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.55/1.15  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.55/1.15  tff(f_39, negated_conjecture, ~(k4_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_relat_1)).
% 1.55/1.15  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => (v1_xboole_0(k4_relat_1(A)) & v1_relat_1(k4_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_relat_1)).
% 1.55/1.15  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.15  tff(c_11, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.15  tff(c_15, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_11])).
% 1.55/1.15  tff(c_10, plain, (k4_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.55/1.15  tff(c_17, plain, (k4_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_15, c_15, c_10])).
% 1.55/1.15  tff(c_29, plain, (![A_6]: (v1_xboole_0(k4_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.55/1.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.15  tff(c_16, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_15, c_2])).
% 1.55/1.15  tff(c_34, plain, (![A_7]: (k4_relat_1(A_7)='#skF_1' | ~v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_29, c_16])).
% 1.55/1.15  tff(c_40, plain, (k4_relat_1('#skF_1')='#skF_1'), inference(resolution, [status(thm)], [c_4, c_34])).
% 1.55/1.15  tff(c_45, plain, $false, inference(negUnitSimplification, [status(thm)], [c_17, c_40])).
% 1.55/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.55/1.15  
% 1.55/1.15  Inference rules
% 1.55/1.15  ----------------------
% 1.55/1.15  #Ref     : 0
% 1.55/1.15  #Sup     : 7
% 1.55/1.15  #Fact    : 0
% 1.55/1.15  #Define  : 0
% 1.55/1.15  #Split   : 0
% 1.55/1.15  #Chain   : 0
% 1.55/1.15  #Close   : 0
% 1.55/1.15  
% 1.55/1.15  Ordering : KBO
% 1.55/1.15  
% 1.55/1.15  Simplification rules
% 1.55/1.15  ----------------------
% 1.55/1.15  #Subsume      : 0
% 1.55/1.15  #Demod        : 3
% 1.55/1.15  #Tautology    : 3
% 1.55/1.15  #SimpNegUnit  : 1
% 1.55/1.15  #BackRed      : 2
% 1.55/1.15  
% 1.55/1.15  #Partial instantiations: 0
% 1.55/1.15  #Strategies tried      : 1
% 1.55/1.15  
% 1.55/1.15  Timing (in seconds)
% 1.55/1.15  ----------------------
% 1.55/1.15  Preprocessing        : 0.25
% 1.55/1.15  Parsing              : 0.14
% 1.55/1.15  CNF conversion       : 0.02
% 1.55/1.15  Main loop            : 0.08
% 1.55/1.15  Inferencing          : 0.04
% 1.55/1.15  Reduction            : 0.02
% 1.55/1.15  Demodulation         : 0.01
% 1.55/1.15  BG Simplification    : 0.01
% 1.55/1.15  Subsumption          : 0.01
% 1.55/1.15  Abstraction          : 0.00
% 1.55/1.15  MUC search           : 0.00
% 1.55/1.15  Cooper               : 0.00
% 1.55/1.15  Total                : 0.35
% 1.55/1.15  Index Insertion      : 0.00
% 1.55/1.15  Index Deletion       : 0.00
% 1.55/1.15  Index Matching       : 0.00
% 1.55/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
