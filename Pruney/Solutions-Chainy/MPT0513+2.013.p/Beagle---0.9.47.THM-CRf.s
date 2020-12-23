%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:00 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   28 (  43 expanded)
%              Number of leaves         :   14 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  54 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ( v1_xboole_0(A)
        & v1_relat_1(A) )
     => ( v1_xboole_0(k7_relat_1(A,B))
        & v1_relat_1(k7_relat_1(A,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc17_relat_1)).

tff(f_46,negated_conjecture,(
    ~ ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t111_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13,plain,(
    ! [A_5] :
      ( v1_relat_1(A_5)
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17,plain,(
    v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4,c_13])).

tff(c_18,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_18])).

tff(c_23,plain,(
    ! [A_7,B_8] :
      ( v1_xboole_0(k7_relat_1(A_7,B_8))
      | ~ v1_relat_1(A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ! [A_7,B_8] :
      ( k7_relat_1(A_7,B_8) = k1_xboole_0
      | ~ v1_relat_1(A_7)
      | ~ v1_xboole_0(A_7) ) ),
    inference(resolution,[status(thm)],[c_23,c_2])).

tff(c_50,plain,(
    ! [A_12,B_13] :
      ( k7_relat_1(A_12,B_13) = '#skF_1'
      | ~ v1_relat_1(A_12)
      | ~ v1_xboole_0(A_12) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_30])).

tff(c_54,plain,(
    ! [B_13] :
      ( k7_relat_1('#skF_1',B_13) = '#skF_1'
      | ~ v1_relat_1('#skF_1') ) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_58,plain,(
    ! [B_13] : k7_relat_1('#skF_1',B_13) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_17,c_54])).

tff(c_12,plain,(
    k7_relat_1(k1_xboole_0,'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_33,plain,(
    k7_relat_1('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_12])).

tff(c_61,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  %$ v1_xboole_0 > v1_relat_1 > k7_relat_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_1
% 1.61/1.12  
% 1.61/1.12  %Foreground sorts:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Background operators:
% 1.61/1.12  
% 1.61/1.12  
% 1.61/1.12  %Foreground operators:
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.12  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.61/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.61/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.12  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.61/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.12  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.61/1.12  
% 1.61/1.12  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.61/1.12  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.61/1.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.61/1.12  tff(f_43, axiom, (![A, B]: ((v1_xboole_0(A) & v1_relat_1(A)) => (v1_xboole_0(k7_relat_1(A, B)) & v1_relat_1(k7_relat_1(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc17_relat_1)).
% 1.61/1.12  tff(f_46, negated_conjecture, ~(![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t111_relat_1)).
% 1.61/1.12  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.12  tff(c_13, plain, (![A_5]: (v1_relat_1(A_5) | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.61/1.12  tff(c_17, plain, (v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4, c_13])).
% 1.61/1.12  tff(c_18, plain, (![A_6]: (k1_xboole_0=A_6 | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.12  tff(c_22, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_18])).
% 1.61/1.12  tff(c_23, plain, (![A_7, B_8]: (v1_xboole_0(k7_relat_1(A_7, B_8)) | ~v1_relat_1(A_7) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.61/1.12  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.61/1.12  tff(c_30, plain, (![A_7, B_8]: (k7_relat_1(A_7, B_8)=k1_xboole_0 | ~v1_relat_1(A_7) | ~v1_xboole_0(A_7))), inference(resolution, [status(thm)], [c_23, c_2])).
% 1.61/1.12  tff(c_50, plain, (![A_12, B_13]: (k7_relat_1(A_12, B_13)='#skF_1' | ~v1_relat_1(A_12) | ~v1_xboole_0(A_12))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_30])).
% 1.61/1.12  tff(c_54, plain, (![B_13]: (k7_relat_1('#skF_1', B_13)='#skF_1' | ~v1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_4, c_50])).
% 1.61/1.12  tff(c_58, plain, (![B_13]: (k7_relat_1('#skF_1', B_13)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_17, c_54])).
% 1.61/1.12  tff(c_12, plain, (k7_relat_1(k1_xboole_0, '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.12  tff(c_33, plain, (k7_relat_1('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_12])).
% 1.61/1.12  tff(c_61, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_33])).
% 1.61/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.12  
% 1.61/1.12  Inference rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Ref     : 0
% 1.61/1.12  #Sup     : 10
% 1.61/1.12  #Fact    : 0
% 1.61/1.12  #Define  : 0
% 1.61/1.12  #Split   : 0
% 1.61/1.12  #Chain   : 0
% 1.61/1.12  #Close   : 0
% 1.61/1.12  
% 1.61/1.12  Ordering : KBO
% 1.61/1.12  
% 1.61/1.12  Simplification rules
% 1.61/1.12  ----------------------
% 1.61/1.12  #Subsume      : 0
% 1.61/1.12  #Demod        : 6
% 1.61/1.12  #Tautology    : 3
% 1.61/1.12  #SimpNegUnit  : 0
% 1.61/1.12  #BackRed      : 3
% 1.61/1.12  
% 1.61/1.12  #Partial instantiations: 0
% 1.61/1.12  #Strategies tried      : 1
% 1.61/1.12  
% 1.61/1.12  Timing (in seconds)
% 1.61/1.12  ----------------------
% 1.61/1.13  Preprocessing        : 0.24
% 1.61/1.13  Parsing              : 0.13
% 1.61/1.13  CNF conversion       : 0.01
% 1.61/1.13  Main loop            : 0.09
% 1.61/1.13  Inferencing          : 0.04
% 1.61/1.13  Reduction            : 0.02
% 1.61/1.13  Demodulation         : 0.02
% 1.61/1.13  BG Simplification    : 0.01
% 1.61/1.13  Subsumption          : 0.02
% 1.61/1.13  Abstraction          : 0.00
% 1.61/1.13  MUC search           : 0.00
% 1.61/1.13  Cooper               : 0.00
% 1.61/1.13  Total                : 0.36
% 1.61/1.13  Index Insertion      : 0.00
% 1.61/1.13  Index Deletion       : 0.00
% 1.61/1.13  Index Matching       : 0.00
% 1.61/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
