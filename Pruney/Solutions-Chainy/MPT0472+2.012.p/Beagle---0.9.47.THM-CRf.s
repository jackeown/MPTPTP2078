%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:27 EST 2020

% Result     : Theorem 1.53s
% Output     : CNFRefutation 1.53s
% Verified   : 
% Statistics : Number of formulae       :   30 (  42 expanded)
%              Number of leaves         :   14 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   31 (  62 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_14,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_14])).

tff(c_62,plain,(
    ! [A_10] :
      ( k3_xboole_0(A_10,k2_zfmisc_1(k1_relat_1(A_10),k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_71,plain,
    ( k3_xboole_0('#skF_1',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_1'))) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_62])).

tff(c_75,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_8,c_71])).

tff(c_77,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_75])).

tff(c_78,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_14])).

tff(c_95,plain,(
    ! [A_13] :
      ( k3_xboole_0(A_13,k2_zfmisc_1(k1_relat_1(A_13),k2_relat_1(A_13))) = A_13
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_104,plain,
    ( k3_xboole_0('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k1_xboole_0)) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_95])).

tff(c_108,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_6,c_104])).

tff(c_110,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:48:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.53/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.15  
% 1.53/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.16  %$ v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.53/1.16  
% 1.53/1.16  %Foreground sorts:
% 1.53/1.16  
% 1.53/1.16  
% 1.53/1.16  %Background operators:
% 1.53/1.16  
% 1.53/1.16  
% 1.53/1.16  %Foreground operators:
% 1.53/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.53/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.53/1.16  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.53/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.53/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.53/1.16  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.53/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.53/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.53/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.53/1.16  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.53/1.16  
% 1.53/1.17  tff(f_46, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.53/1.17  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.53/1.17  tff(f_33, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.53/1.17  tff(f_37, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_relat_1)).
% 1.53/1.17  tff(c_12, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.53/1.17  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.53/1.17  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.53/1.17  tff(c_6, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.53/1.17  tff(c_8, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.53/1.17  tff(c_14, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.53/1.17  tff(c_46, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_14])).
% 1.53/1.17  tff(c_62, plain, (![A_10]: (k3_xboole_0(A_10, k2_zfmisc_1(k1_relat_1(A_10), k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.53/1.17  tff(c_71, plain, (k3_xboole_0('#skF_1', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_1')))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_46, c_62])).
% 1.53/1.17  tff(c_75, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_8, c_71])).
% 1.53/1.17  tff(c_77, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_75])).
% 1.53/1.17  tff(c_78, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_14])).
% 1.53/1.17  tff(c_95, plain, (![A_13]: (k3_xboole_0(A_13, k2_zfmisc_1(k1_relat_1(A_13), k2_relat_1(A_13)))=A_13 | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.53/1.17  tff(c_104, plain, (k3_xboole_0('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k1_xboole_0))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_78, c_95])).
% 1.53/1.17  tff(c_108, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_6, c_104])).
% 1.53/1.17  tff(c_110, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_108])).
% 1.53/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.53/1.17  
% 1.53/1.17  Inference rules
% 1.53/1.17  ----------------------
% 1.53/1.17  #Ref     : 0
% 1.53/1.17  #Sup     : 22
% 1.53/1.17  #Fact    : 0
% 1.53/1.17  #Define  : 0
% 1.53/1.17  #Split   : 1
% 1.53/1.17  #Chain   : 0
% 1.53/1.17  #Close   : 0
% 1.53/1.17  
% 1.53/1.17  Ordering : KBO
% 1.53/1.17  
% 1.53/1.17  Simplification rules
% 1.53/1.17  ----------------------
% 1.53/1.17  #Subsume      : 0
% 1.53/1.17  #Demod        : 6
% 1.53/1.17  #Tautology    : 20
% 1.53/1.17  #SimpNegUnit  : 2
% 1.53/1.17  #BackRed      : 0
% 1.53/1.17  
% 1.53/1.17  #Partial instantiations: 0
% 1.53/1.17  #Strategies tried      : 1
% 1.53/1.17  
% 1.53/1.17  Timing (in seconds)
% 1.53/1.17  ----------------------
% 1.72/1.17  Preprocessing        : 0.27
% 1.72/1.17  Parsing              : 0.15
% 1.72/1.17  CNF conversion       : 0.01
% 1.72/1.17  Main loop            : 0.09
% 1.72/1.17  Inferencing          : 0.03
% 1.72/1.17  Reduction            : 0.03
% 1.72/1.17  Demodulation         : 0.02
% 1.72/1.17  BG Simplification    : 0.01
% 1.72/1.17  Subsumption          : 0.01
% 1.72/1.17  Abstraction          : 0.00
% 1.72/1.17  MUC search           : 0.00
% 1.72/1.17  Cooper               : 0.00
% 1.72/1.17  Total                : 0.39
% 1.72/1.17  Index Insertion      : 0.00
% 1.72/1.17  Index Deletion       : 0.00
% 1.72/1.17  Index Matching       : 0.00
% 1.72/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
