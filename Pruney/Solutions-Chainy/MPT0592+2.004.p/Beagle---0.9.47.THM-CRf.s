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
% DateTime   : Thu Dec  3 10:02:10 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :   16 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  58 expanded)
%              Number of equality atoms :   19 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_51,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( k1_relat_1(A) = k1_xboole_0
                & k1_relat_1(B) = k1_xboole_0 )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

tff(f_27,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_39,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k3_xboole_0(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_relat_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_86,plain,(
    ! [A_15] :
      ( k3_xboole_0(A_15,k2_zfmisc_1(k1_relat_1(A_15),k2_relat_1(A_15))) = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_95,plain,
    ( k3_xboole_0('#skF_1',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_1'))) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_86])).

tff(c_102,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_2,c_10,c_95])).

tff(c_20,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_98,plain,
    ( k3_xboole_0('#skF_2',k2_zfmisc_1(k1_xboole_0,k2_relat_1('#skF_2'))) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_86])).

tff(c_104,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_2,c_10,c_98])).

tff(c_115,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_104])).

tff(c_116,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_115])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.11  
% 1.72/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.11  %$ v1_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.72/1.11  
% 1.72/1.11  %Foreground sorts:
% 1.72/1.11  
% 1.72/1.11  
% 1.72/1.11  %Background operators:
% 1.72/1.11  
% 1.72/1.11  
% 1.72/1.11  %Foreground operators:
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.11  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.72/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.72/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.72/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.11  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.72/1.11  
% 1.72/1.12  tff(f_51, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k1_relat_1(A) = k1_xboole_0) & (k1_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t196_relat_1)).
% 1.72/1.12  tff(f_27, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.72/1.12  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.72/1.12  tff(f_39, axiom, (![A]: (v1_relat_1(A) => (k3_xboole_0(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_relat_1)).
% 1.72/1.12  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.12  tff(c_22, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.12  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.12  tff(c_10, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.12  tff(c_18, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.12  tff(c_86, plain, (![A_15]: (k3_xboole_0(A_15, k2_zfmisc_1(k1_relat_1(A_15), k2_relat_1(A_15)))=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.72/1.12  tff(c_95, plain, (k3_xboole_0('#skF_1', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_1')))='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_18, c_86])).
% 1.72/1.12  tff(c_102, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_2, c_10, c_95])).
% 1.72/1.12  tff(c_20, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.12  tff(c_16, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.72/1.12  tff(c_98, plain, (k3_xboole_0('#skF_2', k2_zfmisc_1(k1_xboole_0, k2_relat_1('#skF_2')))='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_86])).
% 1.72/1.12  tff(c_104, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_2, c_10, c_98])).
% 1.72/1.12  tff(c_115, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_104])).
% 1.72/1.12  tff(c_116, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_115])).
% 1.72/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.72/1.12  
% 1.72/1.12  Inference rules
% 1.72/1.12  ----------------------
% 1.72/1.12  #Ref     : 0
% 1.72/1.12  #Sup     : 24
% 1.72/1.12  #Fact    : 0
% 1.72/1.12  #Define  : 0
% 1.72/1.12  #Split   : 0
% 1.72/1.12  #Chain   : 0
% 1.72/1.12  #Close   : 0
% 1.72/1.12  
% 1.72/1.12  Ordering : KBO
% 1.72/1.12  
% 1.72/1.12  Simplification rules
% 1.72/1.12  ----------------------
% 1.72/1.12  #Subsume      : 0
% 1.72/1.12  #Demod        : 18
% 1.72/1.12  #Tautology    : 20
% 1.72/1.12  #SimpNegUnit  : 1
% 1.72/1.12  #BackRed      : 6
% 1.72/1.12  
% 1.72/1.12  #Partial instantiations: 0
% 1.72/1.12  #Strategies tried      : 1
% 1.72/1.12  
% 1.72/1.12  Timing (in seconds)
% 1.72/1.12  ----------------------
% 1.72/1.12  Preprocessing        : 0.27
% 1.72/1.12  Parsing              : 0.15
% 1.72/1.12  CNF conversion       : 0.02
% 1.72/1.12  Main loop            : 0.09
% 1.72/1.12  Inferencing          : 0.03
% 1.72/1.12  Reduction            : 0.03
% 1.72/1.12  Demodulation         : 0.03
% 1.72/1.12  BG Simplification    : 0.01
% 1.72/1.12  Subsumption          : 0.01
% 1.72/1.12  Abstraction          : 0.00
% 1.72/1.12  MUC search           : 0.00
% 1.72/1.12  Cooper               : 0.00
% 1.72/1.12  Total                : 0.39
% 1.72/1.12  Index Insertion      : 0.00
% 1.72/1.12  Index Deletion       : 0.00
% 1.72/1.12  Index Matching       : 0.00
% 1.72/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
