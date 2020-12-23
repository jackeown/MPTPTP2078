%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:06 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   48 (  74 expanded)
%              Number of leaves         :   25 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   47 (  93 expanded)
%              Number of equality atoms :   16 (  41 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_47,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(B,k3_subset_1(A,B))
        <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_subset_1)).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_18,plain,(
    ! [A_14] : k1_subset_1(A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_24,plain,
    ( k1_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,
    ( k1_xboole_0 != '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_24])).

tff(c_46,plain,(
    ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_31])).

tff(c_30,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_32,plain,
    ( r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4'))
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_30])).

tff(c_48,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_32])).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_12])).

tff(c_74,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_2'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    ! [A_36,B_37] :
      ( ~ v1_xboole_0(A_36)
      | r1_tarski(A_36,B_37) ) ),
    inference(resolution,[status(thm)],[c_74,c_2])).

tff(c_99,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_92,c_46])).

tff(c_104,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_51,c_99])).

tff(c_105,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_31])).

tff(c_107,plain,(
    r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_32])).

tff(c_22,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_150,plain,(
    ! [A_53,B_54] :
      ( k4_xboole_0(A_53,B_54) = k3_subset_1(A_53,B_54)
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_154,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_22,c_150])).

tff(c_16,plain,(
    ! [A_12,B_13] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k4_xboole_0(B_13,A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_158,plain,
    ( k1_xboole_0 = '#skF_4'
    | ~ r1_tarski('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_162,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_158])).

tff(c_164,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:13:12 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 1.98/1.23  
% 1.98/1.23  %Foreground sorts:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Background operators:
% 1.98/1.23  
% 1.98/1.23  
% 1.98/1.23  %Foreground operators:
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.98/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.98/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.98/1.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.98/1.23  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 1.98/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.98/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.23  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.98/1.23  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.98/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.98/1.23  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 1.98/1.23  
% 1.98/1.23  tff(f_47, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 1.98/1.23  tff(f_58, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_subset_1)).
% 1.98/1.23  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.98/1.23  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.98/1.23  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.98/1.23  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 1.98/1.23  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 1.98/1.23  tff(c_18, plain, (![A_14]: (k1_subset_1(A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.98/1.23  tff(c_24, plain, (k1_subset_1('#skF_3')!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.23  tff(c_31, plain, (k1_xboole_0!='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_24])).
% 1.98/1.23  tff(c_46, plain, (~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_31])).
% 1.98/1.23  tff(c_30, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.23  tff(c_32, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4')) | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_18, c_30])).
% 1.98/1.23  tff(c_48, plain, (k1_xboole_0='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_46, c_32])).
% 1.98/1.23  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.98/1.23  tff(c_51, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_12])).
% 1.98/1.23  tff(c_74, plain, (![A_30, B_31]: (r2_hidden('#skF_2'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.98/1.23  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.23  tff(c_92, plain, (![A_36, B_37]: (~v1_xboole_0(A_36) | r1_tarski(A_36, B_37))), inference(resolution, [status(thm)], [c_74, c_2])).
% 1.98/1.23  tff(c_99, plain, (~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_92, c_46])).
% 1.98/1.23  tff(c_104, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_51, c_99])).
% 1.98/1.23  tff(c_105, plain, (k1_xboole_0!='#skF_4'), inference(splitRight, [status(thm)], [c_31])).
% 1.98/1.23  tff(c_107, plain, (r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_105, c_32])).
% 1.98/1.23  tff(c_22, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.23  tff(c_150, plain, (![A_53, B_54]: (k4_xboole_0(A_53, B_54)=k3_subset_1(A_53, B_54) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.98/1.23  tff(c_154, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_22, c_150])).
% 1.98/1.23  tff(c_16, plain, (![A_12, B_13]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k4_xboole_0(B_13, A_12)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.98/1.23  tff(c_158, plain, (k1_xboole_0='#skF_4' | ~r1_tarski('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_154, c_16])).
% 1.98/1.23  tff(c_162, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_107, c_158])).
% 1.98/1.23  tff(c_164, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_162])).
% 1.98/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.98/1.23  
% 1.98/1.23  Inference rules
% 1.98/1.23  ----------------------
% 1.98/1.23  #Ref     : 0
% 1.98/1.23  #Sup     : 27
% 1.98/1.23  #Fact    : 0
% 1.98/1.23  #Define  : 0
% 1.98/1.24  #Split   : 1
% 1.98/1.24  #Chain   : 0
% 1.98/1.24  #Close   : 0
% 1.98/1.24  
% 1.98/1.24  Ordering : KBO
% 1.98/1.24  
% 1.98/1.24  Simplification rules
% 1.98/1.24  ----------------------
% 1.98/1.24  #Subsume      : 0
% 1.98/1.24  #Demod        : 8
% 1.98/1.24  #Tautology    : 16
% 1.98/1.24  #SimpNegUnit  : 3
% 1.98/1.24  #BackRed      : 3
% 1.98/1.24  
% 1.98/1.24  #Partial instantiations: 0
% 1.98/1.24  #Strategies tried      : 1
% 1.98/1.24  
% 1.98/1.24  Timing (in seconds)
% 1.98/1.24  ----------------------
% 1.98/1.24  Preprocessing        : 0.30
% 1.98/1.24  Parsing              : 0.16
% 1.98/1.24  CNF conversion       : 0.02
% 1.98/1.24  Main loop            : 0.14
% 1.98/1.24  Inferencing          : 0.05
% 1.98/1.24  Reduction            : 0.04
% 1.98/1.24  Demodulation         : 0.03
% 1.98/1.24  BG Simplification    : 0.01
% 1.98/1.24  Subsumption          : 0.02
% 1.98/1.24  Abstraction          : 0.01
% 1.98/1.24  MUC search           : 0.00
% 1.98/1.24  Cooper               : 0.00
% 1.98/1.24  Total                : 0.47
% 1.98/1.24  Index Insertion      : 0.00
% 1.98/1.24  Index Deletion       : 0.00
% 1.98/1.24  Index Matching       : 0.00
% 1.98/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
