%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:48 EST 2020

% Result     : Theorem 2.21s
% Output     : CNFRefutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  90 expanded)
%              Number of equality atoms :   18 (  27 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_58,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_26,plain,(
    k10_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_138,plain,(
    ! [A_55,B_56] :
      ( r2_hidden('#skF_1'(A_55,B_56),B_56)
      | r2_hidden('#skF_2'(A_55,B_56),A_55)
      | B_56 = A_55 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_18,plain,(
    ! [A_12] : r1_xboole_0(A_12,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,(
    ! [A_21,C_22,B_23] :
      ( ~ r2_hidden(A_21,C_22)
      | ~ r1_xboole_0(k2_tarski(A_21,B_23),C_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_44,plain,(
    ! [A_21] : ~ r2_hidden(A_21,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_39])).

tff(c_157,plain,(
    ! [B_56] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_56),B_56)
      | k1_xboole_0 = B_56 ) ),
    inference(resolution,[status(thm)],[c_138,c_44])).

tff(c_32,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_28,plain,(
    r1_tarski('#skF_4',k2_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_97,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(k2_relat_1(B_42),A_43)
      | k10_relat_1(B_42,A_43) != k1_xboole_0
      | ~ v1_relat_1(B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_xboole_0(A_9,C_11)
      | ~ r1_xboole_0(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_332,plain,(
    ! [A_94,A_95,B_96] :
      ( r1_xboole_0(A_94,A_95)
      | ~ r1_tarski(A_94,k2_relat_1(B_96))
      | k10_relat_1(B_96,A_95) != k1_xboole_0
      | ~ v1_relat_1(B_96) ) ),
    inference(resolution,[status(thm)],[c_97,c_16])).

tff(c_334,plain,(
    ! [A_95] :
      ( r1_xboole_0('#skF_4',A_95)
      | k10_relat_1('#skF_5',A_95) != k1_xboole_0
      | ~ v1_relat_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_28,c_332])).

tff(c_338,plain,(
    ! [A_97] :
      ( r1_xboole_0('#skF_4',A_97)
      | k10_relat_1('#skF_5',A_97) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_334])).

tff(c_10,plain,(
    ! [A_4,B_5,C_8] :
      ( ~ r1_xboole_0(A_4,B_5)
      | ~ r2_hidden(C_8,B_5)
      | ~ r2_hidden(C_8,A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_362,plain,(
    ! [C_100,A_101] :
      ( ~ r2_hidden(C_100,A_101)
      | ~ r2_hidden(C_100,'#skF_4')
      | k10_relat_1('#skF_5',A_101) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_338,c_10])).

tff(c_387,plain,(
    ! [B_102] :
      ( ~ r2_hidden('#skF_1'(k1_xboole_0,B_102),'#skF_4')
      | k10_relat_1('#skF_5',B_102) != k1_xboole_0
      | k1_xboole_0 = B_102 ) ),
    inference(resolution,[status(thm)],[c_157,c_362])).

tff(c_395,plain,
    ( k10_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_157,c_387])).

tff(c_404,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_395])).

tff(c_406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:40:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.21/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  
% 2.21/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.28  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_5 > #skF_4 > #skF_2 > #skF_1
% 2.21/1.28  
% 2.21/1.28  %Foreground sorts:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Background operators:
% 2.21/1.28  
% 2.21/1.28  
% 2.21/1.28  %Foreground operators:
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.21/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.21/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.21/1.28  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.21/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.21/1.28  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.21/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.21/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.21/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.21/1.28  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.21/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.21/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.21/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.21/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.21/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.21/1.28  
% 2.21/1.29  tff(f_80, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t174_relat_1)).
% 2.21/1.29  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 2.21/1.29  tff(f_58, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.21/1.29  tff(f_63, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.21/1.29  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 2.21/1.29  tff(f_56, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.21/1.29  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.21/1.29  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.29  tff(c_26, plain, (k10_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.29  tff(c_138, plain, (![A_55, B_56]: (r2_hidden('#skF_1'(A_55, B_56), B_56) | r2_hidden('#skF_2'(A_55, B_56), A_55) | B_56=A_55)), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.21/1.29  tff(c_18, plain, (![A_12]: (r1_xboole_0(A_12, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.21/1.29  tff(c_39, plain, (![A_21, C_22, B_23]: (~r2_hidden(A_21, C_22) | ~r1_xboole_0(k2_tarski(A_21, B_23), C_22))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.21/1.29  tff(c_44, plain, (![A_21]: (~r2_hidden(A_21, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_39])).
% 2.21/1.29  tff(c_157, plain, (![B_56]: (r2_hidden('#skF_1'(k1_xboole_0, B_56), B_56) | k1_xboole_0=B_56)), inference(resolution, [status(thm)], [c_138, c_44])).
% 2.21/1.29  tff(c_32, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.29  tff(c_28, plain, (r1_tarski('#skF_4', k2_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.21/1.29  tff(c_97, plain, (![B_42, A_43]: (r1_xboole_0(k2_relat_1(B_42), A_43) | k10_relat_1(B_42, A_43)!=k1_xboole_0 | ~v1_relat_1(B_42))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.21/1.29  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_xboole_0(A_9, C_11) | ~r1_xboole_0(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.21/1.29  tff(c_332, plain, (![A_94, A_95, B_96]: (r1_xboole_0(A_94, A_95) | ~r1_tarski(A_94, k2_relat_1(B_96)) | k10_relat_1(B_96, A_95)!=k1_xboole_0 | ~v1_relat_1(B_96))), inference(resolution, [status(thm)], [c_97, c_16])).
% 2.21/1.29  tff(c_334, plain, (![A_95]: (r1_xboole_0('#skF_4', A_95) | k10_relat_1('#skF_5', A_95)!=k1_xboole_0 | ~v1_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_28, c_332])).
% 2.21/1.29  tff(c_338, plain, (![A_97]: (r1_xboole_0('#skF_4', A_97) | k10_relat_1('#skF_5', A_97)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_334])).
% 2.21/1.29  tff(c_10, plain, (![A_4, B_5, C_8]: (~r1_xboole_0(A_4, B_5) | ~r2_hidden(C_8, B_5) | ~r2_hidden(C_8, A_4))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.21/1.29  tff(c_362, plain, (![C_100, A_101]: (~r2_hidden(C_100, A_101) | ~r2_hidden(C_100, '#skF_4') | k10_relat_1('#skF_5', A_101)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_338, c_10])).
% 2.21/1.29  tff(c_387, plain, (![B_102]: (~r2_hidden('#skF_1'(k1_xboole_0, B_102), '#skF_4') | k10_relat_1('#skF_5', B_102)!=k1_xboole_0 | k1_xboole_0=B_102)), inference(resolution, [status(thm)], [c_157, c_362])).
% 2.21/1.29  tff(c_395, plain, (k10_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_157, c_387])).
% 2.21/1.29  tff(c_404, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_395])).
% 2.21/1.29  tff(c_406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_404])).
% 2.21/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.21/1.29  
% 2.21/1.29  Inference rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Ref     : 0
% 2.21/1.29  #Sup     : 86
% 2.21/1.29  #Fact    : 0
% 2.21/1.29  #Define  : 0
% 2.21/1.29  #Split   : 1
% 2.21/1.29  #Chain   : 0
% 2.21/1.29  #Close   : 0
% 2.21/1.29  
% 2.21/1.29  Ordering : KBO
% 2.21/1.29  
% 2.21/1.29  Simplification rules
% 2.21/1.29  ----------------------
% 2.21/1.29  #Subsume      : 22
% 2.21/1.29  #Demod        : 5
% 2.21/1.29  #Tautology    : 10
% 2.21/1.29  #SimpNegUnit  : 3
% 2.21/1.29  #BackRed      : 0
% 2.21/1.29  
% 2.21/1.29  #Partial instantiations: 0
% 2.21/1.29  #Strategies tried      : 1
% 2.21/1.29  
% 2.21/1.29  Timing (in seconds)
% 2.21/1.29  ----------------------
% 2.21/1.29  Preprocessing        : 0.28
% 2.21/1.29  Parsing              : 0.15
% 2.21/1.29  CNF conversion       : 0.02
% 2.21/1.30  Main loop            : 0.25
% 2.21/1.30  Inferencing          : 0.10
% 2.21/1.30  Reduction            : 0.06
% 2.21/1.30  Demodulation         : 0.04
% 2.21/1.30  BG Simplification    : 0.02
% 2.21/1.30  Subsumption          : 0.06
% 2.21/1.30  Abstraction          : 0.01
% 2.21/1.30  MUC search           : 0.00
% 2.21/1.30  Cooper               : 0.00
% 2.21/1.30  Total                : 0.56
% 2.21/1.30  Index Insertion      : 0.00
% 2.21/1.30  Index Deletion       : 0.00
% 2.21/1.30  Index Matching       : 0.00
% 2.21/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
