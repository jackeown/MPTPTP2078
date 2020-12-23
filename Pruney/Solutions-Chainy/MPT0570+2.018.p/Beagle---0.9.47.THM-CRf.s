%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:43 EST 2020

% Result     : Theorem 2.50s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   48 (  66 expanded)
%              Number of leaves         :   23 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   69 ( 124 expanded)
%              Number of equality atoms :   17 (  34 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

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

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_28,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [B_11] : r1_tarski(B_11,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_34,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_30,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_281,plain,(
    ! [B_83,A_84] :
      ( r1_xboole_0(k2_relat_1(B_83),A_84)
      | k10_relat_1(B_83,A_84) != k1_xboole_0
      | ~ v1_relat_1(B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_20,plain,(
    ! [A_13,C_15,B_14] :
      ( r1_xboole_0(A_13,C_15)
      | ~ r1_xboole_0(B_14,C_15)
      | ~ r1_tarski(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_422,plain,(
    ! [A_108,A_109,B_110] :
      ( r1_xboole_0(A_108,A_109)
      | ~ r1_tarski(A_108,k2_relat_1(B_110))
      | k10_relat_1(B_110,A_109) != k1_xboole_0
      | ~ v1_relat_1(B_110) ) ),
    inference(resolution,[status(thm)],[c_281,c_20])).

tff(c_427,plain,(
    ! [A_109] :
      ( r1_xboole_0('#skF_3',A_109)
      | k10_relat_1('#skF_4',A_109) != k1_xboole_0
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_30,c_422])).

tff(c_440,plain,(
    ! [A_111] :
      ( r1_xboole_0('#skF_3',A_111)
      | k10_relat_1('#skF_4',A_111) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_427])).

tff(c_22,plain,(
    ! [B_17,A_16] :
      ( ~ r1_xboole_0(B_17,A_16)
      | ~ r1_tarski(B_17,A_16)
      | v1_xboole_0(B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_447,plain,(
    ! [A_111] :
      ( ~ r1_tarski('#skF_3',A_111)
      | v1_xboole_0('#skF_3')
      | k10_relat_1('#skF_4',A_111) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_440,c_22])).

tff(c_477,plain,(
    ! [A_115] :
      ( ~ r1_tarski('#skF_3',A_115)
      | k10_relat_1('#skF_4',A_115) != k1_xboole_0 ) ),
    inference(splitLeft,[status(thm)],[c_447])).

tff(c_488,plain,(
    k10_relat_1('#skF_4','#skF_3') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_477])).

tff(c_494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_488])).

tff(c_495,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_447])).

tff(c_76,plain,(
    ! [A_30,B_31] :
      ( r2_hidden('#skF_2'(A_30,B_31),A_30)
      | r1_tarski(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_81,plain,(
    ! [A_32,B_33] :
      ( ~ v1_xboole_0(A_32)
      | r1_tarski(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_48,plain,(
    ! [B_25,A_26] :
      ( B_25 = A_26
      | ~ r1_tarski(B_25,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [A_12] :
      ( k1_xboole_0 = A_12
      | ~ r1_tarski(A_12,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_18,c_48])).

tff(c_91,plain,(
    ! [A_32] :
      ( k1_xboole_0 = A_32
      | ~ v1_xboole_0(A_32) ) ),
    inference(resolution,[status(thm)],[c_81,c_60])).

tff(c_500,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_495,c_91])).

tff(c_505,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_500])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n022.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 11:01:41 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.50/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.35  
% 2.50/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.35  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > v1_relat_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_4 > #skF_2
% 2.50/1.35  
% 2.50/1.35  %Foreground sorts:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Background operators:
% 2.50/1.35  
% 2.50/1.35  
% 2.50/1.35  %Foreground operators:
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.50/1.35  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.50/1.35  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.50/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.50/1.35  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.50/1.35  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.50/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.50/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.50/1.35  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.50/1.35  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.50/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.50/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.50/1.35  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.50/1.35  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.50/1.35  
% 2.50/1.36  tff(f_77, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.50/1.36  tff(f_44, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.50/1.36  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.50/1.36  tff(f_52, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.50/1.36  tff(f_60, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 2.50/1.36  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.50/1.36  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.50/1.36  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.50/1.36  tff(c_32, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.50/1.36  tff(c_28, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.50/1.36  tff(c_16, plain, (![B_11]: (r1_tarski(B_11, B_11))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.50/1.36  tff(c_34, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.50/1.36  tff(c_30, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.50/1.36  tff(c_281, plain, (![B_83, A_84]: (r1_xboole_0(k2_relat_1(B_83), A_84) | k10_relat_1(B_83, A_84)!=k1_xboole_0 | ~v1_relat_1(B_83))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.36  tff(c_20, plain, (![A_13, C_15, B_14]: (r1_xboole_0(A_13, C_15) | ~r1_xboole_0(B_14, C_15) | ~r1_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.50/1.36  tff(c_422, plain, (![A_108, A_109, B_110]: (r1_xboole_0(A_108, A_109) | ~r1_tarski(A_108, k2_relat_1(B_110)) | k10_relat_1(B_110, A_109)!=k1_xboole_0 | ~v1_relat_1(B_110))), inference(resolution, [status(thm)], [c_281, c_20])).
% 2.50/1.36  tff(c_427, plain, (![A_109]: (r1_xboole_0('#skF_3', A_109) | k10_relat_1('#skF_4', A_109)!=k1_xboole_0 | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_30, c_422])).
% 2.50/1.36  tff(c_440, plain, (![A_111]: (r1_xboole_0('#skF_3', A_111) | k10_relat_1('#skF_4', A_111)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_427])).
% 2.50/1.36  tff(c_22, plain, (![B_17, A_16]: (~r1_xboole_0(B_17, A_16) | ~r1_tarski(B_17, A_16) | v1_xboole_0(B_17))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.50/1.36  tff(c_447, plain, (![A_111]: (~r1_tarski('#skF_3', A_111) | v1_xboole_0('#skF_3') | k10_relat_1('#skF_4', A_111)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_440, c_22])).
% 2.50/1.36  tff(c_477, plain, (![A_115]: (~r1_tarski('#skF_3', A_115) | k10_relat_1('#skF_4', A_115)!=k1_xboole_0)), inference(splitLeft, [status(thm)], [c_447])).
% 2.50/1.36  tff(c_488, plain, (k10_relat_1('#skF_4', '#skF_3')!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_477])).
% 2.50/1.36  tff(c_494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_488])).
% 2.50/1.36  tff(c_495, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_447])).
% 2.50/1.36  tff(c_76, plain, (![A_30, B_31]: (r2_hidden('#skF_2'(A_30, B_31), A_30) | r1_tarski(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.50/1.36  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.50/1.36  tff(c_81, plain, (![A_32, B_33]: (~v1_xboole_0(A_32) | r1_tarski(A_32, B_33))), inference(resolution, [status(thm)], [c_76, c_2])).
% 2.50/1.36  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.50/1.36  tff(c_48, plain, (![B_25, A_26]: (B_25=A_26 | ~r1_tarski(B_25, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.50/1.36  tff(c_60, plain, (![A_12]: (k1_xboole_0=A_12 | ~r1_tarski(A_12, k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_48])).
% 2.50/1.36  tff(c_91, plain, (![A_32]: (k1_xboole_0=A_32 | ~v1_xboole_0(A_32))), inference(resolution, [status(thm)], [c_81, c_60])).
% 2.50/1.36  tff(c_500, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_495, c_91])).
% 2.50/1.36  tff(c_505, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_500])).
% 2.50/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.36  
% 2.50/1.36  Inference rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Ref     : 0
% 2.50/1.36  #Sup     : 98
% 2.50/1.36  #Fact    : 0
% 2.50/1.36  #Define  : 0
% 2.50/1.36  #Split   : 6
% 2.50/1.36  #Chain   : 0
% 2.50/1.36  #Close   : 0
% 2.50/1.36  
% 2.50/1.36  Ordering : KBO
% 2.50/1.36  
% 2.50/1.36  Simplification rules
% 2.50/1.36  ----------------------
% 2.50/1.36  #Subsume      : 39
% 2.50/1.36  #Demod        : 13
% 2.50/1.36  #Tautology    : 23
% 2.50/1.36  #SimpNegUnit  : 15
% 2.50/1.36  #BackRed      : 10
% 2.50/1.36  
% 2.50/1.36  #Partial instantiations: 0
% 2.50/1.36  #Strategies tried      : 1
% 2.50/1.36  
% 2.50/1.36  Timing (in seconds)
% 2.50/1.36  ----------------------
% 2.50/1.37  Preprocessing        : 0.29
% 2.50/1.37  Parsing              : 0.16
% 2.50/1.37  CNF conversion       : 0.02
% 2.50/1.37  Main loop            : 0.29
% 2.50/1.37  Inferencing          : 0.11
% 2.50/1.37  Reduction            : 0.07
% 2.50/1.37  Demodulation         : 0.05
% 2.50/1.37  BG Simplification    : 0.02
% 2.50/1.37  Subsumption          : 0.07
% 2.50/1.37  Abstraction          : 0.01
% 2.50/1.37  MUC search           : 0.00
% 2.50/1.37  Cooper               : 0.00
% 2.50/1.37  Total                : 0.61
% 2.50/1.37  Index Insertion      : 0.00
% 2.50/1.37  Index Deletion       : 0.00
% 2.50/1.37  Index Matching       : 0.00
% 2.50/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
