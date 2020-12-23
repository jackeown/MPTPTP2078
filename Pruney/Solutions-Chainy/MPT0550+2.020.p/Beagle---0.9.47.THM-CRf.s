%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:54 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.33s
% Verified   : 
% Statistics : Number of formulae       :   41 (  49 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 100 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_60,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_54,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    ! [C_23,B_24,A_25] :
      ( r2_hidden(C_23,B_24)
      | ~ r2_hidden(C_23,A_25)
      | ~ r1_tarski(A_25,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_6,B_7,B_24] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_24)
      | ~ r1_tarski(A_6,B_24)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_60,plain,(
    ! [B_32,A_33] :
      ( r1_xboole_0(k1_relat_1(B_32),A_33)
      | k9_relat_1(B_32,A_33) != k1_xboole_0
      | ~ v1_relat_1(B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_85,plain,(
    ! [C_43,A_44,B_45] :
      ( ~ r2_hidden(C_43,A_44)
      | ~ r2_hidden(C_43,k1_relat_1(B_45))
      | k9_relat_1(B_45,A_44) != k1_xboole_0
      | ~ v1_relat_1(B_45) ) ),
    inference(resolution,[status(thm)],[c_60,c_8])).

tff(c_161,plain,(
    ! [A_65,B_66,B_67] :
      ( ~ r2_hidden('#skF_2'(A_65,B_66),k1_relat_1(B_67))
      | k9_relat_1(B_67,B_66) != k1_xboole_0
      | ~ v1_relat_1(B_67)
      | r1_xboole_0(A_65,B_66) ) ),
    inference(resolution,[status(thm)],[c_10,c_85])).

tff(c_225,plain,(
    ! [B_77,B_78,A_79] :
      ( k9_relat_1(B_77,B_78) != k1_xboole_0
      | ~ v1_relat_1(B_77)
      | ~ r1_tarski(A_79,k1_relat_1(B_77))
      | r1_xboole_0(A_79,B_78) ) ),
    inference(resolution,[status(thm)],[c_50,c_161])).

tff(c_227,plain,(
    ! [A_79] :
      ( ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_79,k1_relat_1('#skF_4'))
      | r1_xboole_0(A_79,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_225])).

tff(c_231,plain,(
    ! [A_80] :
      ( ~ r1_tarski(A_80,k1_relat_1('#skF_4'))
      | r1_xboole_0(A_80,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_227])).

tff(c_244,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_231])).

tff(c_248,plain,(
    ! [C_81] : ~ r2_hidden(C_81,'#skF_3') ),
    inference(resolution,[status(thm)],[c_244,c_8])).

tff(c_285,plain,(
    ! [B_82] : r1_tarski('#skF_3',B_82) ),
    inference(resolution,[status(thm)],[c_6,c_248])).

tff(c_14,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_299,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_285,c_14])).

tff(c_308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_299])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:48:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.40  
% 2.33/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.33/1.40  
% 2.33/1.40  %Foreground sorts:
% 2.33/1.40  
% 2.33/1.40  
% 2.33/1.40  %Background operators:
% 2.33/1.40  
% 2.33/1.40  
% 2.33/1.40  %Foreground operators:
% 2.33/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.33/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.33/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.33/1.40  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.33/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.40  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.33/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.33/1.40  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.33/1.40  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.33/1.40  
% 2.33/1.41  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 2.33/1.41  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.33/1.41  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.33/1.41  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 2.33/1.41  tff(f_54, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 2.33/1.41  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.33/1.41  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.41  tff(c_22, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.33/1.41  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.33/1.41  tff(c_20, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.33/1.41  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.41  tff(c_41, plain, (![C_23, B_24, A_25]: (r2_hidden(C_23, B_24) | ~r2_hidden(C_23, A_25) | ~r1_tarski(A_25, B_24))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.33/1.41  tff(c_50, plain, (![A_6, B_7, B_24]: (r2_hidden('#skF_2'(A_6, B_7), B_24) | ~r1_tarski(A_6, B_24) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_12, c_41])).
% 2.33/1.41  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.41  tff(c_60, plain, (![B_32, A_33]: (r1_xboole_0(k1_relat_1(B_32), A_33) | k9_relat_1(B_32, A_33)!=k1_xboole_0 | ~v1_relat_1(B_32))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.33/1.41  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.33/1.41  tff(c_85, plain, (![C_43, A_44, B_45]: (~r2_hidden(C_43, A_44) | ~r2_hidden(C_43, k1_relat_1(B_45)) | k9_relat_1(B_45, A_44)!=k1_xboole_0 | ~v1_relat_1(B_45))), inference(resolution, [status(thm)], [c_60, c_8])).
% 2.33/1.41  tff(c_161, plain, (![A_65, B_66, B_67]: (~r2_hidden('#skF_2'(A_65, B_66), k1_relat_1(B_67)) | k9_relat_1(B_67, B_66)!=k1_xboole_0 | ~v1_relat_1(B_67) | r1_xboole_0(A_65, B_66))), inference(resolution, [status(thm)], [c_10, c_85])).
% 2.33/1.41  tff(c_225, plain, (![B_77, B_78, A_79]: (k9_relat_1(B_77, B_78)!=k1_xboole_0 | ~v1_relat_1(B_77) | ~r1_tarski(A_79, k1_relat_1(B_77)) | r1_xboole_0(A_79, B_78))), inference(resolution, [status(thm)], [c_50, c_161])).
% 2.33/1.41  tff(c_227, plain, (![A_79]: (~v1_relat_1('#skF_4') | ~r1_tarski(A_79, k1_relat_1('#skF_4')) | r1_xboole_0(A_79, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_225])).
% 2.33/1.41  tff(c_231, plain, (![A_80]: (~r1_tarski(A_80, k1_relat_1('#skF_4')) | r1_xboole_0(A_80, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_227])).
% 2.33/1.41  tff(c_244, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_231])).
% 2.33/1.41  tff(c_248, plain, (![C_81]: (~r2_hidden(C_81, '#skF_3'))), inference(resolution, [status(thm)], [c_244, c_8])).
% 2.33/1.41  tff(c_285, plain, (![B_82]: (r1_tarski('#skF_3', B_82))), inference(resolution, [status(thm)], [c_6, c_248])).
% 2.33/1.41  tff(c_14, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.33/1.41  tff(c_299, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_285, c_14])).
% 2.33/1.41  tff(c_308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_299])).
% 2.33/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.41  
% 2.33/1.41  Inference rules
% 2.33/1.41  ----------------------
% 2.33/1.41  #Ref     : 0
% 2.33/1.41  #Sup     : 65
% 2.33/1.41  #Fact    : 0
% 2.33/1.41  #Define  : 0
% 2.33/1.41  #Split   : 0
% 2.33/1.41  #Chain   : 0
% 2.33/1.41  #Close   : 0
% 2.33/1.41  
% 2.33/1.41  Ordering : KBO
% 2.33/1.41  
% 2.33/1.41  Simplification rules
% 2.33/1.41  ----------------------
% 2.33/1.41  #Subsume      : 4
% 2.33/1.41  #Demod        : 5
% 2.33/1.41  #Tautology    : 7
% 2.33/1.41  #SimpNegUnit  : 1
% 2.33/1.41  #BackRed      : 0
% 2.33/1.41  
% 2.33/1.41  #Partial instantiations: 0
% 2.33/1.41  #Strategies tried      : 1
% 2.33/1.41  
% 2.33/1.41  Timing (in seconds)
% 2.33/1.41  ----------------------
% 2.33/1.41  Preprocessing        : 0.33
% 2.33/1.41  Parsing              : 0.18
% 2.33/1.41  CNF conversion       : 0.02
% 2.33/1.41  Main loop            : 0.24
% 2.33/1.41  Inferencing          : 0.10
% 2.33/1.41  Reduction            : 0.06
% 2.33/1.41  Demodulation         : 0.04
% 2.33/1.41  BG Simplification    : 0.02
% 2.33/1.41  Subsumption          : 0.06
% 2.33/1.41  Abstraction          : 0.01
% 2.33/1.41  MUC search           : 0.00
% 2.33/1.41  Cooper               : 0.00
% 2.33/1.41  Total                : 0.60
% 2.33/1.41  Index Insertion      : 0.00
% 2.33/1.41  Index Deletion       : 0.00
% 2.33/1.41  Index Matching       : 0.00
% 2.33/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
