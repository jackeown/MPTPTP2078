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
% DateTime   : Thu Dec  3 10:01:46 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :   11
%              Number of atoms          :   64 ( 100 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k2_relat_1(B))
            & k10_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t174_relat_1)).

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
     => ( k10_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_22,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_20,plain,(
    k10_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),A_6)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_41,plain,(
    ! [C_25,B_26,A_27] :
      ( r2_hidden(C_25,B_26)
      | ~ r2_hidden(C_25,A_27)
      | ~ r1_tarski(A_27,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    ! [A_6,B_7,B_26] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_26)
      | ~ r1_tarski(A_6,B_26)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_41])).

tff(c_10,plain,(
    ! [A_6,B_7] :
      ( r2_hidden('#skF_2'(A_6,B_7),B_7)
      | r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    ! [B_34,A_35] :
      ( r1_xboole_0(k2_relat_1(B_34),A_35)
      | k10_relat_1(B_34,A_35) != k1_xboole_0
      | ~ v1_relat_1(B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    ! [C_45,A_46,B_47] :
      ( ~ r2_hidden(C_45,A_46)
      | ~ r2_hidden(C_45,k2_relat_1(B_47))
      | k10_relat_1(B_47,A_46) != k1_xboole_0
      | ~ v1_relat_1(B_47) ) ),
    inference(resolution,[status(thm)],[c_54,c_8])).

tff(c_155,plain,(
    ! [A_67,B_68,B_69] :
      ( ~ r2_hidden('#skF_2'(A_67,B_68),k2_relat_1(B_69))
      | k10_relat_1(B_69,B_68) != k1_xboole_0
      | ~ v1_relat_1(B_69)
      | r1_xboole_0(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_10,c_79])).

tff(c_219,plain,(
    ! [B_79,B_80,A_81] :
      ( k10_relat_1(B_79,B_80) != k1_xboole_0
      | ~ v1_relat_1(B_79)
      | ~ r1_tarski(A_81,k2_relat_1(B_79))
      | r1_xboole_0(A_81,B_80) ) ),
    inference(resolution,[status(thm)],[c_50,c_155])).

tff(c_221,plain,(
    ! [A_81] :
      ( ~ v1_relat_1('#skF_4')
      | ~ r1_tarski(A_81,k2_relat_1('#skF_4'))
      | r1_xboole_0(A_81,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_219])).

tff(c_225,plain,(
    ! [A_82] :
      ( ~ r1_tarski(A_82,k2_relat_1('#skF_4'))
      | r1_xboole_0(A_82,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_221])).

tff(c_238,plain,(
    r1_xboole_0('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_225])).

tff(c_242,plain,(
    ! [C_83] : ~ r2_hidden(C_83,'#skF_3') ),
    inference(resolution,[status(thm)],[c_238,c_8])).

tff(c_279,plain,(
    ! [B_84] : r1_tarski('#skF_3',B_84) ),
    inference(resolution,[status(thm)],[c_6,c_242])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k4_xboole_0(B_12,A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_293,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_279,c_14])).

tff(c_302,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_293])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:50:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.32  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  
% 2.37/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.32  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_xboole_0 > k10_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.37/1.32  
% 2.37/1.32  %Foreground sorts:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Background operators:
% 2.37/1.32  
% 2.37/1.32  
% 2.37/1.32  %Foreground operators:
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.37/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.37/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.37/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.37/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.37/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.37/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.37/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.37/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.37/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.37/1.32  tff('#skF_4', type, '#skF_4': $i).
% 2.37/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.37/1.32  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.37/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.37/1.32  
% 2.37/1.34  tff(f_71, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k2_relat_1(B))) & (k10_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t174_relat_1)).
% 2.37/1.34  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.37/1.34  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.37/1.34  tff(f_60, axiom, (![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t173_relat_1)).
% 2.37/1.34  tff(f_54, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.37/1.34  tff(c_24, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.34  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.34  tff(c_22, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.34  tff(c_26, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.34  tff(c_20, plain, (k10_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.37/1.34  tff(c_12, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), A_6) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.34  tff(c_41, plain, (![C_25, B_26, A_27]: (r2_hidden(C_25, B_26) | ~r2_hidden(C_25, A_27) | ~r1_tarski(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.34  tff(c_50, plain, (![A_6, B_7, B_26]: (r2_hidden('#skF_2'(A_6, B_7), B_26) | ~r1_tarski(A_6, B_26) | r1_xboole_0(A_6, B_7))), inference(resolution, [status(thm)], [c_12, c_41])).
% 2.37/1.34  tff(c_10, plain, (![A_6, B_7]: (r2_hidden('#skF_2'(A_6, B_7), B_7) | r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.34  tff(c_54, plain, (![B_34, A_35]: (r1_xboole_0(k2_relat_1(B_34), A_35) | k10_relat_1(B_34, A_35)!=k1_xboole_0 | ~v1_relat_1(B_34))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.37/1.34  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.37/1.34  tff(c_79, plain, (![C_45, A_46, B_47]: (~r2_hidden(C_45, A_46) | ~r2_hidden(C_45, k2_relat_1(B_47)) | k10_relat_1(B_47, A_46)!=k1_xboole_0 | ~v1_relat_1(B_47))), inference(resolution, [status(thm)], [c_54, c_8])).
% 2.37/1.34  tff(c_155, plain, (![A_67, B_68, B_69]: (~r2_hidden('#skF_2'(A_67, B_68), k2_relat_1(B_69)) | k10_relat_1(B_69, B_68)!=k1_xboole_0 | ~v1_relat_1(B_69) | r1_xboole_0(A_67, B_68))), inference(resolution, [status(thm)], [c_10, c_79])).
% 2.37/1.34  tff(c_219, plain, (![B_79, B_80, A_81]: (k10_relat_1(B_79, B_80)!=k1_xboole_0 | ~v1_relat_1(B_79) | ~r1_tarski(A_81, k2_relat_1(B_79)) | r1_xboole_0(A_81, B_80))), inference(resolution, [status(thm)], [c_50, c_155])).
% 2.37/1.34  tff(c_221, plain, (![A_81]: (~v1_relat_1('#skF_4') | ~r1_tarski(A_81, k2_relat_1('#skF_4')) | r1_xboole_0(A_81, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_20, c_219])).
% 2.37/1.34  tff(c_225, plain, (![A_82]: (~r1_tarski(A_82, k2_relat_1('#skF_4')) | r1_xboole_0(A_82, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_221])).
% 2.37/1.34  tff(c_238, plain, (r1_xboole_0('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_225])).
% 2.37/1.34  tff(c_242, plain, (![C_83]: (~r2_hidden(C_83, '#skF_3'))), inference(resolution, [status(thm)], [c_238, c_8])).
% 2.37/1.34  tff(c_279, plain, (![B_84]: (r1_tarski('#skF_3', B_84))), inference(resolution, [status(thm)], [c_6, c_242])).
% 2.37/1.34  tff(c_14, plain, (![A_11, B_12]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k4_xboole_0(B_12, A_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.37/1.34  tff(c_293, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_279, c_14])).
% 2.37/1.34  tff(c_302, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_293])).
% 2.37/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.37/1.34  
% 2.37/1.34  Inference rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Ref     : 0
% 2.37/1.34  #Sup     : 64
% 2.37/1.34  #Fact    : 0
% 2.37/1.34  #Define  : 0
% 2.37/1.34  #Split   : 0
% 2.37/1.34  #Chain   : 0
% 2.37/1.34  #Close   : 0
% 2.37/1.34  
% 2.37/1.34  Ordering : KBO
% 2.37/1.34  
% 2.37/1.34  Simplification rules
% 2.37/1.34  ----------------------
% 2.37/1.34  #Subsume      : 4
% 2.37/1.34  #Demod        : 5
% 2.37/1.34  #Tautology    : 6
% 2.37/1.34  #SimpNegUnit  : 1
% 2.37/1.34  #BackRed      : 0
% 2.37/1.34  
% 2.37/1.34  #Partial instantiations: 0
% 2.37/1.34  #Strategies tried      : 1
% 2.37/1.34  
% 2.37/1.34  Timing (in seconds)
% 2.37/1.34  ----------------------
% 2.37/1.34  Preprocessing        : 0.30
% 2.37/1.34  Parsing              : 0.17
% 2.37/1.34  CNF conversion       : 0.02
% 2.37/1.34  Main loop            : 0.24
% 2.37/1.34  Inferencing          : 0.10
% 2.37/1.34  Reduction            : 0.06
% 2.37/1.34  Demodulation         : 0.04
% 2.37/1.34  BG Simplification    : 0.02
% 2.37/1.34  Subsumption          : 0.06
% 2.37/1.34  Abstraction          : 0.01
% 2.37/1.34  MUC search           : 0.00
% 2.37/1.34  Cooper               : 0.00
% 2.37/1.34  Total                : 0.57
% 2.37/1.34  Index Insertion      : 0.00
% 2.37/1.34  Index Deletion       : 0.00
% 2.37/1.34  Index Matching       : 0.00
% 2.37/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
