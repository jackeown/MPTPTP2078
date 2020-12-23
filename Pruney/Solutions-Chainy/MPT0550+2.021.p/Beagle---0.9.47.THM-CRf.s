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
% DateTime   : Thu Dec  3 10:00:54 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   20 (  27 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 (  95 expanded)
%              Number of equality atoms :   21 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_58,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

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

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    k9_relat_1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_35,plain,(
    ! [A_22,B_23] :
      ( r2_hidden('#skF_1'(A_22,B_23),A_22)
      | r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_40,plain,(
    ! [A_22] : r1_tarski(A_22,A_22) ),
    inference(resolution,[status(thm)],[c_35,c_4])).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    r1_tarski('#skF_4',k1_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_14,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_41,plain,(
    ! [C_24,B_25,A_26] :
      ( r2_hidden(C_24,B_25)
      | ~ r2_hidden(C_24,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_56,plain,(
    ! [A_31,B_32] :
      ( r2_hidden('#skF_3'(A_31),B_32)
      | ~ r1_tarski(A_31,B_32)
      | k1_xboole_0 = A_31 ) ),
    inference(resolution,[status(thm)],[c_14,c_41])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_86,plain,(
    ! [A_46,B_47,B_48] :
      ( r2_hidden('#skF_3'(A_46),B_47)
      | ~ r1_tarski(B_48,B_47)
      | ~ r1_tarski(A_46,B_48)
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_56,c_2])).

tff(c_92,plain,(
    ! [A_46] :
      ( r2_hidden('#skF_3'(A_46),k1_relat_1('#skF_5'))
      | ~ r1_tarski(A_46,'#skF_4')
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_22,c_86])).

tff(c_61,plain,(
    ! [B_35,A_36] :
      ( r1_xboole_0(k1_relat_1(B_35),A_36)
      | k9_relat_1(B_35,A_36) != k1_xboole_0
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,B_7)
      | ~ r2_hidden(C_10,A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_97,plain,(
    ! [C_50,A_51,B_52] :
      ( ~ r2_hidden(C_50,A_51)
      | ~ r2_hidden(C_50,k1_relat_1(B_52))
      | k9_relat_1(B_52,A_51) != k1_xboole_0
      | ~ v1_relat_1(B_52) ) ),
    inference(resolution,[status(thm)],[c_61,c_8])).

tff(c_125,plain,(
    ! [A_53,B_54] :
      ( ~ r2_hidden('#skF_3'(A_53),k1_relat_1(B_54))
      | k9_relat_1(B_54,A_53) != k1_xboole_0
      | ~ v1_relat_1(B_54)
      | k1_xboole_0 = A_53 ) ),
    inference(resolution,[status(thm)],[c_14,c_97])).

tff(c_128,plain,(
    ! [A_46] :
      ( k9_relat_1('#skF_5',A_46) != k1_xboole_0
      | ~ v1_relat_1('#skF_5')
      | ~ r1_tarski(A_46,'#skF_4')
      | k1_xboole_0 = A_46 ) ),
    inference(resolution,[status(thm)],[c_92,c_125])).

tff(c_142,plain,(
    ! [A_55] :
      ( k9_relat_1('#skF_5',A_55) != k1_xboole_0
      | ~ r1_tarski(A_55,'#skF_4')
      | k1_xboole_0 = A_55 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_128])).

tff(c_146,plain,
    ( k9_relat_1('#skF_5','#skF_4') != k1_xboole_0
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_40,c_142])).

tff(c_149,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_146])).

tff(c_151,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:52:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.18  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.97/1.18  
% 1.97/1.18  %Foreground sorts:
% 1.97/1.18  
% 1.97/1.18  
% 1.97/1.18  %Background operators:
% 1.97/1.18  
% 1.97/1.18  
% 1.97/1.18  %Foreground operators:
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.97/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.97/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.97/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.97/1.18  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.97/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.97/1.18  tff('#skF_3', type, '#skF_3': $i > $i).
% 1.97/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.97/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.97/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.97/1.18  
% 1.97/1.19  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 1.97/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.97/1.19  tff(f_58, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.97/1.19  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 1.97/1.19  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.97/1.19  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.19  tff(c_20, plain, (k9_relat_1('#skF_5', '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.19  tff(c_35, plain, (![A_22, B_23]: (r2_hidden('#skF_1'(A_22, B_23), A_22) | r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.19  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.19  tff(c_40, plain, (![A_22]: (r1_tarski(A_22, A_22))), inference(resolution, [status(thm)], [c_35, c_4])).
% 1.97/1.19  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.19  tff(c_22, plain, (r1_tarski('#skF_4', k1_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.97/1.19  tff(c_14, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.19  tff(c_41, plain, (![C_24, B_25, A_26]: (r2_hidden(C_24, B_25) | ~r2_hidden(C_24, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.19  tff(c_56, plain, (![A_31, B_32]: (r2_hidden('#skF_3'(A_31), B_32) | ~r1_tarski(A_31, B_32) | k1_xboole_0=A_31)), inference(resolution, [status(thm)], [c_14, c_41])).
% 1.97/1.19  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.97/1.19  tff(c_86, plain, (![A_46, B_47, B_48]: (r2_hidden('#skF_3'(A_46), B_47) | ~r1_tarski(B_48, B_47) | ~r1_tarski(A_46, B_48) | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_56, c_2])).
% 1.97/1.19  tff(c_92, plain, (![A_46]: (r2_hidden('#skF_3'(A_46), k1_relat_1('#skF_5')) | ~r1_tarski(A_46, '#skF_4') | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_22, c_86])).
% 1.97/1.19  tff(c_61, plain, (![B_35, A_36]: (r1_xboole_0(k1_relat_1(B_35), A_36) | k9_relat_1(B_35, A_36)!=k1_xboole_0 | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.97/1.19  tff(c_8, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, B_7) | ~r2_hidden(C_10, A_6))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.97/1.19  tff(c_97, plain, (![C_50, A_51, B_52]: (~r2_hidden(C_50, A_51) | ~r2_hidden(C_50, k1_relat_1(B_52)) | k9_relat_1(B_52, A_51)!=k1_xboole_0 | ~v1_relat_1(B_52))), inference(resolution, [status(thm)], [c_61, c_8])).
% 1.97/1.19  tff(c_125, plain, (![A_53, B_54]: (~r2_hidden('#skF_3'(A_53), k1_relat_1(B_54)) | k9_relat_1(B_54, A_53)!=k1_xboole_0 | ~v1_relat_1(B_54) | k1_xboole_0=A_53)), inference(resolution, [status(thm)], [c_14, c_97])).
% 1.97/1.19  tff(c_128, plain, (![A_46]: (k9_relat_1('#skF_5', A_46)!=k1_xboole_0 | ~v1_relat_1('#skF_5') | ~r1_tarski(A_46, '#skF_4') | k1_xboole_0=A_46)), inference(resolution, [status(thm)], [c_92, c_125])).
% 1.97/1.19  tff(c_142, plain, (![A_55]: (k9_relat_1('#skF_5', A_55)!=k1_xboole_0 | ~r1_tarski(A_55, '#skF_4') | k1_xboole_0=A_55)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_128])).
% 1.97/1.19  tff(c_146, plain, (k9_relat_1('#skF_5', '#skF_4')!=k1_xboole_0 | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_40, c_142])).
% 1.97/1.19  tff(c_149, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_20, c_146])).
% 1.97/1.19  tff(c_151, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_149])).
% 1.97/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.19  
% 1.97/1.19  Inference rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Ref     : 0
% 1.97/1.19  #Sup     : 30
% 1.97/1.19  #Fact    : 0
% 1.97/1.19  #Define  : 0
% 1.97/1.19  #Split   : 0
% 1.97/1.19  #Chain   : 0
% 1.97/1.19  #Close   : 0
% 1.97/1.19  
% 1.97/1.19  Ordering : KBO
% 1.97/1.19  
% 1.97/1.19  Simplification rules
% 1.97/1.19  ----------------------
% 1.97/1.19  #Subsume      : 1
% 1.97/1.19  #Demod        : 2
% 1.97/1.19  #Tautology    : 4
% 1.97/1.19  #SimpNegUnit  : 1
% 1.97/1.19  #BackRed      : 0
% 1.97/1.19  
% 1.97/1.19  #Partial instantiations: 0
% 1.97/1.19  #Strategies tried      : 1
% 1.97/1.19  
% 1.97/1.19  Timing (in seconds)
% 1.97/1.19  ----------------------
% 1.97/1.19  Preprocessing        : 0.27
% 1.97/1.19  Parsing              : 0.14
% 1.97/1.19  CNF conversion       : 0.02
% 1.97/1.19  Main loop            : 0.17
% 1.97/1.19  Inferencing          : 0.07
% 1.97/1.19  Reduction            : 0.04
% 1.97/1.19  Demodulation         : 0.03
% 1.97/1.19  BG Simplification    : 0.01
% 1.97/1.19  Subsumption          : 0.04
% 1.97/1.19  Abstraction          : 0.01
% 1.97/1.19  MUC search           : 0.00
% 1.97/1.19  Cooper               : 0.00
% 1.97/1.19  Total                : 0.46
% 1.97/1.19  Index Insertion      : 0.00
% 1.97/1.19  Index Deletion       : 0.00
% 1.97/1.19  Index Matching       : 0.00
% 1.97/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
