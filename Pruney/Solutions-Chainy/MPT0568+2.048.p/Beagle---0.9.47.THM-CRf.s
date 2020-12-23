%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:26 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   39 (  54 expanded)
%              Number of leaves         :   25 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  63 expanded)
%              Number of equality atoms :   10 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1 > #skF_6

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i > $i )).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k10_relat_1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ? [E] :
                  ( r2_hidden(k4_tarski(D,E),A)
                  & r2_hidden(E,B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d14_relat_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_32,plain,(
    ! [A_50] :
      ( r2_hidden('#skF_6'(A_50),A_50)
      | v1_relat_1(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_45,plain,(
    ! [A_74,B_75,C_76] :
      ( ~ r1_xboole_0(A_74,B_75)
      | ~ r2_hidden(C_76,k3_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_52,plain,(
    ! [A_6,C_76] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_76,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_45])).

tff(c_56,plain,(
    ! [C_77] : ~ r2_hidden(C_77,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_61,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_56])).

tff(c_496,plain,(
    ! [A_146,B_147,C_148] :
      ( r2_hidden(k4_tarski('#skF_2'(A_146,B_147,C_148),'#skF_3'(A_146,B_147,C_148)),A_146)
      | r2_hidden('#skF_4'(A_146,B_147,C_148),C_148)
      | k10_relat_1(A_146,B_147) = C_148
      | ~ v1_relat_1(A_146) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    ! [C_76] : ~ r2_hidden(C_76,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_52])).

tff(c_530,plain,(
    ! [B_147,C_148] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_147,C_148),C_148)
      | k10_relat_1(k1_xboole_0,B_147) = C_148
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_496,c_55])).

tff(c_993,plain,(
    ! [B_161,C_162] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_161,C_162),C_162)
      | k10_relat_1(k1_xboole_0,B_161) = C_162 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_530])).

tff(c_1040,plain,(
    ! [B_161] : k10_relat_1(k1_xboole_0,B_161) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_993,c_55])).

tff(c_34,plain,(
    k10_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_1059,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1040,c_34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n009.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 13:04:26 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.35  
% 2.63/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.63/1.36  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_2 > #skF_8 > #skF_9 > #skF_5 > #skF_3 > #skF_7 > #skF_1 > #skF_6
% 2.63/1.36  
% 2.63/1.36  %Foreground sorts:
% 2.63/1.36  
% 2.63/1.36  
% 2.63/1.36  %Background operators:
% 2.63/1.36  
% 2.63/1.36  
% 2.63/1.36  %Foreground operators:
% 2.63/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.36  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.63/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.63/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.63/1.36  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 2.63/1.36  tff('#skF_9', type, '#skF_9': $i).
% 2.63/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.36  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.63/1.36  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.63/1.36  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.63/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.63/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.36  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 2.63/1.36  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.36  tff('#skF_6', type, '#skF_6': $i > $i).
% 2.63/1.36  
% 2.86/1.37  tff(f_66, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.86/1.37  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.86/1.37  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.86/1.37  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.86/1.37  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.86/1.37  tff(f_69, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.86/1.37  tff(c_32, plain, (![A_50]: (r2_hidden('#skF_6'(A_50), A_50) | v1_relat_1(A_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.86/1.37  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.86/1.37  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.86/1.37  tff(c_45, plain, (![A_74, B_75, C_76]: (~r1_xboole_0(A_74, B_75) | ~r2_hidden(C_76, k3_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.86/1.37  tff(c_52, plain, (![A_6, C_76]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_76, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_45])).
% 2.86/1.37  tff(c_56, plain, (![C_77]: (~r2_hidden(C_77, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_52])).
% 2.86/1.37  tff(c_61, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_32, c_56])).
% 2.86/1.37  tff(c_496, plain, (![A_146, B_147, C_148]: (r2_hidden(k4_tarski('#skF_2'(A_146, B_147, C_148), '#skF_3'(A_146, B_147, C_148)), A_146) | r2_hidden('#skF_4'(A_146, B_147, C_148), C_148) | k10_relat_1(A_146, B_147)=C_148 | ~v1_relat_1(A_146))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.86/1.37  tff(c_55, plain, (![C_76]: (~r2_hidden(C_76, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_52])).
% 2.86/1.37  tff(c_530, plain, (![B_147, C_148]: (r2_hidden('#skF_4'(k1_xboole_0, B_147, C_148), C_148) | k10_relat_1(k1_xboole_0, B_147)=C_148 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_496, c_55])).
% 2.86/1.37  tff(c_993, plain, (![B_161, C_162]: (r2_hidden('#skF_4'(k1_xboole_0, B_161, C_162), C_162) | k10_relat_1(k1_xboole_0, B_161)=C_162)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_530])).
% 2.86/1.37  tff(c_1040, plain, (![B_161]: (k10_relat_1(k1_xboole_0, B_161)=k1_xboole_0)), inference(resolution, [status(thm)], [c_993, c_55])).
% 2.86/1.37  tff(c_34, plain, (k10_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.86/1.37  tff(c_1059, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1040, c_34])).
% 2.86/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.86/1.37  
% 2.86/1.37  Inference rules
% 2.86/1.37  ----------------------
% 2.86/1.37  #Ref     : 1
% 2.86/1.37  #Sup     : 209
% 2.86/1.37  #Fact    : 0
% 2.86/1.37  #Define  : 0
% 2.86/1.37  #Split   : 0
% 2.86/1.37  #Chain   : 0
% 2.86/1.37  #Close   : 0
% 2.86/1.37  
% 2.86/1.37  Ordering : KBO
% 2.86/1.37  
% 2.86/1.37  Simplification rules
% 2.86/1.37  ----------------------
% 2.86/1.37  #Subsume      : 71
% 2.86/1.37  #Demod        : 118
% 2.86/1.37  #Tautology    : 57
% 2.86/1.37  #SimpNegUnit  : 10
% 2.86/1.37  #BackRed      : 11
% 2.86/1.37  
% 2.86/1.37  #Partial instantiations: 0
% 2.86/1.37  #Strategies tried      : 1
% 2.86/1.37  
% 2.86/1.37  Timing (in seconds)
% 2.86/1.37  ----------------------
% 2.86/1.37  Preprocessing        : 0.28
% 2.86/1.37  Parsing              : 0.15
% 2.86/1.37  CNF conversion       : 0.03
% 2.86/1.37  Main loop            : 0.35
% 2.86/1.37  Inferencing          : 0.14
% 2.86/1.37  Reduction            : 0.09
% 2.86/1.37  Demodulation         : 0.06
% 2.86/1.37  BG Simplification    : 0.02
% 2.86/1.37  Subsumption          : 0.08
% 2.86/1.37  Abstraction          : 0.02
% 2.86/1.37  MUC search           : 0.00
% 2.86/1.37  Cooper               : 0.00
% 2.86/1.37  Total                : 0.66
% 2.86/1.37  Index Insertion      : 0.00
% 2.86/1.37  Index Deletion       : 0.00
% 2.86/1.37  Index Matching       : 0.00
% 2.86/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
