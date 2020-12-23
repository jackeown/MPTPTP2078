%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:04:32 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   43 (  67 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   51 ( 109 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ! [B,C] :
            ( r1_xboole_0(B,C)
           => r1_xboole_0(k10_relat_1(A,B),k10_relat_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_funct_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => k10_relat_1(C,k3_xboole_0(A,B)) = k3_xboole_0(k10_relat_1(C,A),k10_relat_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t137_funct_1)).

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

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_36,plain,(
    v1_relat_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    r1_xboole_0('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    ! [A_57,B_58] :
      ( k3_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_xboole_0(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_50,plain,(
    k3_xboole_0('#skF_7','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_32,c_42])).

tff(c_76,plain,(
    ! [C_69,A_70,B_71] :
      ( k3_xboole_0(k10_relat_1(C_69,A_70),k10_relat_1(C_69,B_71)) = k10_relat_1(C_69,k3_xboole_0(A_70,B_71))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_37,plain,(
    ! [A_55,B_56] :
      ( r1_xboole_0(A_55,B_56)
      | k3_xboole_0(A_55,B_56) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_30,plain,(
    ~ r1_xboole_0(k10_relat_1('#skF_6','#skF_7'),k10_relat_1('#skF_6','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_41,plain,(
    k3_xboole_0(k10_relat_1('#skF_6','#skF_7'),k10_relat_1('#skF_6','#skF_8')) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_37,c_30])).

tff(c_85,plain,
    ( k10_relat_1('#skF_6',k3_xboole_0('#skF_7','#skF_8')) != k1_xboole_0
    | ~ v1_funct_1('#skF_6')
    | ~ v1_relat_1('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_41])).

tff(c_94,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_34,c_50,c_85])).

tff(c_110,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_3'(A_75,B_76,C_77),B_76)
      | r2_hidden('#skF_4'(A_75,B_76,C_77),C_77)
      | k10_relat_1(A_75,B_76) = C_77
      | ~ v1_relat_1(A_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_58,plain,(
    ! [C_61] :
      ( ~ r1_xboole_0('#skF_7','#skF_8')
      | ~ r2_hidden(C_61,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_55])).

tff(c_60,plain,(
    ! [C_61] : ~ r2_hidden(C_61,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_58])).

tff(c_190,plain,(
    ! [A_87,B_88] :
      ( r2_hidden('#skF_3'(A_87,B_88,k1_xboole_0),B_88)
      | k10_relat_1(A_87,B_88) = k1_xboole_0
      | ~ v1_relat_1(A_87) ) ),
    inference(resolution,[status(thm)],[c_110,c_60])).

tff(c_219,plain,(
    ! [A_89] :
      ( k10_relat_1(A_89,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_89) ) ),
    inference(resolution,[status(thm)],[c_190,c_60])).

tff(c_222,plain,(
    k10_relat_1('#skF_6',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_219])).

tff(c_226,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_222])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n008.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:40:15 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.31  
% 2.12/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.32  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > v1_funct_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_5 > #skF_3 > #skF_1
% 2.12/1.32  
% 2.12/1.32  %Foreground sorts:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Background operators:
% 2.12/1.32  
% 2.12/1.32  
% 2.12/1.32  %Foreground operators:
% 2.12/1.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.32  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.12/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.32  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.12/1.32  tff('#skF_7', type, '#skF_7': $i).
% 2.12/1.32  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.32  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.12/1.32  tff('#skF_8', type, '#skF_8': $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.32  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.12/1.32  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 2.12/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.12/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.12/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.12/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.12/1.32  
% 2.12/1.33  tff(f_72, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B, C]: (r1_xboole_0(B, C) => r1_xboole_0(k10_relat_1(A, B), k10_relat_1(A, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_funct_1)).
% 2.12/1.33  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.12/1.33  tff(f_62, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (k10_relat_1(C, k3_xboole_0(A, B)) = k3_xboole_0(k10_relat_1(C, A), k10_relat_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t137_funct_1)).
% 2.12/1.33  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 2.12/1.33  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.12/1.33  tff(c_36, plain, (v1_relat_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.33  tff(c_34, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.33  tff(c_32, plain, (r1_xboole_0('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.33  tff(c_42, plain, (![A_57, B_58]: (k3_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.33  tff(c_50, plain, (k3_xboole_0('#skF_7', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_32, c_42])).
% 2.12/1.33  tff(c_76, plain, (![C_69, A_70, B_71]: (k3_xboole_0(k10_relat_1(C_69, A_70), k10_relat_1(C_69, B_71))=k10_relat_1(C_69, k3_xboole_0(A_70, B_71)) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.12/1.33  tff(c_37, plain, (![A_55, B_56]: (r1_xboole_0(A_55, B_56) | k3_xboole_0(A_55, B_56)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.12/1.33  tff(c_30, plain, (~r1_xboole_0(k10_relat_1('#skF_6', '#skF_7'), k10_relat_1('#skF_6', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.12/1.33  tff(c_41, plain, (k3_xboole_0(k10_relat_1('#skF_6', '#skF_7'), k10_relat_1('#skF_6', '#skF_8'))!=k1_xboole_0), inference(resolution, [status(thm)], [c_37, c_30])).
% 2.12/1.33  tff(c_85, plain, (k10_relat_1('#skF_6', k3_xboole_0('#skF_7', '#skF_8'))!=k1_xboole_0 | ~v1_funct_1('#skF_6') | ~v1_relat_1('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_76, c_41])).
% 2.12/1.33  tff(c_94, plain, (k10_relat_1('#skF_6', k1_xboole_0)!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_36, c_34, c_50, c_85])).
% 2.12/1.33  tff(c_110, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_3'(A_75, B_76, C_77), B_76) | r2_hidden('#skF_4'(A_75, B_76, C_77), C_77) | k10_relat_1(A_75, B_76)=C_77 | ~v1_relat_1(A_75))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.12/1.33  tff(c_55, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.12/1.33  tff(c_58, plain, (![C_61]: (~r1_xboole_0('#skF_7', '#skF_8') | ~r2_hidden(C_61, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_50, c_55])).
% 2.12/1.33  tff(c_60, plain, (![C_61]: (~r2_hidden(C_61, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_58])).
% 2.12/1.33  tff(c_190, plain, (![A_87, B_88]: (r2_hidden('#skF_3'(A_87, B_88, k1_xboole_0), B_88) | k10_relat_1(A_87, B_88)=k1_xboole_0 | ~v1_relat_1(A_87))), inference(resolution, [status(thm)], [c_110, c_60])).
% 2.12/1.33  tff(c_219, plain, (![A_89]: (k10_relat_1(A_89, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_89))), inference(resolution, [status(thm)], [c_190, c_60])).
% 2.12/1.33  tff(c_222, plain, (k10_relat_1('#skF_6', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_219])).
% 2.12/1.33  tff(c_226, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_222])).
% 2.12/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.12/1.33  
% 2.12/1.33  Inference rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Ref     : 0
% 2.12/1.33  #Sup     : 40
% 2.12/1.33  #Fact    : 0
% 2.12/1.33  #Define  : 0
% 2.12/1.33  #Split   : 0
% 2.12/1.33  #Chain   : 0
% 2.12/1.33  #Close   : 0
% 2.12/1.33  
% 2.12/1.33  Ordering : KBO
% 2.12/1.33  
% 2.12/1.33  Simplification rules
% 2.12/1.33  ----------------------
% 2.12/1.33  #Subsume      : 1
% 2.12/1.33  #Demod        : 6
% 2.12/1.33  #Tautology    : 7
% 2.12/1.33  #SimpNegUnit  : 2
% 2.12/1.33  #BackRed      : 0
% 2.12/1.33  
% 2.12/1.33  #Partial instantiations: 0
% 2.12/1.33  #Strategies tried      : 1
% 2.12/1.33  
% 2.12/1.33  Timing (in seconds)
% 2.12/1.33  ----------------------
% 2.12/1.33  Preprocessing        : 0.34
% 2.12/1.33  Parsing              : 0.19
% 2.12/1.33  CNF conversion       : 0.03
% 2.12/1.33  Main loop            : 0.18
% 2.12/1.33  Inferencing          : 0.07
% 2.12/1.33  Reduction            : 0.05
% 2.12/1.33  Demodulation         : 0.03
% 2.12/1.33  BG Simplification    : 0.01
% 2.12/1.33  Subsumption          : 0.03
% 2.12/1.33  Abstraction          : 0.01
% 2.12/1.33  MUC search           : 0.00
% 2.12/1.33  Cooper               : 0.00
% 2.12/1.33  Total                : 0.55
% 2.12/1.33  Index Insertion      : 0.00
% 2.12/1.33  Index Deletion       : 0.00
% 2.12/1.33  Index Matching       : 0.00
% 2.12/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
