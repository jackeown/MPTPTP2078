%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:36 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   37 (  55 expanded)
%              Number of leaves         :   17 (  29 expanded)
%              Depth                    :    9
%              Number of atoms          :   70 ( 139 expanded)
%              Number of equality atoms :   12 (  21 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(v2_wellord1,type,(
    v2_wellord1: $i > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ~ ( v2_wellord1(A)
            & k3_relat_1(A) != k1_xboole_0
            & ! [B] :
                ~ ( r2_hidden(B,k3_relat_1(A))
                  & ! [C] :
                      ( r2_hidden(C,k3_relat_1(A))
                     => r2_hidden(k4_tarski(B,C),A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_52,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( v2_wellord1(A)
       => ! [B] :
            ~ ( r1_tarski(B,k3_relat_1(A))
              & B != k1_xboole_0
              & ! [C] :
                  ~ ( r2_hidden(C,B)
                    & ! [D] :
                        ( r2_hidden(D,B)
                       => r2_hidden(k4_tarski(C,D),A) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord1)).

tff(c_12,plain,(
    k3_relat_1('#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_14,plain,(
    v2_wellord1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_22,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_27,plain,(
    ! [A_27] : r1_tarski(A_27,A_27) ),
    inference(resolution,[status(thm)],[c_22,c_4])).

tff(c_55,plain,(
    ! [A_44,B_45] :
      ( r2_hidden('#skF_2'(A_44,B_45),B_45)
      | k1_xboole_0 = B_45
      | ~ r1_tarski(B_45,k3_relat_1(A_44))
      | ~ v2_wellord1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    ! [A_44,B_45,B_2] :
      ( r2_hidden('#skF_2'(A_44,B_45),B_2)
      | ~ r1_tarski(B_45,B_2)
      | k1_xboole_0 = B_45
      | ~ r1_tarski(B_45,k3_relat_1(A_44))
      | ~ v2_wellord1(A_44)
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_55,c_2])).

tff(c_20,plain,(
    ! [B_23] :
      ( r2_hidden('#skF_4'(B_23),k3_relat_1('#skF_3'))
      | ~ r2_hidden(B_23,k3_relat_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_67,plain,(
    ! [A_52,B_53,D_54] :
      ( r2_hidden(k4_tarski('#skF_2'(A_52,B_53),D_54),A_52)
      | ~ r2_hidden(D_54,B_53)
      | k1_xboole_0 = B_53
      | ~ r1_tarski(B_53,k3_relat_1(A_52))
      | ~ v2_wellord1(A_52)
      | ~ v1_relat_1(A_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_18,plain,(
    ! [B_23] :
      ( ~ r2_hidden(k4_tarski(B_23,'#skF_4'(B_23)),'#skF_3')
      | ~ r2_hidden(B_23,k3_relat_1('#skF_3')) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_71,plain,(
    ! [B_53] :
      ( ~ r2_hidden('#skF_2'('#skF_3',B_53),k3_relat_1('#skF_3'))
      | ~ r2_hidden('#skF_4'('#skF_2'('#skF_3',B_53)),B_53)
      | k1_xboole_0 = B_53
      | ~ r1_tarski(B_53,k3_relat_1('#skF_3'))
      | ~ v2_wellord1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_67,c_18])).

tff(c_78,plain,(
    ! [B_55] :
      ( ~ r2_hidden('#skF_2'('#skF_3',B_55),k3_relat_1('#skF_3'))
      | ~ r2_hidden('#skF_4'('#skF_2'('#skF_3',B_55)),B_55)
      | k1_xboole_0 = B_55
      | ~ r1_tarski(B_55,k3_relat_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_71])).

tff(c_86,plain,
    ( k3_relat_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k3_relat_1('#skF_3'),k3_relat_1('#skF_3'))
    | ~ r2_hidden('#skF_2'('#skF_3',k3_relat_1('#skF_3')),k3_relat_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_78])).

tff(c_90,plain,
    ( k3_relat_1('#skF_3') = k1_xboole_0
    | ~ r2_hidden('#skF_2'('#skF_3',k3_relat_1('#skF_3')),k3_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_86])).

tff(c_91,plain,(
    ~ r2_hidden('#skF_2'('#skF_3',k3_relat_1('#skF_3')),k3_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_90])).

tff(c_94,plain,
    ( k3_relat_1('#skF_3') = k1_xboole_0
    | ~ r1_tarski(k3_relat_1('#skF_3'),k3_relat_1('#skF_3'))
    | ~ v2_wellord1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_91])).

tff(c_100,plain,(
    k3_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_27,c_94])).

tff(c_102,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:55:32 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.27  
% 1.86/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.28  %$ r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.86/1.28  
% 1.86/1.28  %Foreground sorts:
% 1.86/1.28  
% 1.86/1.28  
% 1.86/1.28  %Background operators:
% 1.86/1.28  
% 1.86/1.28  
% 1.86/1.28  %Foreground operators:
% 1.86/1.28  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.86/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.86/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.28  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.86/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.28  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.86/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.28  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.28  
% 1.86/1.29  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => ~((v2_wellord1(A) & ~(k3_relat_1(A) = k1_xboole_0)) & (![B]: ~(r2_hidden(B, k3_relat_1(A)) & (![C]: (r2_hidden(C, k3_relat_1(A)) => r2_hidden(k4_tarski(B, C), A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_wellord1)).
% 1.86/1.29  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.86/1.29  tff(f_52, axiom, (![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~((r1_tarski(B, k3_relat_1(A)) & ~(B = k1_xboole_0)) & (![C]: ~(r2_hidden(C, B) & (![D]: (r2_hidden(D, B) => r2_hidden(k4_tarski(C, D), A)))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_wellord1)).
% 1.86/1.29  tff(c_12, plain, (k3_relat_1('#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.86/1.29  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.86/1.29  tff(c_14, plain, (v2_wellord1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.86/1.29  tff(c_22, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.29  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.29  tff(c_27, plain, (![A_27]: (r1_tarski(A_27, A_27))), inference(resolution, [status(thm)], [c_22, c_4])).
% 1.86/1.29  tff(c_55, plain, (![A_44, B_45]: (r2_hidden('#skF_2'(A_44, B_45), B_45) | k1_xboole_0=B_45 | ~r1_tarski(B_45, k3_relat_1(A_44)) | ~v2_wellord1(A_44) | ~v1_relat_1(A_44))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.29  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.29  tff(c_58, plain, (![A_44, B_45, B_2]: (r2_hidden('#skF_2'(A_44, B_45), B_2) | ~r1_tarski(B_45, B_2) | k1_xboole_0=B_45 | ~r1_tarski(B_45, k3_relat_1(A_44)) | ~v2_wellord1(A_44) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_55, c_2])).
% 1.86/1.29  tff(c_20, plain, (![B_23]: (r2_hidden('#skF_4'(B_23), k3_relat_1('#skF_3')) | ~r2_hidden(B_23, k3_relat_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.86/1.29  tff(c_67, plain, (![A_52, B_53, D_54]: (r2_hidden(k4_tarski('#skF_2'(A_52, B_53), D_54), A_52) | ~r2_hidden(D_54, B_53) | k1_xboole_0=B_53 | ~r1_tarski(B_53, k3_relat_1(A_52)) | ~v2_wellord1(A_52) | ~v1_relat_1(A_52))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.29  tff(c_18, plain, (![B_23]: (~r2_hidden(k4_tarski(B_23, '#skF_4'(B_23)), '#skF_3') | ~r2_hidden(B_23, k3_relat_1('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 1.86/1.29  tff(c_71, plain, (![B_53]: (~r2_hidden('#skF_2'('#skF_3', B_53), k3_relat_1('#skF_3')) | ~r2_hidden('#skF_4'('#skF_2'('#skF_3', B_53)), B_53) | k1_xboole_0=B_53 | ~r1_tarski(B_53, k3_relat_1('#skF_3')) | ~v2_wellord1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_67, c_18])).
% 1.86/1.29  tff(c_78, plain, (![B_55]: (~r2_hidden('#skF_2'('#skF_3', B_55), k3_relat_1('#skF_3')) | ~r2_hidden('#skF_4'('#skF_2'('#skF_3', B_55)), B_55) | k1_xboole_0=B_55 | ~r1_tarski(B_55, k3_relat_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_71])).
% 1.86/1.29  tff(c_86, plain, (k3_relat_1('#skF_3')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_3'), k3_relat_1('#skF_3')) | ~r2_hidden('#skF_2'('#skF_3', k3_relat_1('#skF_3')), k3_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_78])).
% 1.86/1.29  tff(c_90, plain, (k3_relat_1('#skF_3')=k1_xboole_0 | ~r2_hidden('#skF_2'('#skF_3', k3_relat_1('#skF_3')), k3_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_86])).
% 1.86/1.29  tff(c_91, plain, (~r2_hidden('#skF_2'('#skF_3', k3_relat_1('#skF_3')), k3_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_12, c_90])).
% 1.86/1.29  tff(c_94, plain, (k3_relat_1('#skF_3')=k1_xboole_0 | ~r1_tarski(k3_relat_1('#skF_3'), k3_relat_1('#skF_3')) | ~v2_wellord1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_58, c_91])).
% 1.86/1.29  tff(c_100, plain, (k3_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_27, c_94])).
% 1.86/1.29  tff(c_102, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_100])).
% 1.86/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.29  
% 1.86/1.29  Inference rules
% 1.86/1.29  ----------------------
% 1.86/1.29  #Ref     : 0
% 1.86/1.29  #Sup     : 16
% 1.86/1.29  #Fact    : 0
% 1.86/1.29  #Define  : 0
% 1.86/1.29  #Split   : 0
% 1.86/1.29  #Chain   : 0
% 1.86/1.29  #Close   : 0
% 1.86/1.29  
% 1.86/1.29  Ordering : KBO
% 1.86/1.29  
% 1.86/1.29  Simplification rules
% 1.86/1.29  ----------------------
% 1.86/1.29  #Subsume      : 2
% 1.86/1.29  #Demod        : 6
% 1.86/1.29  #Tautology    : 1
% 1.86/1.29  #SimpNegUnit  : 2
% 1.86/1.29  #BackRed      : 0
% 1.86/1.29  
% 1.86/1.29  #Partial instantiations: 0
% 1.86/1.29  #Strategies tried      : 1
% 1.86/1.29  
% 1.86/1.29  Timing (in seconds)
% 2.05/1.29  ----------------------
% 2.05/1.29  Preprocessing        : 0.30
% 2.05/1.29  Parsing              : 0.16
% 2.05/1.29  CNF conversion       : 0.02
% 2.05/1.29  Main loop            : 0.16
% 2.05/1.29  Inferencing          : 0.07
% 2.05/1.29  Reduction            : 0.04
% 2.05/1.29  Demodulation         : 0.03
% 2.05/1.29  BG Simplification    : 0.02
% 2.05/1.29  Subsumption          : 0.03
% 2.05/1.29  Abstraction          : 0.01
% 2.05/1.29  MUC search           : 0.00
% 2.05/1.29  Cooper               : 0.00
% 2.05/1.29  Total                : 0.49
% 2.05/1.29  Index Insertion      : 0.00
% 2.05/1.29  Index Deletion       : 0.00
% 2.05/1.29  Index Matching       : 0.00
% 2.05/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
