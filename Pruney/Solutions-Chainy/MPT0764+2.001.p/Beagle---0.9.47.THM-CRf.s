%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:35 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   36 (  48 expanded)
%              Number of leaves         :   18 (  27 expanded)
%              Depth                    :   10
%              Number of atoms          :   70 ( 136 expanded)
%              Number of equality atoms :   10 (  20 expanded)
%              Maximal formula depth    :   14 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(r2_wellord1,type,(
    r2_wellord1: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_72,negated_conjecture,(
    ~ ! [A] :
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( r2_wellord1(A,k3_relat_1(A))
      <=> v2_wellord1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_wellord1(B,A)
       => ! [C] :
            ~ ( r1_tarski(C,A)
              & C != k1_xboole_0
              & ! [D] :
                  ~ ( r2_hidden(D,C)
                    & ! [E] :
                        ( r2_hidden(E,C)
                       => r2_hidden(k4_tarski(D,E),B) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_wellord1)).

tff(c_16,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_14,plain,(
    v2_wellord1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_12,plain,(
    r1_tarski('#skF_3',k3_relat_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_wellord1(A_1,k3_relat_1(A_1))
      | ~ v2_wellord1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_2,B_3,C_11] :
      ( r2_hidden('#skF_1'(A_2,B_3,C_11),C_11)
      | k1_xboole_0 = C_11
      | ~ r1_tarski(C_11,A_2)
      | ~ r2_wellord1(B_3,A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [C_27] :
      ( r2_hidden('#skF_4'(C_27),'#skF_3')
      | ~ r2_hidden(C_27,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30,plain,(
    ! [A_36,B_37,C_38,E_39] :
      ( r2_hidden(k4_tarski('#skF_1'(A_36,B_37,C_38),E_39),B_37)
      | ~ r2_hidden(E_39,C_38)
      | k1_xboole_0 = C_38
      | ~ r1_tarski(C_38,A_36)
      | ~ r2_wellord1(B_37,A_36)
      | ~ v1_relat_1(B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_18,plain,(
    ! [C_27] :
      ( ~ r2_hidden(k4_tarski(C_27,'#skF_4'(C_27)),'#skF_2')
      | ~ r2_hidden(C_27,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_34,plain,(
    ! [A_36,C_38] :
      ( ~ r2_hidden('#skF_1'(A_36,'#skF_2',C_38),'#skF_3')
      | ~ r2_hidden('#skF_4'('#skF_1'(A_36,'#skF_2',C_38)),C_38)
      | k1_xboole_0 = C_38
      | ~ r1_tarski(C_38,A_36)
      | ~ r2_wellord1('#skF_2',A_36)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_18])).

tff(c_38,plain,(
    ! [A_40,C_41] :
      ( ~ r2_hidden('#skF_1'(A_40,'#skF_2',C_41),'#skF_3')
      | ~ r2_hidden('#skF_4'('#skF_1'(A_40,'#skF_2',C_41)),C_41)
      | k1_xboole_0 = C_41
      | ~ r1_tarski(C_41,A_40)
      | ~ r2_wellord1('#skF_2',A_40) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_34])).

tff(c_42,plain,(
    ! [A_40] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r1_tarski('#skF_3',A_40)
      | ~ r2_wellord1('#skF_2',A_40)
      | ~ r2_hidden('#skF_1'(A_40,'#skF_2','#skF_3'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_38])).

tff(c_46,plain,(
    ! [A_42] :
      ( ~ r1_tarski('#skF_3',A_42)
      | ~ r2_wellord1('#skF_2',A_42)
      | ~ r2_hidden('#skF_1'(A_42,'#skF_2','#skF_3'),'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_42])).

tff(c_50,plain,(
    ! [A_2] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r1_tarski('#skF_3',A_2)
      | ~ r2_wellord1('#skF_2',A_2)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_8,c_46])).

tff(c_53,plain,(
    ! [A_2] :
      ( k1_xboole_0 = '#skF_3'
      | ~ r1_tarski('#skF_3',A_2)
      | ~ r2_wellord1('#skF_2',A_2) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_50])).

tff(c_55,plain,(
    ! [A_43] :
      ( ~ r1_tarski('#skF_3',A_43)
      | ~ r2_wellord1('#skF_2',A_43) ) ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_53])).

tff(c_59,plain,
    ( ~ r1_tarski('#skF_3',k3_relat_1('#skF_2'))
    | ~ v2_wellord1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2,c_55])).

tff(c_63,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_14,c_12,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n004.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:11:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  %$ r2_wellord1 > r2_hidden > r1_tarski > v2_wellord1 > v1_relat_1 > k4_tarski > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_4 > #skF_2 > #skF_3
% 1.64/1.11  
% 1.64/1.11  %Foreground sorts:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Background operators:
% 1.64/1.11  
% 1.64/1.11  
% 1.64/1.11  %Foreground operators:
% 1.64/1.11  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.64/1.11  tff('#skF_4', type, '#skF_4': $i > $i).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.11  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.64/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.11  tff(v2_wellord1, type, v2_wellord1: $i > $o).
% 1.64/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.11  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.11  tff(r2_wellord1, type, r2_wellord1: ($i * $i) > $o).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.11  
% 1.64/1.12  tff(f_72, negated_conjecture, ~(![A]: (v1_relat_1(A) => (v2_wellord1(A) => (![B]: ~((r1_tarski(B, k3_relat_1(A)) & ~(B = k1_xboole_0)) & (![C]: ~(r2_hidden(C, B) & (![D]: (r2_hidden(D, B) => r2_hidden(k4_tarski(C, D), A)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_wellord1)).
% 1.64/1.12  tff(f_31, axiom, (![A]: (v1_relat_1(A) => (r2_wellord1(A, k3_relat_1(A)) <=> v2_wellord1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_wellord1)).
% 1.64/1.12  tff(f_51, axiom, (![A, B]: (v1_relat_1(B) => (r2_wellord1(B, A) => (![C]: ~((r1_tarski(C, A) & ~(C = k1_xboole_0)) & (![D]: ~(r2_hidden(D, C) & (![E]: (r2_hidden(E, C) => r2_hidden(k4_tarski(D, E), B)))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_wellord1)).
% 1.64/1.12  tff(c_16, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.12  tff(c_14, plain, (v2_wellord1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.12  tff(c_12, plain, (r1_tarski('#skF_3', k3_relat_1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.12  tff(c_2, plain, (![A_1]: (r2_wellord1(A_1, k3_relat_1(A_1)) | ~v2_wellord1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.12  tff(c_10, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.12  tff(c_8, plain, (![A_2, B_3, C_11]: (r2_hidden('#skF_1'(A_2, B_3, C_11), C_11) | k1_xboole_0=C_11 | ~r1_tarski(C_11, A_2) | ~r2_wellord1(B_3, A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.12  tff(c_20, plain, (![C_27]: (r2_hidden('#skF_4'(C_27), '#skF_3') | ~r2_hidden(C_27, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.12  tff(c_30, plain, (![A_36, B_37, C_38, E_39]: (r2_hidden(k4_tarski('#skF_1'(A_36, B_37, C_38), E_39), B_37) | ~r2_hidden(E_39, C_38) | k1_xboole_0=C_38 | ~r1_tarski(C_38, A_36) | ~r2_wellord1(B_37, A_36) | ~v1_relat_1(B_37))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.64/1.12  tff(c_18, plain, (![C_27]: (~r2_hidden(k4_tarski(C_27, '#skF_4'(C_27)), '#skF_2') | ~r2_hidden(C_27, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.64/1.12  tff(c_34, plain, (![A_36, C_38]: (~r2_hidden('#skF_1'(A_36, '#skF_2', C_38), '#skF_3') | ~r2_hidden('#skF_4'('#skF_1'(A_36, '#skF_2', C_38)), C_38) | k1_xboole_0=C_38 | ~r1_tarski(C_38, A_36) | ~r2_wellord1('#skF_2', A_36) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_18])).
% 1.64/1.12  tff(c_38, plain, (![A_40, C_41]: (~r2_hidden('#skF_1'(A_40, '#skF_2', C_41), '#skF_3') | ~r2_hidden('#skF_4'('#skF_1'(A_40, '#skF_2', C_41)), C_41) | k1_xboole_0=C_41 | ~r1_tarski(C_41, A_40) | ~r2_wellord1('#skF_2', A_40))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_34])).
% 1.64/1.12  tff(c_42, plain, (![A_40]: (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', A_40) | ~r2_wellord1('#skF_2', A_40) | ~r2_hidden('#skF_1'(A_40, '#skF_2', '#skF_3'), '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_38])).
% 1.64/1.12  tff(c_46, plain, (![A_42]: (~r1_tarski('#skF_3', A_42) | ~r2_wellord1('#skF_2', A_42) | ~r2_hidden('#skF_1'(A_42, '#skF_2', '#skF_3'), '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_10, c_42])).
% 1.64/1.12  tff(c_50, plain, (![A_2]: (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', A_2) | ~r2_wellord1('#skF_2', A_2) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_8, c_46])).
% 1.64/1.12  tff(c_53, plain, (![A_2]: (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', A_2) | ~r2_wellord1('#skF_2', A_2))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_50])).
% 1.64/1.12  tff(c_55, plain, (![A_43]: (~r1_tarski('#skF_3', A_43) | ~r2_wellord1('#skF_2', A_43))), inference(negUnitSimplification, [status(thm)], [c_10, c_53])).
% 1.64/1.12  tff(c_59, plain, (~r1_tarski('#skF_3', k3_relat_1('#skF_2')) | ~v2_wellord1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2, c_55])).
% 1.64/1.12  tff(c_63, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_14, c_12, c_59])).
% 1.64/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.12  
% 1.64/1.12  Inference rules
% 1.64/1.12  ----------------------
% 1.64/1.12  #Ref     : 0
% 1.64/1.12  #Sup     : 5
% 1.64/1.12  #Fact    : 0
% 1.64/1.12  #Define  : 0
% 1.64/1.13  #Split   : 0
% 1.64/1.13  #Chain   : 0
% 1.64/1.13  #Close   : 0
% 1.64/1.13  
% 1.64/1.13  Ordering : KBO
% 1.64/1.13  
% 1.64/1.13  Simplification rules
% 1.64/1.13  ----------------------
% 1.64/1.13  #Subsume      : 1
% 1.64/1.13  #Demod        : 5
% 1.64/1.13  #Tautology    : 1
% 1.64/1.13  #SimpNegUnit  : 2
% 1.64/1.13  #BackRed      : 0
% 1.64/1.13  
% 1.64/1.13  #Partial instantiations: 0
% 1.64/1.13  #Strategies tried      : 1
% 1.64/1.13  
% 1.64/1.13  Timing (in seconds)
% 1.64/1.13  ----------------------
% 1.64/1.13  Preprocessing        : 0.27
% 1.64/1.13  Parsing              : 0.14
% 1.64/1.13  CNF conversion       : 0.02
% 1.64/1.13  Main loop            : 0.10
% 1.64/1.13  Inferencing          : 0.05
% 1.64/1.13  Reduction            : 0.02
% 1.64/1.13  Demodulation         : 0.02
% 1.64/1.13  BG Simplification    : 0.01
% 1.64/1.13  Subsumption          : 0.01
% 1.64/1.13  Abstraction          : 0.00
% 1.64/1.13  MUC search           : 0.00
% 1.64/1.13  Cooper               : 0.00
% 1.64/1.13  Total                : 0.40
% 1.64/1.13  Index Insertion      : 0.00
% 1.64/1.13  Index Deletion       : 0.00
% 1.64/1.13  Index Matching       : 0.00
% 1.64/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
