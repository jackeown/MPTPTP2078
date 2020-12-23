%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:53 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   44 (  56 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  70 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_7 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(C,D),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_relat_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_relat_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k2_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_relat_1)).

tff(c_26,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_33,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_5] :
      ( r2_hidden('#skF_2'(A_5),A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_79,plain,(
    ! [C_48,A_49] :
      ( r2_hidden(k4_tarski(C_48,'#skF_6'(A_49,k1_relat_1(A_49),C_48)),A_49)
      | ~ r2_hidden(C_48,k1_relat_1(A_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_93,plain,(
    ! [A_50,C_51] :
      ( ~ v1_xboole_0(A_50)
      | ~ r2_hidden(C_51,k1_relat_1(A_50)) ) ),
    inference(resolution,[status(thm)],[c_79,c_2])).

tff(c_113,plain,(
    ! [A_52] :
      ( ~ v1_xboole_0(A_52)
      | k1_relat_1(A_52) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_93])).

tff(c_119,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_113])).

tff(c_124,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_119])).

tff(c_125,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_27,plain,(
    ! [A_30] :
      ( v1_relat_1(A_30)
      | ~ v1_xboole_0(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_31,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_6,c_27])).

tff(c_126,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_148,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_7'(A_59,B_60),k1_relat_1(B_60))
      | ~ r2_hidden(A_59,k2_relat_1(B_60))
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_158,plain,(
    ! [B_61,A_62] :
      ( ~ v1_xboole_0(k1_relat_1(B_61))
      | ~ r2_hidden(A_62,k2_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(resolution,[status(thm)],[c_148,c_2])).

tff(c_169,plain,(
    ! [B_63] :
      ( ~ v1_xboole_0(k1_relat_1(B_63))
      | ~ v1_relat_1(B_63)
      | k2_relat_1(B_63) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_158])).

tff(c_172,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0)
    | k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_169])).

tff(c_174,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_6,c_172])).

tff(c_176,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_125,c_174])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n017.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:49:16 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.23  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_6 > #skF_1 > #skF_3 > #skF_7 > #skF_5 > #skF_4
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.95/1.23  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 1.95/1.23  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.95/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.95/1.23  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 1.95/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.95/1.23  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 1.95/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.95/1.23  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.95/1.23  
% 1.95/1.24  tff(f_65, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.95/1.24  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.95/1.24  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.95/1.24  tff(f_52, axiom, (![A, B]: ((B = k1_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(C, D), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_relat_1)).
% 1.95/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.95/1.24  tff(f_44, axiom, (![A]: (v1_xboole_0(A) => v1_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relat_1)).
% 1.95/1.24  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k2_relat_1(B)) & (![C]: ~r2_hidden(C, k1_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_relat_1)).
% 1.95/1.24  tff(c_26, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.95/1.24  tff(c_33, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_26])).
% 1.95/1.24  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.95/1.24  tff(c_8, plain, (![A_5]: (r2_hidden('#skF_2'(A_5), A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.95/1.24  tff(c_79, plain, (![C_48, A_49]: (r2_hidden(k4_tarski(C_48, '#skF_6'(A_49, k1_relat_1(A_49), C_48)), A_49) | ~r2_hidden(C_48, k1_relat_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.95/1.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.24  tff(c_93, plain, (![A_50, C_51]: (~v1_xboole_0(A_50) | ~r2_hidden(C_51, k1_relat_1(A_50)))), inference(resolution, [status(thm)], [c_79, c_2])).
% 1.95/1.24  tff(c_113, plain, (![A_52]: (~v1_xboole_0(A_52) | k1_relat_1(A_52)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_93])).
% 1.95/1.24  tff(c_119, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_6, c_113])).
% 1.95/1.24  tff(c_124, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_119])).
% 1.95/1.24  tff(c_125, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 1.95/1.24  tff(c_27, plain, (![A_30]: (v1_relat_1(A_30) | ~v1_xboole_0(A_30))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.95/1.24  tff(c_31, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_27])).
% 1.95/1.24  tff(c_126, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(splitRight, [status(thm)], [c_26])).
% 1.95/1.24  tff(c_148, plain, (![A_59, B_60]: (r2_hidden('#skF_7'(A_59, B_60), k1_relat_1(B_60)) | ~r2_hidden(A_59, k2_relat_1(B_60)) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.95/1.24  tff(c_158, plain, (![B_61, A_62]: (~v1_xboole_0(k1_relat_1(B_61)) | ~r2_hidden(A_62, k2_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(resolution, [status(thm)], [c_148, c_2])).
% 1.95/1.24  tff(c_169, plain, (![B_63]: (~v1_xboole_0(k1_relat_1(B_63)) | ~v1_relat_1(B_63) | k2_relat_1(B_63)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_158])).
% 1.95/1.24  tff(c_172, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_126, c_169])).
% 1.95/1.24  tff(c_174, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_31, c_6, c_172])).
% 1.95/1.24  tff(c_176, plain, $false, inference(negUnitSimplification, [status(thm)], [c_125, c_174])).
% 1.95/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  Inference rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Ref     : 0
% 1.95/1.24  #Sup     : 28
% 1.95/1.24  #Fact    : 0
% 1.95/1.24  #Define  : 0
% 1.95/1.24  #Split   : 1
% 1.95/1.24  #Chain   : 0
% 1.95/1.24  #Close   : 0
% 1.95/1.24  
% 1.95/1.24  Ordering : KBO
% 1.95/1.24  
% 1.95/1.24  Simplification rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Subsume      : 1
% 1.95/1.24  #Demod        : 3
% 1.95/1.24  #Tautology    : 7
% 1.95/1.24  #SimpNegUnit  : 2
% 1.95/1.24  #BackRed      : 0
% 1.95/1.24  
% 1.95/1.24  #Partial instantiations: 0
% 1.95/1.24  #Strategies tried      : 1
% 1.95/1.24  
% 1.95/1.24  Timing (in seconds)
% 1.95/1.24  ----------------------
% 1.95/1.24  Preprocessing        : 0.28
% 1.95/1.25  Parsing              : 0.16
% 1.95/1.25  CNF conversion       : 0.02
% 1.95/1.25  Main loop            : 0.15
% 1.95/1.25  Inferencing          : 0.07
% 1.95/1.25  Reduction            : 0.03
% 1.95/1.25  Demodulation         : 0.02
% 1.95/1.25  BG Simplification    : 0.01
% 1.95/1.25  Subsumption          : 0.03
% 1.95/1.25  Abstraction          : 0.01
% 1.95/1.25  MUC search           : 0.00
% 1.95/1.25  Cooper               : 0.00
% 1.95/1.25  Total                : 0.46
% 1.95/1.25  Index Insertion      : 0.00
% 1.95/1.25  Index Deletion       : 0.00
% 1.95/1.25  Index Matching       : 0.00
% 1.95/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
