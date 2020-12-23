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
% DateTime   : Thu Dec  3 09:59:00 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   44 (  55 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  64 expanded)
%              Number of equality atoms :   16 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_65,negated_conjecture,(
    ~ ( k1_relat_1(k1_xboole_0) = k1_xboole_0
      & k2_relat_1(k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ~ ( r2_hidden(A,k1_relat_1(B))
          & ! [C] : ~ r2_hidden(C,k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_relat_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(c_28,plain,
    ( k2_relat_1(k1_xboole_0) != k1_xboole_0
    | k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_64,plain,(
    k1_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [B_33] : k2_zfmisc_1(k1_xboole_0,B_33) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_26,B_27] : v1_relat_1(k2_zfmisc_1(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_34,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_24])).

tff(c_26,plain,(
    ! [A_28,B_29] :
      ( r2_hidden('#skF_6'(A_28,B_29),k2_relat_1(B_29))
      | ~ r2_hidden(A_28,k1_relat_1(B_29))
      | ~ v1_relat_1(B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_87,plain,(
    ! [A_48,C_49] :
      ( r2_hidden(k4_tarski('#skF_5'(A_48,k2_relat_1(A_48),C_49),C_49),A_48)
      | ~ r2_hidden(C_49,k2_relat_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_35,B_36] : ~ r2_hidden(A_35,k2_zfmisc_1(A_35,B_36)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_60,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_57])).

tff(c_98,plain,(
    ! [C_53] : ~ r2_hidden(C_53,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_87,c_60])).

tff(c_106,plain,(
    ! [A_28] :
      ( ~ r2_hidden(A_28,k1_relat_1(k1_xboole_0))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_26,c_98])).

tff(c_132,plain,(
    ! [A_54] : ~ r2_hidden(A_54,k1_relat_1(k1_xboole_0)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_140,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_132])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_140])).

tff(c_146,plain,(
    k2_relat_1(k1_xboole_0) != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_174,plain,(
    ! [A_66,C_67] :
      ( r2_hidden(k4_tarski('#skF_5'(A_66,k2_relat_1(A_66),C_67),C_67),A_66)
      | ~ r2_hidden(C_67,k2_relat_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_185,plain,(
    ! [C_71] : ~ r2_hidden(C_71,k2_relat_1(k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_174,c_60])).

tff(c_197,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_185])).

tff(c_205,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_146,c_197])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n009.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:19:41 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.21  
% 1.69/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.21  %$ r2_hidden > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_5 > #skF_2 > #skF_4
% 1.69/1.21  
% 1.69/1.21  %Foreground sorts:
% 1.69/1.21  
% 1.69/1.21  
% 1.69/1.21  %Background operators:
% 1.69/1.21  
% 1.69/1.21  
% 1.69/1.21  %Foreground operators:
% 1.69/1.21  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 1.69/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.69/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.69/1.21  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.69/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.69/1.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.69/1.21  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 1.69/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.69/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.69/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.69/1.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.69/1.21  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.69/1.21  
% 1.69/1.22  tff(f_65, negated_conjecture, ~((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.69/1.22  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.69/1.22  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.69/1.22  tff(f_52, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.69/1.22  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ~(r2_hidden(A, k1_relat_1(B)) & (![C]: ~r2_hidden(C, k2_relat_1(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_relat_1)).
% 1.69/1.22  tff(f_50, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 1.69/1.22  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.69/1.22  tff(c_28, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0 | k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.69/1.22  tff(c_64, plain, (k1_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 1.69/1.22  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.22  tff(c_30, plain, (![B_33]: (k2_zfmisc_1(k1_xboole_0, B_33)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.69/1.22  tff(c_24, plain, (![A_26, B_27]: (v1_relat_1(k2_zfmisc_1(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.69/1.22  tff(c_34, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_24])).
% 1.69/1.22  tff(c_26, plain, (![A_28, B_29]: (r2_hidden('#skF_6'(A_28, B_29), k2_relat_1(B_29)) | ~r2_hidden(A_28, k1_relat_1(B_29)) | ~v1_relat_1(B_29))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.91/1.22  tff(c_87, plain, (![A_48, C_49]: (r2_hidden(k4_tarski('#skF_5'(A_48, k2_relat_1(A_48), C_49), C_49), A_48) | ~r2_hidden(C_49, k2_relat_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.22  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.22  tff(c_57, plain, (![A_35, B_36]: (~r2_hidden(A_35, k2_zfmisc_1(A_35, B_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.22  tff(c_60, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_57])).
% 1.91/1.22  tff(c_98, plain, (![C_53]: (~r2_hidden(C_53, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_87, c_60])).
% 1.91/1.22  tff(c_106, plain, (![A_28]: (~r2_hidden(A_28, k1_relat_1(k1_xboole_0)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_26, c_98])).
% 1.91/1.22  tff(c_132, plain, (![A_54]: (~r2_hidden(A_54, k1_relat_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_106])).
% 1.91/1.22  tff(c_140, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_132])).
% 1.91/1.22  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_140])).
% 1.91/1.22  tff(c_146, plain, (k2_relat_1(k1_xboole_0)!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 1.91/1.22  tff(c_174, plain, (![A_66, C_67]: (r2_hidden(k4_tarski('#skF_5'(A_66, k2_relat_1(A_66), C_67), C_67), A_66) | ~r2_hidden(C_67, k2_relat_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.22  tff(c_185, plain, (![C_71]: (~r2_hidden(C_71, k2_relat_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_174, c_60])).
% 1.91/1.22  tff(c_197, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_185])).
% 1.91/1.22  tff(c_205, plain, $false, inference(negUnitSimplification, [status(thm)], [c_146, c_197])).
% 1.91/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.22  
% 1.91/1.22  Inference rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Ref     : 0
% 1.91/1.22  #Sup     : 34
% 1.91/1.22  #Fact    : 0
% 1.91/1.22  #Define  : 0
% 1.91/1.22  #Split   : 1
% 1.91/1.22  #Chain   : 0
% 1.91/1.22  #Close   : 0
% 1.91/1.22  
% 1.91/1.22  Ordering : KBO
% 1.91/1.22  
% 1.91/1.22  Simplification rules
% 1.91/1.22  ----------------------
% 1.91/1.22  #Subsume      : 5
% 1.91/1.22  #Demod        : 7
% 1.91/1.22  #Tautology    : 19
% 1.91/1.22  #SimpNegUnit  : 4
% 1.91/1.22  #BackRed      : 1
% 1.91/1.22  
% 1.91/1.22  #Partial instantiations: 0
% 1.91/1.22  #Strategies tried      : 1
% 1.91/1.22  
% 1.91/1.22  Timing (in seconds)
% 1.91/1.22  ----------------------
% 1.91/1.23  Preprocessing        : 0.28
% 1.91/1.23  Parsing              : 0.16
% 1.91/1.23  CNF conversion       : 0.02
% 1.91/1.23  Main loop            : 0.15
% 1.91/1.23  Inferencing          : 0.06
% 1.91/1.23  Reduction            : 0.04
% 1.91/1.23  Demodulation         : 0.03
% 1.91/1.23  BG Simplification    : 0.01
% 1.91/1.23  Subsumption          : 0.02
% 1.91/1.23  Abstraction          : 0.01
% 1.91/1.23  MUC search           : 0.00
% 1.91/1.23  Cooper               : 0.00
% 1.91/1.23  Total                : 0.45
% 1.91/1.23  Index Insertion      : 0.00
% 1.91/1.23  Index Deletion       : 0.00
% 1.91/1.23  Index Matching       : 0.00
% 1.91/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
