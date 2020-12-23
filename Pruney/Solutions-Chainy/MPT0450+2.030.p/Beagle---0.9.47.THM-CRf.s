%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:40 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   43 (  59 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 (  99 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_70,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k3_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k3_relat_1(A),k3_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_62,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => r1_tarski(k3_relat_1(A),k3_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_38,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_30,plain,(
    ! [A_17,B_18] :
      ( v1_relat_1(k3_xboole_0(A_17,B_18))
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_36,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_49,plain,(
    ! [D_32,B_33,A_34] :
      ( r2_hidden(D_32,B_33)
      | ~ r2_hidden(D_32,k3_xboole_0(A_34,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_134,plain,(
    ! [A_55,B_56,B_57] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_55,B_56),B_57),B_56)
      | r1_tarski(k3_xboole_0(A_55,B_56),B_57) ) ),
    inference(resolution,[status(thm)],[c_6,c_49])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_152,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),B_56) ),
    inference(resolution,[status(thm)],[c_134,c_4])).

tff(c_32,plain,(
    ! [A_19,B_21] :
      ( r1_tarski(k3_relat_1(A_19),k3_relat_1(B_21))
      | ~ r1_tarski(A_19,B_21)
      | ~ v1_relat_1(B_21)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(k3_xboole_0(A_12,B_13),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_65,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(A_41,k3_xboole_0(B_42,C_43))
      | ~ r1_tarski(A_41,C_43)
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_5')),k3_xboole_0(k3_relat_1('#skF_4'),k3_relat_1('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_69,plain,
    ( ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_5')),k3_relat_1('#skF_5'))
    | ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_5')),k3_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_65,c_34])).

tff(c_174,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_5')),k3_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_69])).

tff(c_177,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_4')
    | ~ v1_relat_1('#skF_4')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_174])).

tff(c_180,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_26,c_177])).

tff(c_183,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_180])).

tff(c_187,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_183])).

tff(c_188,plain,(
    ~ r1_tarski(k3_relat_1(k3_xboole_0('#skF_4','#skF_5')),k3_relat_1('#skF_5')) ),
    inference(splitRight,[status(thm)],[c_69])).

tff(c_192,plain,
    ( ~ r1_tarski(k3_xboole_0('#skF_4','#skF_5'),'#skF_5')
    | ~ v1_relat_1('#skF_5')
    | ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_188])).

tff(c_195,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_152,c_192])).

tff(c_198,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_195])).

tff(c_202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:30:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.36  
% 2.19/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.37  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > #nlpp > k3_relat_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 2.19/1.37  
% 2.19/1.37  %Foreground sorts:
% 2.19/1.37  
% 2.19/1.37  
% 2.19/1.37  %Background operators:
% 2.19/1.37  
% 2.19/1.37  
% 2.19/1.37  %Foreground operators:
% 2.19/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.37  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.19/1.37  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.19/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.37  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.19/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.37  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.19/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.37  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.19/1.37  
% 2.19/1.38  tff(f_70, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k3_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_relat_1)).
% 2.19/1.38  tff(f_53, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_relat_1)).
% 2.19/1.38  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.19/1.38  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 2.19/1.38  tff(f_62, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => r1_tarski(k3_relat_1(A), k3_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_relat_1)).
% 2.19/1.38  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.19/1.38  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 2.19/1.38  tff(c_38, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.38  tff(c_30, plain, (![A_17, B_18]: (v1_relat_1(k3_xboole_0(A_17, B_18)) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.19/1.38  tff(c_36, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.38  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.38  tff(c_49, plain, (![D_32, B_33, A_34]: (r2_hidden(D_32, B_33) | ~r2_hidden(D_32, k3_xboole_0(A_34, B_33)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.38  tff(c_134, plain, (![A_55, B_56, B_57]: (r2_hidden('#skF_1'(k3_xboole_0(A_55, B_56), B_57), B_56) | r1_tarski(k3_xboole_0(A_55, B_56), B_57))), inference(resolution, [status(thm)], [c_6, c_49])).
% 2.19/1.38  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.19/1.38  tff(c_152, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), B_56))), inference(resolution, [status(thm)], [c_134, c_4])).
% 2.19/1.38  tff(c_32, plain, (![A_19, B_21]: (r1_tarski(k3_relat_1(A_19), k3_relat_1(B_21)) | ~r1_tarski(A_19, B_21) | ~v1_relat_1(B_21) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.38  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(k3_xboole_0(A_12, B_13), A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.38  tff(c_65, plain, (![A_41, B_42, C_43]: (r1_tarski(A_41, k3_xboole_0(B_42, C_43)) | ~r1_tarski(A_41, C_43) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.38  tff(c_34, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k3_xboole_0(k3_relat_1('#skF_4'), k3_relat_1('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.19/1.38  tff(c_69, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k3_relat_1('#skF_5')) | ~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k3_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_65, c_34])).
% 2.19/1.38  tff(c_174, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k3_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_69])).
% 2.19/1.38  tff(c_177, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_4') | ~v1_relat_1('#skF_4') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_174])).
% 2.19/1.38  tff(c_180, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_26, c_177])).
% 2.19/1.38  tff(c_183, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_180])).
% 2.19/1.38  tff(c_187, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_183])).
% 2.19/1.38  tff(c_188, plain, (~r1_tarski(k3_relat_1(k3_xboole_0('#skF_4', '#skF_5')), k3_relat_1('#skF_5'))), inference(splitRight, [status(thm)], [c_69])).
% 2.19/1.38  tff(c_192, plain, (~r1_tarski(k3_xboole_0('#skF_4', '#skF_5'), '#skF_5') | ~v1_relat_1('#skF_5') | ~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_32, c_188])).
% 2.19/1.38  tff(c_195, plain, (~v1_relat_1(k3_xboole_0('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_152, c_192])).
% 2.19/1.38  tff(c_198, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_195])).
% 2.19/1.38  tff(c_202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_198])).
% 2.19/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.38  
% 2.19/1.38  Inference rules
% 2.19/1.38  ----------------------
% 2.19/1.38  #Ref     : 0
% 2.19/1.38  #Sup     : 31
% 2.19/1.38  #Fact    : 0
% 2.19/1.38  #Define  : 0
% 2.19/1.38  #Split   : 1
% 2.19/1.38  #Chain   : 0
% 2.19/1.38  #Close   : 0
% 2.19/1.38  
% 2.19/1.38  Ordering : KBO
% 2.19/1.38  
% 2.19/1.38  Simplification rules
% 2.19/1.38  ----------------------
% 2.19/1.38  #Subsume      : 0
% 2.19/1.38  #Demod        : 7
% 2.19/1.38  #Tautology    : 4
% 2.19/1.38  #SimpNegUnit  : 0
% 2.19/1.38  #BackRed      : 0
% 2.19/1.38  
% 2.19/1.38  #Partial instantiations: 0
% 2.19/1.38  #Strategies tried      : 1
% 2.19/1.38  
% 2.19/1.38  Timing (in seconds)
% 2.19/1.38  ----------------------
% 2.19/1.39  Preprocessing        : 0.29
% 2.19/1.39  Parsing              : 0.14
% 2.19/1.39  CNF conversion       : 0.02
% 2.19/1.39  Main loop            : 0.24
% 2.19/1.39  Inferencing          : 0.07
% 2.19/1.39  Reduction            : 0.07
% 2.19/1.39  Demodulation         : 0.05
% 2.19/1.39  BG Simplification    : 0.01
% 2.19/1.39  Subsumption          : 0.06
% 2.19/1.39  Abstraction          : 0.01
% 2.19/1.39  MUC search           : 0.00
% 2.19/1.39  Cooper               : 0.00
% 2.19/1.39  Total                : 0.57
% 2.19/1.39  Index Insertion      : 0.00
% 2.19/1.39  Index Deletion       : 0.00
% 2.19/1.39  Index Matching       : 0.00
% 2.19/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
