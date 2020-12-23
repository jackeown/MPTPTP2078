%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:06:34 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   33 (  35 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  46 expanded)
%              Number of equality atoms :    7 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

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

tff(k1_wellord1,type,(
    k1_wellord1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( r2_hidden(A,k3_relat_1(B))
          | k1_wellord1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_wellord1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B,C] :
          ( C = k1_wellord1(A,B)
        <=> ! [D] :
              ( r2_hidden(D,C)
            <=> ( D != B
                & r2_hidden(k4_tarski(D,B),A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(k4_tarski(A,B),C)
       => ( r2_hidden(A,k3_relat_1(C))
          & r2_hidden(B,k3_relat_1(C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_30,plain,(
    k1_wellord1('#skF_5','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [D_33,B_34,A_35] :
      ( r2_hidden(k4_tarski(D_33,B_34),A_35)
      | ~ r2_hidden(D_33,k1_wellord1(A_35,B_34))
      | ~ v1_relat_1(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [B_7,C_8,A_6] :
      ( r2_hidden(B_7,k3_relat_1(C_8))
      | ~ r2_hidden(k4_tarski(A_6,B_7),C_8)
      | ~ v1_relat_1(C_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_83,plain,(
    ! [B_43,A_44,D_45] :
      ( r2_hidden(B_43,k3_relat_1(A_44))
      | ~ r2_hidden(D_45,k1_wellord1(A_44,B_43))
      | ~ v1_relat_1(A_44) ) ),
    inference(resolution,[status(thm)],[c_45,c_8])).

tff(c_92,plain,(
    ! [B_46,A_47] :
      ( r2_hidden(B_46,k3_relat_1(A_47))
      | ~ v1_relat_1(A_47)
      | v1_xboole_0(k1_wellord1(A_47,B_46)) ) ),
    inference(resolution,[status(thm)],[c_4,c_83])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_4',k3_relat_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_106,plain,
    ( ~ v1_relat_1('#skF_5')
    | v1_xboole_0(k1_wellord1('#skF_5','#skF_4')) ),
    inference(resolution,[status(thm)],[c_92,c_32])).

tff(c_112,plain,(
    v1_xboole_0(k1_wellord1('#skF_5','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_106])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_127,plain,(
    k1_wellord1('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_112,c_6])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:55:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.67  
% 2.11/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.67  %$ r2_hidden > v1_xboole_0 > v1_relat_1 > k4_tarski > k1_wellord1 > #nlpp > k3_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.11/1.67  
% 2.11/1.67  %Foreground sorts:
% 2.11/1.67  
% 2.11/1.67  
% 2.11/1.67  %Background operators:
% 2.11/1.67  
% 2.11/1.67  
% 2.11/1.67  %Foreground operators:
% 2.11/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.67  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.11/1.67  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.11/1.67  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.11/1.67  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 2.11/1.67  tff('#skF_5', type, '#skF_5': $i).
% 2.11/1.67  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.67  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.11/1.67  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.67  tff(k1_wellord1, type, k1_wellord1: ($i * $i) > $i).
% 2.11/1.67  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.11/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.67  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.11/1.67  
% 2.11/1.69  tff(f_63, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => (r2_hidden(A, k3_relat_1(B)) | (k1_wellord1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_wellord1)).
% 2.11/1.69  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.11/1.69  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k1_wellord1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (~(D = B) & r2_hidden(k4_tarski(D, B), A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_wellord1)).
% 2.11/1.69  tff(f_43, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(k4_tarski(A, B), C) => (r2_hidden(A, k3_relat_1(C)) & r2_hidden(B, k3_relat_1(C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relat_1)).
% 2.11/1.69  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.11/1.69  tff(c_30, plain, (k1_wellord1('#skF_5', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.69  tff(c_34, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.69  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.11/1.69  tff(c_45, plain, (![D_33, B_34, A_35]: (r2_hidden(k4_tarski(D_33, B_34), A_35) | ~r2_hidden(D_33, k1_wellord1(A_35, B_34)) | ~v1_relat_1(A_35))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.11/1.69  tff(c_8, plain, (![B_7, C_8, A_6]: (r2_hidden(B_7, k3_relat_1(C_8)) | ~r2_hidden(k4_tarski(A_6, B_7), C_8) | ~v1_relat_1(C_8))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.69  tff(c_83, plain, (![B_43, A_44, D_45]: (r2_hidden(B_43, k3_relat_1(A_44)) | ~r2_hidden(D_45, k1_wellord1(A_44, B_43)) | ~v1_relat_1(A_44))), inference(resolution, [status(thm)], [c_45, c_8])).
% 2.11/1.69  tff(c_92, plain, (![B_46, A_47]: (r2_hidden(B_46, k3_relat_1(A_47)) | ~v1_relat_1(A_47) | v1_xboole_0(k1_wellord1(A_47, B_46)))), inference(resolution, [status(thm)], [c_4, c_83])).
% 2.11/1.69  tff(c_32, plain, (~r2_hidden('#skF_4', k3_relat_1('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.11/1.69  tff(c_106, plain, (~v1_relat_1('#skF_5') | v1_xboole_0(k1_wellord1('#skF_5', '#skF_4'))), inference(resolution, [status(thm)], [c_92, c_32])).
% 2.11/1.69  tff(c_112, plain, (v1_xboole_0(k1_wellord1('#skF_5', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_106])).
% 2.11/1.69  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.11/1.69  tff(c_127, plain, (k1_wellord1('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_112, c_6])).
% 2.11/1.69  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_127])).
% 2.11/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.69  
% 2.11/1.69  Inference rules
% 2.11/1.69  ----------------------
% 2.11/1.69  #Ref     : 0
% 2.11/1.69  #Sup     : 19
% 2.11/1.69  #Fact    : 0
% 2.11/1.69  #Define  : 0
% 2.11/1.69  #Split   : 0
% 2.11/1.69  #Chain   : 0
% 2.11/1.69  #Close   : 0
% 2.11/1.69  
% 2.11/1.69  Ordering : KBO
% 2.11/1.69  
% 2.11/1.69  Simplification rules
% 2.11/1.69  ----------------------
% 2.11/1.69  #Subsume      : 0
% 2.11/1.69  #Demod        : 1
% 2.11/1.69  #Tautology    : 2
% 2.11/1.69  #SimpNegUnit  : 1
% 2.11/1.69  #BackRed      : 0
% 2.11/1.69  
% 2.11/1.69  #Partial instantiations: 0
% 2.11/1.69  #Strategies tried      : 1
% 2.11/1.69  
% 2.11/1.69  Timing (in seconds)
% 2.11/1.69  ----------------------
% 2.11/1.69  Preprocessing        : 0.50
% 2.11/1.69  Parsing              : 0.28
% 2.11/1.69  CNF conversion       : 0.04
% 2.11/1.69  Main loop            : 0.25
% 2.26/1.69  Inferencing          : 0.09
% 2.26/1.69  Reduction            : 0.06
% 2.26/1.69  Demodulation         : 0.04
% 2.26/1.69  BG Simplification    : 0.03
% 2.26/1.69  Subsumption          : 0.07
% 2.26/1.69  Abstraction          : 0.01
% 2.26/1.69  MUC search           : 0.00
% 2.26/1.69  Cooper               : 0.00
% 2.26/1.69  Total                : 0.79
% 2.26/1.70  Index Insertion      : 0.00
% 2.26/1.70  Index Deletion       : 0.00
% 2.26/1.70  Index Matching       : 0.00
% 2.26/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
