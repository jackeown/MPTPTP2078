%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:18 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   35 (  36 expanded)
%              Number of leaves         :   22 (  23 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  38 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k10_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_38,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_45,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_36,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_26,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_28,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden('#skF_2'(A_39,B_40,C_41),B_40)
      | ~ r2_hidden(A_39,k10_relat_1(C_41,B_40))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(k1_xboole_0,A_7) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_60,plain,(
    ! [B_25,A_26] :
      ( ~ r2_hidden(B_25,A_26)
      | k4_xboole_0(A_26,k1_tarski(B_25)) != A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_65,plain,(
    ! [B_25] : ~ r2_hidden(B_25,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_60])).

tff(c_140,plain,(
    ! [A_42,C_43] :
      ( ~ r2_hidden(A_42,k10_relat_1(C_43,k1_xboole_0))
      | ~ v1_relat_1(C_43) ) ),
    inference(resolution,[status(thm)],[c_131,c_65])).

tff(c_156,plain,(
    ! [C_44,B_45] :
      ( ~ v1_relat_1(C_44)
      | r1_tarski(k10_relat_1(C_44,k1_xboole_0),B_45) ) ),
    inference(resolution,[status(thm)],[c_6,c_140])).

tff(c_8,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_166,plain,(
    ! [C_46] :
      ( k10_relat_1(C_46,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(C_46) ) ),
    inference(resolution,[status(thm)],[c_156,c_8])).

tff(c_169,plain,(
    k10_relat_1('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_166])).

tff(c_173,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_169])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:17:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.10  
% 1.76/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.10  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_xboole_0 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.76/1.10  
% 1.76/1.10  %Foreground sorts:
% 1.76/1.10  
% 1.76/1.10  
% 1.76/1.10  %Background operators:
% 1.76/1.10  
% 1.76/1.10  
% 1.76/1.10  %Foreground operators:
% 1.76/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.76/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.76/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.10  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.76/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.10  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 1.76/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.76/1.10  
% 1.76/1.11  tff(f_61, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k10_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t171_relat_1)).
% 1.76/1.11  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.76/1.11  tff(f_56, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 1.76/1.11  tff(f_38, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.76/1.11  tff(f_45, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.76/1.11  tff(f_36, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.76/1.11  tff(c_26, plain, (k10_relat_1('#skF_3', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.76/1.11  tff(c_28, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.76/1.11  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.76/1.11  tff(c_131, plain, (![A_39, B_40, C_41]: (r2_hidden('#skF_2'(A_39, B_40, C_41), B_40) | ~r2_hidden(A_39, k10_relat_1(C_41, B_40)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.76/1.11  tff(c_10, plain, (![A_7]: (k4_xboole_0(k1_xboole_0, A_7)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.11  tff(c_60, plain, (![B_25, A_26]: (~r2_hidden(B_25, A_26) | k4_xboole_0(A_26, k1_tarski(B_25))!=A_26)), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.76/1.11  tff(c_65, plain, (![B_25]: (~r2_hidden(B_25, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_60])).
% 1.76/1.11  tff(c_140, plain, (![A_42, C_43]: (~r2_hidden(A_42, k10_relat_1(C_43, k1_xboole_0)) | ~v1_relat_1(C_43))), inference(resolution, [status(thm)], [c_131, c_65])).
% 1.76/1.11  tff(c_156, plain, (![C_44, B_45]: (~v1_relat_1(C_44) | r1_tarski(k10_relat_1(C_44, k1_xboole_0), B_45))), inference(resolution, [status(thm)], [c_6, c_140])).
% 1.76/1.11  tff(c_8, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.76/1.11  tff(c_166, plain, (![C_46]: (k10_relat_1(C_46, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(C_46))), inference(resolution, [status(thm)], [c_156, c_8])).
% 1.76/1.11  tff(c_169, plain, (k10_relat_1('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_166])).
% 1.76/1.11  tff(c_173, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_169])).
% 1.76/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.11  
% 1.76/1.11  Inference rules
% 1.76/1.11  ----------------------
% 1.76/1.11  #Ref     : 0
% 1.76/1.11  #Sup     : 28
% 1.76/1.11  #Fact    : 0
% 1.76/1.11  #Define  : 0
% 1.76/1.11  #Split   : 0
% 1.76/1.11  #Chain   : 0
% 1.76/1.11  #Close   : 0
% 1.76/1.11  
% 1.76/1.11  Ordering : KBO
% 1.76/1.11  
% 1.76/1.11  Simplification rules
% 1.76/1.11  ----------------------
% 1.76/1.11  #Subsume      : 1
% 1.76/1.11  #Demod        : 2
% 1.76/1.11  #Tautology    : 14
% 1.76/1.11  #SimpNegUnit  : 1
% 1.76/1.11  #BackRed      : 0
% 1.76/1.11  
% 1.76/1.11  #Partial instantiations: 0
% 1.76/1.11  #Strategies tried      : 1
% 1.76/1.11  
% 1.76/1.11  Timing (in seconds)
% 1.76/1.11  ----------------------
% 1.76/1.11  Preprocessing        : 0.29
% 1.76/1.11  Parsing              : 0.16
% 1.76/1.11  CNF conversion       : 0.02
% 1.76/1.11  Main loop            : 0.12
% 1.76/1.11  Inferencing          : 0.05
% 1.76/1.11  Reduction            : 0.03
% 1.76/1.11  Demodulation         : 0.02
% 1.76/1.11  BG Simplification    : 0.01
% 1.76/1.11  Subsumption          : 0.02
% 1.76/1.11  Abstraction          : 0.01
% 1.76/1.11  MUC search           : 0.00
% 1.76/1.11  Cooper               : 0.00
% 1.76/1.11  Total                : 0.43
% 1.76/1.11  Index Insertion      : 0.00
% 1.76/1.11  Index Deletion       : 0.00
% 1.76/1.11  Index Matching       : 0.00
% 1.76/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
