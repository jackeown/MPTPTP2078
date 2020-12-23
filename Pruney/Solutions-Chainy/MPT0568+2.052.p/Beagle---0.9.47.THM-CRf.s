%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:27 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.37s
% Verified   : 
% Statistics : Number of formulae       :   38 (  46 expanded)
%              Number of leaves         :   24 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  49 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

tff(f_58,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

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

tff(f_62,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_30,plain,(
    k6_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_37,plain,(
    ! [A_51] : v1_relat_1(k6_relat_1(A_51)) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_39,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_37])).

tff(c_1604,plain,(
    ! [A_149,B_150,C_151] :
      ( r2_hidden(k4_tarski('#skF_2'(A_149,B_150,C_151),'#skF_3'(A_149,B_150,C_151)),A_149)
      | r2_hidden('#skF_4'(A_149,B_150,C_151),C_151)
      | k10_relat_1(A_149,B_150) = C_151
      | ~ v1_relat_1(A_149) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_48,plain,(
    ! [A_54,B_55,C_56] :
      ( ~ r1_xboole_0(A_54,B_55)
      | ~ r2_hidden(C_56,k3_xboole_0(A_54,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [A_6,C_56] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_56,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_48])).

tff(c_53,plain,(
    ! [C_56] : ~ r2_hidden(C_56,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_51])).

tff(c_1658,plain,(
    ! [B_150,C_151] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_150,C_151),C_151)
      | k10_relat_1(k1_xboole_0,B_150) = C_151
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_1604,c_53])).

tff(c_1680,plain,(
    ! [B_152,C_153] :
      ( r2_hidden('#skF_4'(k1_xboole_0,B_152,C_153),C_153)
      | k10_relat_1(k1_xboole_0,B_152) = C_153 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_1658])).

tff(c_1752,plain,(
    ! [B_152] : k10_relat_1(k1_xboole_0,B_152) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1680,c_53])).

tff(c_32,plain,(
    k10_relat_1(k1_xboole_0,'#skF_6') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1772,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1752,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:08:38 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.51  
% 3.15/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.51  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k3_xboole_0 > k10_relat_1 > #nlpp > k6_relat_1 > k1_xboole_0 > #skF_4 > #skF_6 > #skF_2 > #skF_5 > #skF_3 > #skF_1
% 3.15/1.51  
% 3.15/1.51  %Foreground sorts:
% 3.15/1.51  
% 3.15/1.51  
% 3.15/1.51  %Background operators:
% 3.15/1.51  
% 3.15/1.51  
% 3.15/1.51  %Foreground operators:
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.15/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.15/1.51  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.51  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 3.15/1.51  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 3.15/1.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.15/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.15/1.51  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.15/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.51  
% 3.37/1.52  tff(f_59, axiom, (k6_relat_1(k1_xboole_0) = k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_relat_1)).
% 3.37/1.52  tff(f_58, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.37/1.52  tff(f_56, axiom, (![A]: (v1_relat_1(A) => (![B, C]: ((C = k10_relat_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E]: (r2_hidden(k4_tarski(D, E), A) & r2_hidden(E, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d14_relat_1)).
% 3.37/1.52  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.37/1.52  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.37/1.52  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.37/1.52  tff(f_62, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 3.37/1.52  tff(c_30, plain, (k6_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.37/1.52  tff(c_37, plain, (![A_51]: (v1_relat_1(k6_relat_1(A_51)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.37/1.52  tff(c_39, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_30, c_37])).
% 3.37/1.52  tff(c_1604, plain, (![A_149, B_150, C_151]: (r2_hidden(k4_tarski('#skF_2'(A_149, B_150, C_151), '#skF_3'(A_149, B_150, C_151)), A_149) | r2_hidden('#skF_4'(A_149, B_150, C_151), C_151) | k10_relat_1(A_149, B_150)=C_151 | ~v1_relat_1(A_149))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.37/1.52  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.37/1.52  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.37/1.52  tff(c_48, plain, (![A_54, B_55, C_56]: (~r1_xboole_0(A_54, B_55) | ~r2_hidden(C_56, k3_xboole_0(A_54, B_55)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.37/1.52  tff(c_51, plain, (![A_6, C_56]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_48])).
% 3.37/1.52  tff(c_53, plain, (![C_56]: (~r2_hidden(C_56, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_51])).
% 3.37/1.52  tff(c_1658, plain, (![B_150, C_151]: (r2_hidden('#skF_4'(k1_xboole_0, B_150, C_151), C_151) | k10_relat_1(k1_xboole_0, B_150)=C_151 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_1604, c_53])).
% 3.37/1.52  tff(c_1680, plain, (![B_152, C_153]: (r2_hidden('#skF_4'(k1_xboole_0, B_152, C_153), C_153) | k10_relat_1(k1_xboole_0, B_152)=C_153)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_1658])).
% 3.37/1.52  tff(c_1752, plain, (![B_152]: (k10_relat_1(k1_xboole_0, B_152)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1680, c_53])).
% 3.37/1.52  tff(c_32, plain, (k10_relat_1(k1_xboole_0, '#skF_6')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.37/1.52  tff(c_1772, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1752, c_32])).
% 3.37/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.37/1.52  
% 3.37/1.52  Inference rules
% 3.37/1.52  ----------------------
% 3.37/1.52  #Ref     : 0
% 3.37/1.52  #Sup     : 350
% 3.37/1.52  #Fact    : 0
% 3.37/1.52  #Define  : 0
% 3.37/1.52  #Split   : 0
% 3.37/1.52  #Chain   : 0
% 3.37/1.52  #Close   : 0
% 3.37/1.52  
% 3.37/1.52  Ordering : KBO
% 3.37/1.52  
% 3.37/1.52  Simplification rules
% 3.37/1.52  ----------------------
% 3.37/1.52  #Subsume      : 204
% 3.37/1.52  #Demod        : 152
% 3.37/1.52  #Tautology    : 44
% 3.37/1.52  #SimpNegUnit  : 5
% 3.37/1.52  #BackRed      : 10
% 3.37/1.52  
% 3.37/1.52  #Partial instantiations: 0
% 3.37/1.52  #Strategies tried      : 1
% 3.37/1.52  
% 3.37/1.52  Timing (in seconds)
% 3.37/1.52  ----------------------
% 3.37/1.52  Preprocessing        : 0.28
% 3.37/1.52  Parsing              : 0.15
% 3.37/1.52  CNF conversion       : 0.03
% 3.37/1.52  Main loop            : 0.45
% 3.37/1.52  Inferencing          : 0.19
% 3.37/1.52  Reduction            : 0.12
% 3.37/1.52  Demodulation         : 0.08
% 3.37/1.52  BG Simplification    : 0.02
% 3.37/1.52  Subsumption          : 0.10
% 3.37/1.52  Abstraction          : 0.03
% 3.37/1.52  MUC search           : 0.00
% 3.37/1.52  Cooper               : 0.00
% 3.37/1.52  Total                : 0.76
% 3.37/1.52  Index Insertion      : 0.00
% 3.37/1.52  Index Deletion       : 0.00
% 3.37/1.52  Index Matching       : 0.00
% 3.37/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
