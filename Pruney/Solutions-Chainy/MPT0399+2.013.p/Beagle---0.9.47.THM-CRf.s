%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:33 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  47 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :   11
%              Number of atoms          :   44 (  60 expanded)
%              Number of equality atoms :    7 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_68,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_124,plain,(
    ! [A_53,B_54,C_55] :
      ( r2_hidden('#skF_4'(A_53,B_54,C_55),B_54)
      | ~ r2_hidden(C_55,A_53)
      | ~ r1_setfam_1(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_12,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_39,plain,(
    ! [A_33,B_34,C_35] :
      ( ~ r1_xboole_0(A_33,B_34)
      | ~ r2_hidden(C_35,k3_xboole_0(A_33,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_59,plain,(
    ! [A_38,B_39] :
      ( ~ r1_xboole_0(A_38,B_39)
      | v1_xboole_0(k3_xboole_0(A_38,B_39)) ) ),
    inference(resolution,[status(thm)],[c_4,c_39])).

tff(c_6,plain,(
    ! [A_5] :
      ( k1_xboole_0 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_69,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = k1_xboole_0
      | ~ r1_xboole_0(A_42,B_43) ) ),
    inference(resolution,[status(thm)],[c_59,c_6])).

tff(c_74,plain,(
    ! [A_44] : k3_xboole_0(A_44,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_69])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_88,plain,(
    ! [A_44,C_10] :
      ( ~ r1_xboole_0(A_44,k1_xboole_0)
      | ~ r2_hidden(C_10,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_10])).

tff(c_97,plain,(
    ! [C_10] : ~ r2_hidden(C_10,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_88])).

tff(c_139,plain,(
    ! [C_56,A_57] :
      ( ~ r2_hidden(C_56,A_57)
      | ~ r1_setfam_1(A_57,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_124,c_97])).

tff(c_156,plain,(
    ! [A_58] :
      ( ~ r1_setfam_1(A_58,k1_xboole_0)
      | v1_xboole_0(A_58) ) ),
    inference(resolution,[status(thm)],[c_4,c_139])).

tff(c_176,plain,(
    v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_24,c_156])).

tff(c_179,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_176,c_6])).

tff(c_183,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_179])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:22:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  
% 1.82/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.16  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > v1_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_3 > #skF_5 > #skF_2
% 1.82/1.16  
% 1.82/1.16  %Foreground sorts:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Background operators:
% 1.82/1.16  
% 1.82/1.16  
% 1.82/1.16  %Foreground operators:
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.16  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 1.82/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.16  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.82/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.82/1.16  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.82/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.82/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.82/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.82/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.82/1.16  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.16  
% 1.82/1.17  tff(f_68, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_setfam_1)).
% 1.82/1.17  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.82/1.17  tff(f_63, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_setfam_1)).
% 1.82/1.17  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.82/1.17  tff(f_49, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.82/1.17  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.82/1.17  tff(c_22, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.17  tff(c_24, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.82/1.17  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.17  tff(c_124, plain, (![A_53, B_54, C_55]: (r2_hidden('#skF_4'(A_53, B_54, C_55), B_54) | ~r2_hidden(C_55, A_53) | ~r1_setfam_1(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.82/1.17  tff(c_12, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.82/1.17  tff(c_39, plain, (![A_33, B_34, C_35]: (~r1_xboole_0(A_33, B_34) | ~r2_hidden(C_35, k3_xboole_0(A_33, B_34)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.17  tff(c_59, plain, (![A_38, B_39]: (~r1_xboole_0(A_38, B_39) | v1_xboole_0(k3_xboole_0(A_38, B_39)))), inference(resolution, [status(thm)], [c_4, c_39])).
% 1.82/1.17  tff(c_6, plain, (![A_5]: (k1_xboole_0=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.82/1.17  tff(c_69, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=k1_xboole_0 | ~r1_xboole_0(A_42, B_43))), inference(resolution, [status(thm)], [c_59, c_6])).
% 1.82/1.17  tff(c_74, plain, (![A_44]: (k3_xboole_0(A_44, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_12, c_69])).
% 1.82/1.17  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.82/1.17  tff(c_88, plain, (![A_44, C_10]: (~r1_xboole_0(A_44, k1_xboole_0) | ~r2_hidden(C_10, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_74, c_10])).
% 1.82/1.17  tff(c_97, plain, (![C_10]: (~r2_hidden(C_10, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_88])).
% 1.82/1.17  tff(c_139, plain, (![C_56, A_57]: (~r2_hidden(C_56, A_57) | ~r1_setfam_1(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_124, c_97])).
% 1.82/1.17  tff(c_156, plain, (![A_58]: (~r1_setfam_1(A_58, k1_xboole_0) | v1_xboole_0(A_58))), inference(resolution, [status(thm)], [c_4, c_139])).
% 1.82/1.17  tff(c_176, plain, (v1_xboole_0('#skF_5')), inference(resolution, [status(thm)], [c_24, c_156])).
% 1.82/1.17  tff(c_179, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_176, c_6])).
% 1.82/1.17  tff(c_183, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_179])).
% 1.82/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.17  
% 1.82/1.17  Inference rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Ref     : 0
% 1.82/1.17  #Sup     : 31
% 1.82/1.17  #Fact    : 0
% 1.82/1.17  #Define  : 0
% 1.82/1.17  #Split   : 0
% 1.82/1.17  #Chain   : 0
% 1.82/1.17  #Close   : 0
% 1.82/1.17  
% 1.82/1.17  Ordering : KBO
% 1.82/1.17  
% 1.82/1.17  Simplification rules
% 1.82/1.17  ----------------------
% 1.82/1.17  #Subsume      : 1
% 1.82/1.17  #Demod        : 8
% 1.82/1.17  #Tautology    : 12
% 1.82/1.17  #SimpNegUnit  : 1
% 1.82/1.17  #BackRed      : 0
% 1.82/1.17  
% 1.82/1.17  #Partial instantiations: 0
% 1.82/1.17  #Strategies tried      : 1
% 1.82/1.17  
% 1.82/1.17  Timing (in seconds)
% 1.82/1.17  ----------------------
% 1.82/1.17  Preprocessing        : 0.28
% 1.82/1.17  Parsing              : 0.15
% 1.82/1.17  CNF conversion       : 0.02
% 1.82/1.17  Main loop            : 0.14
% 1.82/1.18  Inferencing          : 0.06
% 1.82/1.18  Reduction            : 0.04
% 1.82/1.18  Demodulation         : 0.03
% 1.82/1.18  BG Simplification    : 0.02
% 1.82/1.18  Subsumption          : 0.02
% 1.82/1.18  Abstraction          : 0.01
% 1.82/1.18  MUC search           : 0.00
% 1.82/1.18  Cooper               : 0.00
% 1.82/1.18  Total                : 0.44
% 1.82/1.18  Index Insertion      : 0.00
% 1.82/1.18  Index Deletion       : 0.00
% 1.82/1.18  Index Matching       : 0.00
% 1.82/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------
