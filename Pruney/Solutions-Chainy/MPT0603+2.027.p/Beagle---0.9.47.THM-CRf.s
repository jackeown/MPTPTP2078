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
% DateTime   : Thu Dec  3 10:02:27 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   36 (  40 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   43 (  53 expanded)
%              Number of equality atoms :   13 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t207_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_26,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_33,plain,(
    ! [A_19] :
      ( k7_relat_1(A_19,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_37,plain,(
    k7_relat_1('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_26,c_33])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_52,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r1_xboole_0(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_6,B_7,C_10] :
      ( ~ r1_xboole_0(A_6,B_7)
      | ~ r2_hidden(C_10,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_64,plain,(
    ! [A_29,B_30,A_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | r1_xboole_0(A_31,k3_xboole_0(A_29,B_30)) ) ),
    inference(resolution,[status(thm)],[c_52,c_10])).

tff(c_14,plain,(
    ! [A_11] :
      ( ~ r1_xboole_0(A_11,A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_70,plain,(
    ! [A_32,B_33] :
      ( k3_xboole_0(A_32,B_33) = k1_xboole_0
      | ~ r1_xboole_0(A_32,B_33) ) ),
    inference(resolution,[status(thm)],[c_64,c_14])).

tff(c_82,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_70])).

tff(c_305,plain,(
    ! [C_50,A_51,B_52] :
      ( k7_relat_1(k7_relat_1(C_50,A_51),B_52) = k7_relat_1(C_50,k3_xboole_0(A_51,B_52))
      | ~ v1_relat_1(C_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_314,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_305,c_22])).

tff(c_327,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_37,c_82,c_314])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:19:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  
% 1.90/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.19  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.90/1.19  
% 1.90/1.19  %Foreground sorts:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Background operators:
% 1.90/1.19  
% 1.90/1.19  
% 1.90/1.19  %Foreground operators:
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.19  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.90/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.19  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.90/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.90/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.19  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.90/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.90/1.19  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.19  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.90/1.19  
% 1.90/1.20  tff(f_86, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t207_relat_1)).
% 1.90/1.20  tff(f_79, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.90/1.20  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.90/1.20  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.90/1.20  tff(f_69, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 1.90/1.20  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_relat_1)).
% 1.90/1.20  tff(c_26, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.90/1.20  tff(c_33, plain, (![A_19]: (k7_relat_1(A_19, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_79])).
% 1.90/1.20  tff(c_37, plain, (k7_relat_1('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_26, c_33])).
% 1.90/1.20  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.90/1.20  tff(c_52, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), B_26) | r1_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.90/1.20  tff(c_10, plain, (![A_6, B_7, C_10]: (~r1_xboole_0(A_6, B_7) | ~r2_hidden(C_10, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.90/1.20  tff(c_64, plain, (![A_29, B_30, A_31]: (~r1_xboole_0(A_29, B_30) | r1_xboole_0(A_31, k3_xboole_0(A_29, B_30)))), inference(resolution, [status(thm)], [c_52, c_10])).
% 1.90/1.20  tff(c_14, plain, (![A_11]: (~r1_xboole_0(A_11, A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.90/1.20  tff(c_70, plain, (![A_32, B_33]: (k3_xboole_0(A_32, B_33)=k1_xboole_0 | ~r1_xboole_0(A_32, B_33))), inference(resolution, [status(thm)], [c_64, c_14])).
% 1.90/1.20  tff(c_82, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_70])).
% 1.90/1.20  tff(c_305, plain, (![C_50, A_51, B_52]: (k7_relat_1(k7_relat_1(C_50, A_51), B_52)=k7_relat_1(C_50, k3_xboole_0(A_51, B_52)) | ~v1_relat_1(C_50))), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.90/1.20  tff(c_22, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 1.90/1.20  tff(c_314, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_305, c_22])).
% 1.90/1.20  tff(c_327, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_37, c_82, c_314])).
% 1.90/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.20  
% 1.90/1.20  Inference rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Ref     : 0
% 1.90/1.20  #Sup     : 68
% 1.90/1.20  #Fact    : 0
% 1.90/1.20  #Define  : 0
% 1.90/1.20  #Split   : 0
% 1.90/1.20  #Chain   : 0
% 1.90/1.20  #Close   : 0
% 1.90/1.20  
% 1.90/1.20  Ordering : KBO
% 1.90/1.20  
% 1.90/1.20  Simplification rules
% 1.90/1.20  ----------------------
% 1.90/1.20  #Subsume      : 10
% 1.90/1.20  #Demod        : 33
% 1.90/1.20  #Tautology    : 37
% 1.90/1.20  #SimpNegUnit  : 4
% 1.90/1.20  #BackRed      : 0
% 1.90/1.20  
% 1.90/1.20  #Partial instantiations: 0
% 1.90/1.20  #Strategies tried      : 1
% 1.90/1.20  
% 1.90/1.20  Timing (in seconds)
% 1.90/1.20  ----------------------
% 1.90/1.20  Preprocessing        : 0.27
% 1.90/1.20  Parsing              : 0.15
% 1.90/1.20  CNF conversion       : 0.02
% 1.90/1.20  Main loop            : 0.18
% 1.90/1.20  Inferencing          : 0.08
% 1.90/1.20  Reduction            : 0.05
% 1.90/1.20  Demodulation         : 0.04
% 1.90/1.20  BG Simplification    : 0.01
% 1.90/1.20  Subsumption          : 0.03
% 1.90/1.20  Abstraction          : 0.01
% 1.90/1.20  MUC search           : 0.00
% 1.90/1.20  Cooper               : 0.00
% 1.90/1.20  Total                : 0.47
% 1.90/1.20  Index Insertion      : 0.00
% 1.90/1.20  Index Deletion       : 0.00
% 1.90/1.20  Index Matching       : 0.00
% 1.90/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------
