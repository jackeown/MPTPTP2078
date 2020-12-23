%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:34 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  46 expanded)
%              Number of equality atoms :    6 (   7 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_72,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_30,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_12,B_13,C_22] :
      ( r2_hidden('#skF_4'(A_12,B_13,C_22),B_13)
      | ~ r2_hidden(C_22,A_12)
      | ~ r1_setfam_1(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_142,plain,(
    ! [A_61,B_62,C_63] :
      ( r2_hidden('#skF_4'(A_61,B_62,C_63),B_62)
      | ~ r2_hidden(C_63,A_61)
      | ~ r1_setfam_1(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49,plain,(
    ! [A_39,B_40,C_41] :
      ( ~ r1_xboole_0(A_39,B_40)
      | ~ r2_hidden(C_41,B_40)
      | ~ r2_hidden(C_41,A_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,(
    ! [C_41,A_8] :
      ( ~ r2_hidden(C_41,k1_xboole_0)
      | ~ r2_hidden(C_41,A_8) ) ),
    inference(resolution,[status(thm)],[c_10,c_49])).

tff(c_155,plain,(
    ! [A_68,C_69,A_70] :
      ( ~ r2_hidden('#skF_4'(A_68,k1_xboole_0,C_69),A_70)
      | ~ r2_hidden(C_69,A_68)
      | ~ r1_setfam_1(A_68,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_142,c_52])).

tff(c_166,plain,(
    ! [C_71,A_72] :
      ( ~ r2_hidden(C_71,A_72)
      | ~ r1_setfam_1(A_72,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_155])).

tff(c_191,plain,(
    ! [A_73] :
      ( ~ r1_setfam_1(A_73,k1_xboole_0)
      | k1_xboole_0 = A_73 ) ),
    inference(resolution,[status(thm)],[c_8,c_166])).

tff(c_198,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_30,c_191])).

tff(c_204,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_198])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:49:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.37  
% 2.13/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > m1_subset_1 > v1_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 2.13/1.38  
% 2.13/1.38  %Foreground sorts:
% 2.13/1.38  
% 2.13/1.38  
% 2.13/1.38  %Background operators:
% 2.13/1.38  
% 2.13/1.38  
% 2.13/1.38  %Foreground operators:
% 2.13/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.38  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.13/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.13/1.38  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.13/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.13/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.38  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.13/1.38  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.38  
% 2.13/1.38  tff(f_83, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.13/1.38  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.13/1.38  tff(f_72, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.13/1.38  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.13/1.38  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.13/1.38  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.38  tff(c_30, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.13/1.38  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.13/1.38  tff(c_20, plain, (![A_12, B_13, C_22]: (r2_hidden('#skF_4'(A_12, B_13, C_22), B_13) | ~r2_hidden(C_22, A_12) | ~r1_setfam_1(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.13/1.38  tff(c_142, plain, (![A_61, B_62, C_63]: (r2_hidden('#skF_4'(A_61, B_62, C_63), B_62) | ~r2_hidden(C_63, A_61) | ~r1_setfam_1(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.13/1.38  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.38  tff(c_49, plain, (![A_39, B_40, C_41]: (~r1_xboole_0(A_39, B_40) | ~r2_hidden(C_41, B_40) | ~r2_hidden(C_41, A_39))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.13/1.38  tff(c_52, plain, (![C_41, A_8]: (~r2_hidden(C_41, k1_xboole_0) | ~r2_hidden(C_41, A_8))), inference(resolution, [status(thm)], [c_10, c_49])).
% 2.13/1.38  tff(c_155, plain, (![A_68, C_69, A_70]: (~r2_hidden('#skF_4'(A_68, k1_xboole_0, C_69), A_70) | ~r2_hidden(C_69, A_68) | ~r1_setfam_1(A_68, k1_xboole_0))), inference(resolution, [status(thm)], [c_142, c_52])).
% 2.13/1.38  tff(c_166, plain, (![C_71, A_72]: (~r2_hidden(C_71, A_72) | ~r1_setfam_1(A_72, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_155])).
% 2.13/1.38  tff(c_191, plain, (![A_73]: (~r1_setfam_1(A_73, k1_xboole_0) | k1_xboole_0=A_73)), inference(resolution, [status(thm)], [c_8, c_166])).
% 2.13/1.38  tff(c_198, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_30, c_191])).
% 2.13/1.38  tff(c_204, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_198])).
% 2.13/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.38  
% 2.13/1.38  Inference rules
% 2.13/1.38  ----------------------
% 2.13/1.38  #Ref     : 0
% 2.13/1.38  #Sup     : 32
% 2.13/1.38  #Fact    : 0
% 2.13/1.38  #Define  : 0
% 2.13/1.38  #Split   : 1
% 2.13/1.38  #Chain   : 0
% 2.13/1.38  #Close   : 0
% 2.13/1.38  
% 2.13/1.38  Ordering : KBO
% 2.13/1.38  
% 2.13/1.38  Simplification rules
% 2.13/1.38  ----------------------
% 2.13/1.38  #Subsume      : 3
% 2.13/1.38  #Demod        : 7
% 2.13/1.39  #Tautology    : 10
% 2.13/1.39  #SimpNegUnit  : 1
% 2.13/1.39  #BackRed      : 0
% 2.13/1.39  
% 2.13/1.39  #Partial instantiations: 0
% 2.13/1.39  #Strategies tried      : 1
% 2.13/1.39  
% 2.13/1.39  Timing (in seconds)
% 2.13/1.39  ----------------------
% 2.13/1.39  Preprocessing        : 0.40
% 2.13/1.39  Parsing              : 0.24
% 2.13/1.39  CNF conversion       : 0.02
% 2.13/1.39  Main loop            : 0.16
% 2.13/1.39  Inferencing          : 0.07
% 2.13/1.39  Reduction            : 0.04
% 2.13/1.39  Demodulation         : 0.03
% 2.13/1.39  BG Simplification    : 0.01
% 2.13/1.39  Subsumption          : 0.03
% 2.13/1.39  Abstraction          : 0.01
% 2.13/1.39  MUC search           : 0.00
% 2.13/1.39  Cooper               : 0.00
% 2.13/1.39  Total                : 0.58
% 2.13/1.39  Index Insertion      : 0.00
% 2.13/1.39  Index Deletion       : 0.00
% 2.13/1.39  Index Matching       : 0.00
% 2.13/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
