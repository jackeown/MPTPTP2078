%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:56 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   39 (  50 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    6
%              Number of atoms          :   45 (  75 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ! [B_26,A_27] :
      ( r1_xboole_0(k1_relat_1(B_26),A_27)
      | k9_relat_1(B_26,A_27) != k1_xboole_0
      | ~ v1_relat_1(B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_71,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,k1_relat_1(B_31))
      | k9_relat_1(B_31,A_30) != k1_xboole_0
      | ~ v1_relat_1(B_31) ) ),
    inference(resolution,[status(thm)],[c_58,c_2])).

tff(c_18,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_29,plain,(
    ! [A_17,B_18] :
      ( k3_xboole_0(A_17,B_18) = A_17
      | ~ r1_tarski(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_33,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_18,c_29])).

tff(c_38,plain,(
    ! [A_19,B_20,C_21] :
      ( ~ r1_xboole_0(A_19,B_20)
      | ~ r2_hidden(C_21,k3_xboole_0(A_19,B_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_41,plain,(
    ! [C_21] :
      ( ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4'))
      | ~ r2_hidden(C_21,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_33,c_38])).

tff(c_47,plain,(
    ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_41])).

tff(c_81,plain,
    ( k9_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_71,c_47])).

tff(c_89,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_16,c_81])).

tff(c_92,plain,(
    ! [C_32] : ~ r2_hidden(C_32,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_41])).

tff(c_96,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_92])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:47:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.23  
% 1.86/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 1.86/1.23  
% 1.86/1.23  %Foreground sorts:
% 1.86/1.23  
% 1.86/1.23  
% 1.86/1.23  %Background operators:
% 1.86/1.23  
% 1.86/1.23  
% 1.86/1.23  %Foreground operators:
% 1.86/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.86/1.23  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.86/1.23  tff('#skF_3', type, '#skF_3': $i).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.23  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.86/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.86/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.86/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.23  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.86/1.23  
% 1.86/1.24  tff(f_72, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_relat_1)).
% 1.86/1.24  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.86/1.24  tff(f_61, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t151_relat_1)).
% 1.86/1.24  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.86/1.24  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.86/1.24  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.86/1.24  tff(c_20, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.24  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.24  tff(c_22, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.24  tff(c_16, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.24  tff(c_58, plain, (![B_26, A_27]: (r1_xboole_0(k1_relat_1(B_26), A_27) | k9_relat_1(B_26, A_27)!=k1_xboole_0 | ~v1_relat_1(B_26))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.86/1.24  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.24  tff(c_71, plain, (![A_30, B_31]: (r1_xboole_0(A_30, k1_relat_1(B_31)) | k9_relat_1(B_31, A_30)!=k1_xboole_0 | ~v1_relat_1(B_31))), inference(resolution, [status(thm)], [c_58, c_2])).
% 1.86/1.24  tff(c_18, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 1.86/1.24  tff(c_29, plain, (![A_17, B_18]: (k3_xboole_0(A_17, B_18)=A_17 | ~r1_tarski(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.86/1.24  tff(c_33, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_18, c_29])).
% 1.86/1.24  tff(c_38, plain, (![A_19, B_20, C_21]: (~r1_xboole_0(A_19, B_20) | ~r2_hidden(C_21, k3_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.86/1.24  tff(c_41, plain, (![C_21]: (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4')) | ~r2_hidden(C_21, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_33, c_38])).
% 1.86/1.24  tff(c_47, plain, (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_41])).
% 1.86/1.24  tff(c_81, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_71, c_47])).
% 1.86/1.24  tff(c_89, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_16, c_81])).
% 1.86/1.24  tff(c_92, plain, (![C_32]: (~r2_hidden(C_32, '#skF_3'))), inference(splitRight, [status(thm)], [c_41])).
% 1.86/1.24  tff(c_96, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_92])).
% 1.86/1.24  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_96])).
% 1.86/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.24  
% 1.86/1.24  Inference rules
% 1.86/1.24  ----------------------
% 1.86/1.24  #Ref     : 0
% 1.86/1.24  #Sup     : 17
% 1.86/1.24  #Fact    : 0
% 1.86/1.24  #Define  : 0
% 1.86/1.24  #Split   : 1
% 1.86/1.24  #Chain   : 0
% 1.86/1.24  #Close   : 0
% 1.86/1.24  
% 1.86/1.24  Ordering : KBO
% 1.86/1.24  
% 1.86/1.24  Simplification rules
% 1.86/1.24  ----------------------
% 1.86/1.24  #Subsume      : 0
% 1.86/1.24  #Demod        : 2
% 1.86/1.24  #Tautology    : 6
% 1.86/1.24  #SimpNegUnit  : 2
% 1.86/1.24  #BackRed      : 0
% 1.86/1.24  
% 1.86/1.24  #Partial instantiations: 0
% 1.86/1.24  #Strategies tried      : 1
% 1.86/1.24  
% 1.86/1.24  Timing (in seconds)
% 1.86/1.24  ----------------------
% 1.86/1.25  Preprocessing        : 0.31
% 1.86/1.25  Parsing              : 0.16
% 1.86/1.25  CNF conversion       : 0.02
% 1.86/1.25  Main loop            : 0.11
% 1.86/1.25  Inferencing          : 0.05
% 1.86/1.25  Reduction            : 0.03
% 1.86/1.25  Demodulation         : 0.02
% 1.86/1.25  BG Simplification    : 0.01
% 1.86/1.25  Subsumption          : 0.02
% 1.86/1.25  Abstraction          : 0.00
% 1.86/1.25  MUC search           : 0.00
% 1.86/1.25  Cooper               : 0.00
% 1.86/1.25  Total                : 0.45
% 1.86/1.25  Index Insertion      : 0.00
% 1.86/1.25  Index Deletion       : 0.00
% 1.86/1.25  Index Matching       : 0.00
% 1.86/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
