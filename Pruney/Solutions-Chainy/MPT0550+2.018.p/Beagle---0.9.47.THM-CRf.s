%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:54 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   43 (  54 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   51 (  81 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ~ ( A != k1_xboole_0
            & r1_tarski(A,k1_relat_1(B))
            & k9_relat_1(B,A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_64,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k9_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t151_relat_1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_22,plain,(
    k9_relat_1('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_148,plain,(
    ! [B_55,A_56] :
      ( r1_xboole_0(k1_relat_1(B_55),A_56)
      | k9_relat_1(B_55,A_56) != k1_xboole_0
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_8,plain,(
    ! [B_7,A_6] :
      ( r1_xboole_0(B_7,A_6)
      | ~ r1_xboole_0(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_173,plain,(
    ! [A_57,B_58] :
      ( r1_xboole_0(A_57,k1_relat_1(B_58))
      | k9_relat_1(B_58,A_57) != k1_xboole_0
      | ~ v1_relat_1(B_58) ) ),
    inference(resolution,[status(thm)],[c_148,c_8])).

tff(c_24,plain,(
    r1_tarski('#skF_3',k1_relat_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_34,plain,(
    ! [A_21,B_22] :
      ( k3_xboole_0(A_21,B_22) = A_21
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    k3_xboole_0('#skF_3',k1_relat_1('#skF_4')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_34])).

tff(c_45,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,k3_xboole_0(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    ! [C_29] :
      ( ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4'))
      | ~ r2_hidden(C_29,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_45])).

tff(c_54,plain,(
    ~ r1_xboole_0('#skF_3',k1_relat_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_193,plain,
    ( k9_relat_1('#skF_4','#skF_3') != k1_xboole_0
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_173,c_54])).

tff(c_204,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_22,c_193])).

tff(c_207,plain,(
    ! [C_59] : ~ r2_hidden(C_59,'#skF_3') ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_214,plain,(
    ! [B_60] : r1_tarski('#skF_3',B_60) ),
    inference(resolution,[status(thm)],[c_6,c_207])).

tff(c_16,plain,(
    ! [A_15,B_16] :
      ( k1_xboole_0 = A_15
      | ~ r1_tarski(A_15,k4_xboole_0(B_16,A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_218,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_214,c_16])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:30:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.26  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k9_relat_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.13/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.13/1.26  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.13/1.26  tff('#skF_3', type, '#skF_3': $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.13/1.26  tff('#skF_4', type, '#skF_4': $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.13/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.13/1.26  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.13/1.26  
% 2.13/1.27  tff(f_75, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ~((~(A = k1_xboole_0) & r1_tarski(A, k1_relat_1(B))) & (k9_relat_1(B, A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_relat_1)).
% 2.13/1.27  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.13/1.27  tff(f_64, axiom, (![A, B]: (v1_relat_1(B) => ((k9_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t151_relat_1)).
% 2.13/1.27  tff(f_36, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.13/1.27  tff(f_54, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.13/1.27  tff(f_50, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.13/1.27  tff(f_58, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.13/1.27  tff(c_26, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.13/1.27  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_22, plain, (k9_relat_1('#skF_4', '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_148, plain, (![B_55, A_56]: (r1_xboole_0(k1_relat_1(B_55), A_56) | k9_relat_1(B_55, A_56)!=k1_xboole_0 | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.13/1.27  tff(c_8, plain, (![B_7, A_6]: (r1_xboole_0(B_7, A_6) | ~r1_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.13/1.27  tff(c_173, plain, (![A_57, B_58]: (r1_xboole_0(A_57, k1_relat_1(B_58)) | k9_relat_1(B_58, A_57)!=k1_xboole_0 | ~v1_relat_1(B_58))), inference(resolution, [status(thm)], [c_148, c_8])).
% 2.13/1.27  tff(c_24, plain, (r1_tarski('#skF_3', k1_relat_1('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.13/1.27  tff(c_34, plain, (![A_21, B_22]: (k3_xboole_0(A_21, B_22)=A_21 | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.13/1.27  tff(c_38, plain, (k3_xboole_0('#skF_3', k1_relat_1('#skF_4'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_34])).
% 2.13/1.27  tff(c_45, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, k3_xboole_0(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.13/1.27  tff(c_52, plain, (![C_29]: (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4')) | ~r2_hidden(C_29, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_38, c_45])).
% 2.13/1.27  tff(c_54, plain, (~r1_xboole_0('#skF_3', k1_relat_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_52])).
% 2.13/1.27  tff(c_193, plain, (k9_relat_1('#skF_4', '#skF_3')!=k1_xboole_0 | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_173, c_54])).
% 2.13/1.27  tff(c_204, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_22, c_193])).
% 2.13/1.27  tff(c_207, plain, (![C_59]: (~r2_hidden(C_59, '#skF_3'))), inference(splitRight, [status(thm)], [c_52])).
% 2.13/1.27  tff(c_214, plain, (![B_60]: (r1_tarski('#skF_3', B_60))), inference(resolution, [status(thm)], [c_6, c_207])).
% 2.13/1.27  tff(c_16, plain, (![A_15, B_16]: (k1_xboole_0=A_15 | ~r1_tarski(A_15, k4_xboole_0(B_16, A_15)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.13/1.27  tff(c_218, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_214, c_16])).
% 2.13/1.27  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_218])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 44
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 1
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 2
% 2.13/1.27  #Demod        : 4
% 2.13/1.27  #Tautology    : 9
% 2.13/1.27  #SimpNegUnit  : 2
% 2.13/1.27  #BackRed      : 0
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.27  Preprocessing        : 0.30
% 2.13/1.27  Parsing              : 0.17
% 2.13/1.27  CNF conversion       : 0.02
% 2.13/1.27  Main loop            : 0.18
% 2.13/1.27  Inferencing          : 0.07
% 2.13/1.27  Reduction            : 0.05
% 2.13/1.27  Demodulation         : 0.03
% 2.13/1.27  BG Simplification    : 0.01
% 2.13/1.27  Subsumption          : 0.03
% 2.13/1.27  Abstraction          : 0.01
% 2.13/1.27  MUC search           : 0.00
% 2.13/1.27  Cooper               : 0.00
% 2.13/1.27  Total                : 0.51
% 2.13/1.27  Index Insertion      : 0.00
% 2.13/1.27  Index Deletion       : 0.00
% 2.13/1.27  Index Matching       : 0.00
% 2.13/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
