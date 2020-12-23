%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:27 EST 2020

% Result     : Theorem 1.71s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  37 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   41 (  51 expanded)
%              Number of equality atoms :    9 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C] :
        ( v1_relat_1(C)
       => ( r1_xboole_0(A,B)
         => k7_relat_1(k7_relat_1(C,A),B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t207_relat_1)).

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

tff(f_57,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_xboole_0(B,k1_relat_1(A))
         => k7_relat_1(A,B) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => k7_relat_1(k7_relat_1(C,A),B) = k7_relat_1(C,k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_relat_1)).

tff(c_18,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_20,plain,(
    v1_relat_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_23,plain,(
    ! [A_21,B_22,C_23] :
      ( ~ r1_xboole_0(A_21,B_22)
      | ~ r2_hidden(C_23,k3_xboole_0(A_21,B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_33,plain,(
    ! [A_21,B_22,B_2] :
      ( ~ r1_xboole_0(A_21,B_22)
      | r1_xboole_0(k3_xboole_0(A_21,B_22),B_2) ) ),
    inference(resolution,[status(thm)],[c_6,c_23])).

tff(c_73,plain,(
    ! [A_36,B_37] :
      ( k7_relat_1(A_36,B_37) = k1_xboole_0
      | ~ r1_xboole_0(B_37,k1_relat_1(A_36))
      | ~ v1_relat_1(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_104,plain,(
    ! [A_43,A_44,B_45] :
      ( k7_relat_1(A_43,k3_xboole_0(A_44,B_45)) = k1_xboole_0
      | ~ v1_relat_1(A_43)
      | ~ r1_xboole_0(A_44,B_45) ) ),
    inference(resolution,[status(thm)],[c_33,c_73])).

tff(c_84,plain,(
    ! [C_40,A_41,B_42] :
      ( k7_relat_1(k7_relat_1(C_40,A_41),B_42) = k7_relat_1(C_40,k3_xboole_0(A_41,B_42))
      | ~ v1_relat_1(C_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    k7_relat_1(k7_relat_1('#skF_5','#skF_3'),'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_93,plain,
    ( k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_84,c_16])).

tff(c_102,plain,(
    k7_relat_1('#skF_5',k3_xboole_0('#skF_3','#skF_4')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_93])).

tff(c_110,plain,
    ( ~ v1_relat_1('#skF_5')
    | ~ r1_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_102])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:02:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.71/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.71/1.18  
% 1.71/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.92/1.18  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k7_relat_1 > k3_xboole_0 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.92/1.18  
% 1.92/1.18  %Foreground sorts:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Background operators:
% 1.92/1.18  
% 1.92/1.18  
% 1.92/1.18  %Foreground operators:
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.18  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.92/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.18  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.18  
% 1.93/1.19  tff(f_75, negated_conjecture, ~(![A, B, C]: (v1_relat_1(C) => (r1_xboole_0(A, B) => (k7_relat_1(k7_relat_1(C, A), B) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t207_relat_1)).
% 1.93/1.19  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.93/1.19  tff(f_57, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.93/1.19  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_xboole_0(B, k1_relat_1(A)) => (k7_relat_1(A, B) = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t187_relat_1)).
% 1.93/1.19  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => (k7_relat_1(k7_relat_1(C, A), B) = k7_relat_1(C, k3_xboole_0(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_relat_1)).
% 1.93/1.19  tff(c_18, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.19  tff(c_20, plain, (v1_relat_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.19  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.93/1.19  tff(c_23, plain, (![A_21, B_22, C_23]: (~r1_xboole_0(A_21, B_22) | ~r2_hidden(C_23, k3_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.93/1.19  tff(c_33, plain, (![A_21, B_22, B_2]: (~r1_xboole_0(A_21, B_22) | r1_xboole_0(k3_xboole_0(A_21, B_22), B_2))), inference(resolution, [status(thm)], [c_6, c_23])).
% 1.93/1.19  tff(c_73, plain, (![A_36, B_37]: (k7_relat_1(A_36, B_37)=k1_xboole_0 | ~r1_xboole_0(B_37, k1_relat_1(A_36)) | ~v1_relat_1(A_36))), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.93/1.19  tff(c_104, plain, (![A_43, A_44, B_45]: (k7_relat_1(A_43, k3_xboole_0(A_44, B_45))=k1_xboole_0 | ~v1_relat_1(A_43) | ~r1_xboole_0(A_44, B_45))), inference(resolution, [status(thm)], [c_33, c_73])).
% 1.93/1.19  tff(c_84, plain, (![C_40, A_41, B_42]: (k7_relat_1(k7_relat_1(C_40, A_41), B_42)=k7_relat_1(C_40, k3_xboole_0(A_41, B_42)) | ~v1_relat_1(C_40))), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.93/1.19  tff(c_16, plain, (k7_relat_1(k7_relat_1('#skF_5', '#skF_3'), '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_75])).
% 1.93/1.19  tff(c_93, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0 | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_84, c_16])).
% 1.93/1.19  tff(c_102, plain, (k7_relat_1('#skF_5', k3_xboole_0('#skF_3', '#skF_4'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_20, c_93])).
% 1.93/1.19  tff(c_110, plain, (~v1_relat_1('#skF_5') | ~r1_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_104, c_102])).
% 1.93/1.19  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_110])).
% 1.93/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.19  
% 1.93/1.19  Inference rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Ref     : 0
% 1.93/1.19  #Sup     : 23
% 1.93/1.19  #Fact    : 0
% 1.93/1.19  #Define  : 0
% 1.93/1.19  #Split   : 0
% 1.93/1.19  #Chain   : 0
% 1.93/1.19  #Close   : 0
% 1.93/1.19  
% 1.93/1.19  Ordering : KBO
% 1.93/1.19  
% 1.93/1.19  Simplification rules
% 1.93/1.19  ----------------------
% 1.93/1.19  #Subsume      : 3
% 1.93/1.19  #Demod        : 4
% 1.93/1.19  #Tautology    : 5
% 1.93/1.19  #SimpNegUnit  : 0
% 1.93/1.19  #BackRed      : 0
% 1.93/1.19  
% 1.93/1.19  #Partial instantiations: 0
% 1.93/1.19  #Strategies tried      : 1
% 1.93/1.19  
% 1.93/1.19  Timing (in seconds)
% 1.93/1.19  ----------------------
% 1.93/1.19  Preprocessing        : 0.27
% 1.93/1.19  Parsing              : 0.16
% 1.93/1.19  CNF conversion       : 0.02
% 1.93/1.19  Main loop            : 0.14
% 1.93/1.19  Inferencing          : 0.07
% 1.93/1.19  Reduction            : 0.03
% 1.93/1.19  Demodulation         : 0.02
% 1.93/1.19  BG Simplification    : 0.01
% 1.93/1.19  Subsumption          : 0.02
% 1.93/1.19  Abstraction          : 0.01
% 1.93/1.19  MUC search           : 0.00
% 1.93/1.19  Cooper               : 0.00
% 1.93/1.19  Total                : 0.44
% 1.93/1.19  Index Insertion      : 0.00
% 1.93/1.19  Index Deletion       : 0.00
% 1.93/1.19  Index Matching       : 0.00
% 1.93/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
