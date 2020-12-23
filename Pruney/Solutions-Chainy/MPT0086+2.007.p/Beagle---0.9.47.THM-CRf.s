%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:14 EST 2020

% Result     : Theorem 26.29s
% Output     : CNFRefutation 26.29s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   41 (  49 expanded)
%              Number of equality atoms :   11 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_6,plain,(
    ! [A_3] :
      ( v1_xboole_0(A_3)
      | r2_hidden('#skF_1'(A_3),A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_120,plain,(
    ! [D_38,A_39,B_40] :
      ( r2_hidden(D_38,A_39)
      | ~ r2_hidden(D_38,k3_xboole_0(A_39,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_131,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_39,B_40)),A_39)
      | v1_xboole_0(k3_xboole_0(A_39,B_40)) ) ),
    inference(resolution,[status(thm)],[c_6,c_120])).

tff(c_108,plain,(
    ! [D_35,B_36,A_37] :
      ( r2_hidden(D_35,B_36)
      | ~ r2_hidden(D_35,k3_xboole_0(A_37,B_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2142,plain,(
    ! [A_175,B_176] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_175,B_176)),B_176)
      | v1_xboole_0(k3_xboole_0(A_175,B_176)) ) ),
    inference(resolution,[status(thm)],[c_6,c_108])).

tff(c_28,plain,(
    ! [D_18,B_14,A_13] :
      ( ~ r2_hidden(D_18,B_14)
      | ~ r2_hidden(D_18,k4_xboole_0(A_13,B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_91092,plain,(
    ! [A_1255,A_1256,B_1257] :
      ( ~ r2_hidden('#skF_1'(k3_xboole_0(A_1255,k4_xboole_0(A_1256,B_1257))),B_1257)
      | v1_xboole_0(k3_xboole_0(A_1255,k4_xboole_0(A_1256,B_1257))) ) ),
    inference(resolution,[status(thm)],[c_2142,c_28])).

tff(c_91469,plain,(
    ! [A_1258,A_1259] : v1_xboole_0(k3_xboole_0(A_1258,k4_xboole_0(A_1259,A_1258))) ),
    inference(resolution,[status(thm)],[c_131,c_91092])).

tff(c_48,plain,(
    ! [A_21] :
      ( k1_xboole_0 = A_21
      | ~ v1_xboole_0(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_92012,plain,(
    ! [A_1258,A_1259] : k3_xboole_0(A_1258,k4_xboole_0(A_1259,A_1258)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_91469,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_92,plain,(
    ! [A_30,B_31] :
      ( r1_xboole_0(A_30,B_31)
      | k3_xboole_0(A_30,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    ~ r1_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_98,plain,(
    k3_xboole_0(k4_xboole_0('#skF_6','#skF_7'),'#skF_7') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_92,c_50])).

tff(c_101,plain,(
    k3_xboole_0('#skF_7',k4_xboole_0('#skF_6','#skF_7')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_98])).

tff(c_92061,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_92012,c_101])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:14:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 26.29/16.93  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.29/16.93  
% 26.29/16.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.29/16.93  %$ r2_hidden > r1_xboole_0 > v1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_6 > #skF_5 > #skF_2 > #skF_3
% 26.29/16.93  
% 26.29/16.93  %Foreground sorts:
% 26.29/16.93  
% 26.29/16.93  
% 26.29/16.93  %Background operators:
% 26.29/16.93  
% 26.29/16.93  
% 26.29/16.93  %Foreground operators:
% 26.29/16.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 26.29/16.93  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 26.29/16.93  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 26.29/16.93  tff('#skF_1', type, '#skF_1': $i > $i).
% 26.29/16.93  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 26.29/16.93  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 26.29/16.93  tff('#skF_7', type, '#skF_7': $i).
% 26.29/16.93  tff('#skF_6', type, '#skF_6': $i).
% 26.29/16.93  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 26.29/16.93  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 26.29/16.93  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 26.29/16.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 26.29/16.93  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 26.29/16.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 26.29/16.93  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 26.29/16.93  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 26.29/16.93  
% 26.29/16.94  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 26.29/16.94  tff(f_42, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 26.29/16.94  tff(f_52, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 26.29/16.94  tff(f_60, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_boole)).
% 26.29/16.94  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 26.29/16.94  tff(f_56, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 26.29/16.94  tff(f_63, negated_conjecture, ~(![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 26.29/16.94  tff(c_6, plain, (![A_3]: (v1_xboole_0(A_3) | r2_hidden('#skF_1'(A_3), A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 26.29/16.94  tff(c_120, plain, (![D_38, A_39, B_40]: (r2_hidden(D_38, A_39) | ~r2_hidden(D_38, k3_xboole_0(A_39, B_40)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 26.29/16.94  tff(c_131, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(k3_xboole_0(A_39, B_40)), A_39) | v1_xboole_0(k3_xboole_0(A_39, B_40)))), inference(resolution, [status(thm)], [c_6, c_120])).
% 26.29/16.94  tff(c_108, plain, (![D_35, B_36, A_37]: (r2_hidden(D_35, B_36) | ~r2_hidden(D_35, k3_xboole_0(A_37, B_36)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 26.29/16.94  tff(c_2142, plain, (![A_175, B_176]: (r2_hidden('#skF_1'(k3_xboole_0(A_175, B_176)), B_176) | v1_xboole_0(k3_xboole_0(A_175, B_176)))), inference(resolution, [status(thm)], [c_6, c_108])).
% 26.29/16.94  tff(c_28, plain, (![D_18, B_14, A_13]: (~r2_hidden(D_18, B_14) | ~r2_hidden(D_18, k4_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 26.29/16.94  tff(c_91092, plain, (![A_1255, A_1256, B_1257]: (~r2_hidden('#skF_1'(k3_xboole_0(A_1255, k4_xboole_0(A_1256, B_1257))), B_1257) | v1_xboole_0(k3_xboole_0(A_1255, k4_xboole_0(A_1256, B_1257))))), inference(resolution, [status(thm)], [c_2142, c_28])).
% 26.29/16.94  tff(c_91469, plain, (![A_1258, A_1259]: (v1_xboole_0(k3_xboole_0(A_1258, k4_xboole_0(A_1259, A_1258))))), inference(resolution, [status(thm)], [c_131, c_91092])).
% 26.29/16.94  tff(c_48, plain, (![A_21]: (k1_xboole_0=A_21 | ~v1_xboole_0(A_21))), inference(cnfTransformation, [status(thm)], [f_60])).
% 26.29/16.94  tff(c_92012, plain, (![A_1258, A_1259]: (k3_xboole_0(A_1258, k4_xboole_0(A_1259, A_1258))=k1_xboole_0)), inference(resolution, [status(thm)], [c_91469, c_48])).
% 26.29/16.94  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 26.29/16.94  tff(c_92, plain, (![A_30, B_31]: (r1_xboole_0(A_30, B_31) | k3_xboole_0(A_30, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 26.29/16.94  tff(c_50, plain, (~r1_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_63])).
% 26.29/16.94  tff(c_98, plain, (k3_xboole_0(k4_xboole_0('#skF_6', '#skF_7'), '#skF_7')!=k1_xboole_0), inference(resolution, [status(thm)], [c_92, c_50])).
% 26.29/16.94  tff(c_101, plain, (k3_xboole_0('#skF_7', k4_xboole_0('#skF_6', '#skF_7'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_2, c_98])).
% 26.29/16.94  tff(c_92061, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_92012, c_101])).
% 26.29/16.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 26.29/16.94  
% 26.29/16.94  Inference rules
% 26.29/16.94  ----------------------
% 26.29/16.94  #Ref     : 0
% 26.29/16.94  #Sup     : 26457
% 26.29/16.94  #Fact    : 0
% 26.29/16.94  #Define  : 0
% 26.29/16.94  #Split   : 1
% 26.29/16.94  #Chain   : 0
% 26.29/16.94  #Close   : 0
% 26.29/16.94  
% 26.29/16.94  Ordering : KBO
% 26.29/16.94  
% 26.29/16.94  Simplification rules
% 26.29/16.94  ----------------------
% 26.29/16.94  #Subsume      : 12253
% 26.29/16.94  #Demod        : 8490
% 26.29/16.94  #Tautology    : 5752
% 26.29/16.94  #SimpNegUnit  : 3
% 26.29/16.94  #BackRed      : 11
% 26.29/16.94  
% 26.29/16.94  #Partial instantiations: 0
% 26.29/16.94  #Strategies tried      : 1
% 26.29/16.94  
% 26.29/16.94  Timing (in seconds)
% 26.29/16.94  ----------------------
% 26.29/16.95  Preprocessing        : 0.32
% 26.29/16.95  Parsing              : 0.16
% 26.29/16.95  CNF conversion       : 0.03
% 26.29/16.95  Main loop            : 15.82
% 26.29/16.95  Inferencing          : 2.08
% 26.29/16.95  Reduction            : 3.09
% 26.29/16.95  Demodulation         : 2.39
% 26.29/16.95  BG Simplification    : 0.27
% 26.29/16.95  Subsumption          : 9.78
% 26.29/16.95  Abstraction          : 0.41
% 26.29/16.95  MUC search           : 0.00
% 26.29/16.95  Cooper               : 0.00
% 26.29/16.95  Total                : 16.16
% 26.29/16.95  Index Insertion      : 0.00
% 26.29/16.95  Index Deletion       : 0.00
% 26.29/16.95  Index Matching       : 0.00
% 26.29/16.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
