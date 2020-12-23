%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:40 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   41 (  41 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  36 expanded)
%              Number of equality atoms :   15 (  15 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_53,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_43,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_39,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_62,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_55,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_14,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | v1_relat_1(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_50,plain,(
    ! [A_36,B_37,C_38] :
      ( ~ r1_xboole_0(A_36,B_37)
      | ~ r2_hidden(C_38,k3_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_57,plain,(
    ! [A_6,C_38] :
      ( ~ r1_xboole_0(A_6,k1_xboole_0)
      | ~ r2_hidden(C_38,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_74,plain,(
    ! [C_41] : ~ r2_hidden(C_41,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_57])).

tff(c_79,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_74])).

tff(c_20,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_16,plain,(
    ! [A_26] : k7_relat_1(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    ! [B_39,A_40] :
      ( k2_relat_1(k7_relat_1(B_39,A_40)) = k9_relat_1(B_39,A_40)
      | ~ v1_relat_1(B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [A_26] :
      ( k9_relat_1(k1_xboole_0,A_26) = k2_relat_1(k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_61])).

tff(c_73,plain,(
    ! [A_26] :
      ( k9_relat_1(k1_xboole_0,A_26) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_70])).

tff(c_81,plain,(
    ! [A_26] : k9_relat_1(k1_xboole_0,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_73])).

tff(c_24,plain,(
    k9_relat_1(k1_xboole_0,'#skF_5') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_84,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:28:02 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.15  
% 1.83/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.15  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > k4_tarski > k3_xboole_0 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_5 > #skF_1 > #skF_4
% 1.83/1.15  
% 1.83/1.15  %Foreground sorts:
% 1.83/1.15  
% 1.83/1.15  
% 1.83/1.15  %Background operators:
% 1.83/1.15  
% 1.83/1.15  
% 1.83/1.15  %Foreground operators:
% 1.83/1.15  tff('#skF_2', type, '#skF_2': $i > $i).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.83/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.83/1.15  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.83/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.83/1.15  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.83/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.83/1.15  tff('#skF_5', type, '#skF_5': $i).
% 1.83/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.83/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.15  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.83/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.83/1.15  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 1.83/1.15  
% 1.83/1.16  tff(f_53, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_relat_1)).
% 1.83/1.16  tff(f_43, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.83/1.16  tff(f_41, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 1.83/1.16  tff(f_39, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 1.83/1.16  tff(f_62, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.83/1.16  tff(f_55, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 1.83/1.16  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.83/1.16  tff(f_65, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.83/1.16  tff(c_14, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | v1_relat_1(A_8))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.83/1.16  tff(c_8, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.83/1.16  tff(c_6, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.83/1.16  tff(c_50, plain, (![A_36, B_37, C_38]: (~r1_xboole_0(A_36, B_37) | ~r2_hidden(C_38, k3_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.83/1.16  tff(c_57, plain, (![A_6, C_38]: (~r1_xboole_0(A_6, k1_xboole_0) | ~r2_hidden(C_38, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_50])).
% 1.83/1.16  tff(c_74, plain, (![C_41]: (~r2_hidden(C_41, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_57])).
% 1.83/1.16  tff(c_79, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_74])).
% 1.83/1.16  tff(c_20, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.83/1.16  tff(c_16, plain, (![A_26]: (k7_relat_1(k1_xboole_0, A_26)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.83/1.16  tff(c_61, plain, (![B_39, A_40]: (k2_relat_1(k7_relat_1(B_39, A_40))=k9_relat_1(B_39, A_40) | ~v1_relat_1(B_39))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.83/1.16  tff(c_70, plain, (![A_26]: (k9_relat_1(k1_xboole_0, A_26)=k2_relat_1(k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_16, c_61])).
% 1.83/1.16  tff(c_73, plain, (![A_26]: (k9_relat_1(k1_xboole_0, A_26)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_70])).
% 1.83/1.16  tff(c_81, plain, (![A_26]: (k9_relat_1(k1_xboole_0, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_73])).
% 1.83/1.16  tff(c_24, plain, (k9_relat_1(k1_xboole_0, '#skF_5')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.83/1.16  tff(c_84, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81, c_24])).
% 1.83/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.83/1.16  
% 1.83/1.16  Inference rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Ref     : 0
% 1.83/1.16  #Sup     : 14
% 1.83/1.16  #Fact    : 0
% 1.83/1.16  #Define  : 0
% 1.83/1.16  #Split   : 0
% 1.83/1.16  #Chain   : 0
% 1.83/1.16  #Close   : 0
% 1.83/1.16  
% 1.83/1.16  Ordering : KBO
% 1.83/1.16  
% 1.83/1.16  Simplification rules
% 1.83/1.16  ----------------------
% 1.83/1.16  #Subsume      : 0
% 1.83/1.16  #Demod        : 4
% 1.83/1.16  #Tautology    : 10
% 1.83/1.16  #SimpNegUnit  : 0
% 1.83/1.16  #BackRed      : 1
% 1.83/1.16  
% 1.83/1.16  #Partial instantiations: 0
% 1.83/1.16  #Strategies tried      : 1
% 1.83/1.16  
% 1.83/1.16  Timing (in seconds)
% 1.83/1.16  ----------------------
% 1.83/1.17  Preprocessing        : 0.29
% 1.83/1.17  Parsing              : 0.16
% 1.83/1.17  CNF conversion       : 0.02
% 1.83/1.17  Main loop            : 0.11
% 1.83/1.17  Inferencing          : 0.05
% 1.83/1.17  Reduction            : 0.03
% 1.83/1.17  Demodulation         : 0.02
% 1.83/1.17  BG Simplification    : 0.01
% 1.83/1.17  Subsumption          : 0.01
% 1.83/1.17  Abstraction          : 0.00
% 1.83/1.17  MUC search           : 0.00
% 1.83/1.17  Cooper               : 0.00
% 1.83/1.17  Total                : 0.43
% 1.83/1.17  Index Insertion      : 0.00
% 1.83/1.17  Index Deletion       : 0.00
% 1.83/1.17  Index Matching       : 0.00
% 1.83/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
