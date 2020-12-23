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
% DateTime   : Thu Dec  3 10:10:41 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   35 (  40 expanded)
%              Number of leaves         :   20 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   38 (  51 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k1_wellord2,type,(
    k1_wellord2: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_wellord1,type,(
    k2_wellord1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_48,axiom,(
    ! [A] : v1_relat_1(k1_wellord2(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

tff(f_52,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_wellord1(k1_wellord2(B),A) = k1_wellord2(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] : k2_wellord1(A,B) = k3_xboole_0(A,k2_zfmisc_1(B,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_wellord1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_55,negated_conjecture,(
    ~ ! [A] : r1_tarski(k1_wellord2(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_wellord2)).

tff(c_37,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_1'(A_27,B_28),A_27)
      | r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_52,plain,(
    ! [A_27] : r1_tarski(A_27,A_27) ),
    inference(resolution,[status(thm)],[c_37,c_4])).

tff(c_28,plain,(
    ! [A_15] : v1_relat_1(k1_wellord2(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_30,plain,(
    ! [B_17,A_16] :
      ( k2_wellord1(k1_wellord2(B_17),A_16) = k1_wellord2(A_16)
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_26,plain,(
    ! [A_12,B_14] :
      ( k3_xboole_0(A_12,k2_zfmisc_1(B_14,B_14)) = k2_wellord1(A_12,B_14)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [D_11,B_7,A_6] :
      ( r2_hidden(D_11,B_7)
      | ~ r2_hidden(D_11,k3_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_146,plain,(
    ! [A_49,B_50,B_51] :
      ( r2_hidden('#skF_1'(k3_xboole_0(A_49,B_50),B_51),B_50)
      | r1_tarski(k3_xboole_0(A_49,B_50),B_51) ) ),
    inference(resolution,[status(thm)],[c_37,c_10])).

tff(c_183,plain,(
    ! [A_55,B_56] : r1_tarski(k3_xboole_0(A_55,B_56),B_56) ),
    inference(resolution,[status(thm)],[c_146,c_4])).

tff(c_187,plain,(
    ! [A_57,B_58] :
      ( r1_tarski(k2_wellord1(A_57,B_58),k2_zfmisc_1(B_58,B_58))
      | ~ v1_relat_1(A_57) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_183])).

tff(c_190,plain,(
    ! [A_16,B_17] :
      ( r1_tarski(k1_wellord2(A_16),k2_zfmisc_1(A_16,A_16))
      | ~ v1_relat_1(k1_wellord2(B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_187])).

tff(c_193,plain,(
    ! [A_59,B_60] :
      ( r1_tarski(k1_wellord2(A_59),k2_zfmisc_1(A_59,A_59))
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_190])).

tff(c_202,plain,(
    ! [A_27] : r1_tarski(k1_wellord2(A_27),k2_zfmisc_1(A_27,A_27)) ),
    inference(resolution,[status(thm)],[c_52,c_193])).

tff(c_32,plain,(
    ~ r1_tarski(k1_wellord2('#skF_4'),k2_zfmisc_1('#skF_4','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_256,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:58:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.22  
% 1.84/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.22  %$ r2_hidden > r1_tarski > v1_relat_1 > k3_xboole_0 > k2_zfmisc_1 > k2_wellord1 > #nlpp > k1_wellord2 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.84/1.22  
% 1.84/1.22  %Foreground sorts:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Background operators:
% 1.84/1.22  
% 1.84/1.22  
% 1.84/1.22  %Foreground operators:
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.84/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.84/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.84/1.22  tff(k1_wellord2, type, k1_wellord2: $i > $i).
% 1.84/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.84/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.84/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.84/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.84/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.84/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.84/1.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.84/1.22  tff(k2_wellord1, type, k2_wellord1: ($i * $i) > $i).
% 1.84/1.22  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.84/1.22  
% 1.84/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.84/1.23  tff(f_48, axiom, (![A]: v1_relat_1(k1_wellord2(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_wellord2)).
% 1.84/1.23  tff(f_52, axiom, (![A, B]: (r1_tarski(A, B) => (k2_wellord1(k1_wellord2(B), A) = k1_wellord2(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_wellord2)).
% 1.84/1.23  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (![B]: (k2_wellord1(A, B) = k3_xboole_0(A, k2_zfmisc_1(B, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_wellord1)).
% 1.84/1.23  tff(f_41, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.84/1.23  tff(f_55, negated_conjecture, ~(![A]: r1_tarski(k1_wellord2(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_wellord2)).
% 1.84/1.23  tff(c_37, plain, (![A_27, B_28]: (r2_hidden('#skF_1'(A_27, B_28), A_27) | r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.23  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.84/1.23  tff(c_52, plain, (![A_27]: (r1_tarski(A_27, A_27))), inference(resolution, [status(thm)], [c_37, c_4])).
% 1.84/1.23  tff(c_28, plain, (![A_15]: (v1_relat_1(k1_wellord2(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.84/1.23  tff(c_30, plain, (![B_17, A_16]: (k2_wellord1(k1_wellord2(B_17), A_16)=k1_wellord2(A_16) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.84/1.23  tff(c_26, plain, (![A_12, B_14]: (k3_xboole_0(A_12, k2_zfmisc_1(B_14, B_14))=k2_wellord1(A_12, B_14) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.84/1.23  tff(c_10, plain, (![D_11, B_7, A_6]: (r2_hidden(D_11, B_7) | ~r2_hidden(D_11, k3_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.84/1.23  tff(c_146, plain, (![A_49, B_50, B_51]: (r2_hidden('#skF_1'(k3_xboole_0(A_49, B_50), B_51), B_50) | r1_tarski(k3_xboole_0(A_49, B_50), B_51))), inference(resolution, [status(thm)], [c_37, c_10])).
% 1.84/1.23  tff(c_183, plain, (![A_55, B_56]: (r1_tarski(k3_xboole_0(A_55, B_56), B_56))), inference(resolution, [status(thm)], [c_146, c_4])).
% 1.84/1.23  tff(c_187, plain, (![A_57, B_58]: (r1_tarski(k2_wellord1(A_57, B_58), k2_zfmisc_1(B_58, B_58)) | ~v1_relat_1(A_57))), inference(superposition, [status(thm), theory('equality')], [c_26, c_183])).
% 1.84/1.23  tff(c_190, plain, (![A_16, B_17]: (r1_tarski(k1_wellord2(A_16), k2_zfmisc_1(A_16, A_16)) | ~v1_relat_1(k1_wellord2(B_17)) | ~r1_tarski(A_16, B_17))), inference(superposition, [status(thm), theory('equality')], [c_30, c_187])).
% 1.84/1.23  tff(c_193, plain, (![A_59, B_60]: (r1_tarski(k1_wellord2(A_59), k2_zfmisc_1(A_59, A_59)) | ~r1_tarski(A_59, B_60))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_190])).
% 1.84/1.23  tff(c_202, plain, (![A_27]: (r1_tarski(k1_wellord2(A_27), k2_zfmisc_1(A_27, A_27)))), inference(resolution, [status(thm)], [c_52, c_193])).
% 1.84/1.23  tff(c_32, plain, (~r1_tarski(k1_wellord2('#skF_4'), k2_zfmisc_1('#skF_4', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.84/1.23  tff(c_256, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_32])).
% 1.84/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.84/1.23  
% 1.84/1.23  Inference rules
% 1.84/1.23  ----------------------
% 1.84/1.23  #Ref     : 0
% 1.84/1.23  #Sup     : 48
% 1.84/1.23  #Fact    : 0
% 1.84/1.23  #Define  : 0
% 1.84/1.23  #Split   : 0
% 1.84/1.23  #Chain   : 0
% 1.84/1.23  #Close   : 0
% 1.84/1.23  
% 1.84/1.23  Ordering : KBO
% 1.84/1.23  
% 1.84/1.23  Simplification rules
% 1.84/1.23  ----------------------
% 1.84/1.23  #Subsume      : 0
% 1.84/1.23  #Demod        : 4
% 1.84/1.23  #Tautology    : 8
% 1.84/1.23  #SimpNegUnit  : 0
% 1.84/1.23  #BackRed      : 1
% 1.84/1.23  
% 1.84/1.23  #Partial instantiations: 0
% 1.84/1.23  #Strategies tried      : 1
% 1.84/1.23  
% 1.84/1.23  Timing (in seconds)
% 1.84/1.23  ----------------------
% 1.84/1.23  Preprocessing        : 0.28
% 1.84/1.23  Parsing              : 0.15
% 1.84/1.23  CNF conversion       : 0.02
% 1.84/1.23  Main loop            : 0.20
% 1.84/1.23  Inferencing          : 0.08
% 1.84/1.23  Reduction            : 0.05
% 1.84/1.23  Demodulation         : 0.03
% 1.84/1.23  BG Simplification    : 0.01
% 1.84/1.23  Subsumption          : 0.04
% 1.84/1.23  Abstraction          : 0.01
% 1.84/1.23  MUC search           : 0.00
% 1.84/1.23  Cooper               : 0.00
% 1.84/1.23  Total                : 0.50
% 1.84/1.23  Index Insertion      : 0.00
% 1.84/1.23  Index Deletion       : 0.00
% 1.84/1.23  Index Matching       : 0.00
% 1.84/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
