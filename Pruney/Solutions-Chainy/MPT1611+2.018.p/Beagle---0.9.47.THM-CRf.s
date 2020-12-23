%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:34 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   49 (  58 expanded)
%              Number of leaves         :   31 (  35 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  53 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_53,axiom,(
    ! [A] : r1_tarski(k1_tarski(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_57,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_66,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_55,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_26,plain,(
    ! [A_36] : r1_tarski(k1_tarski(A_36),k1_zfmisc_1(A_36)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_90,plain,(
    ! [A_51,C_52,B_53] :
      ( r2_hidden(A_51,C_52)
      | ~ r1_tarski(k2_tarski(A_51,B_53),C_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_94,plain,(
    ! [A_54,C_55] :
      ( r2_hidden(A_54,C_55)
      | ~ r1_tarski(k1_tarski(A_54),C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_90])).

tff(c_99,plain,(
    ! [A_56] : r2_hidden(A_56,k1_zfmisc_1(A_56)) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_103,plain,(
    ! [A_56] : ~ v1_xboole_0(k1_zfmisc_1(A_56)) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_98,plain,(
    ! [A_36] : r2_hidden(A_36,k1_zfmisc_1(A_36)) ),
    inference(resolution,[status(thm)],[c_26,c_94])).

tff(c_30,plain,(
    ! [A_38] : k9_setfam_1(A_38) = k1_zfmisc_1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_40] : k2_yellow_1(k9_setfam_1(A_40)) = k3_yellow_1(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_37,plain,(
    ! [A_40] : k2_yellow_1(k1_zfmisc_1(A_40)) = k3_yellow_1(A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_34])).

tff(c_28,plain,(
    ! [A_37] : k3_tarski(k1_zfmisc_1(A_37)) = A_37 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_144,plain,(
    ! [A_73] :
      ( k4_yellow_0(k2_yellow_1(A_73)) = k3_tarski(A_73)
      | ~ r2_hidden(k3_tarski(A_73),A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_147,plain,(
    ! [A_37] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_37))) = k3_tarski(k1_zfmisc_1(A_37))
      | ~ r2_hidden(A_37,k1_zfmisc_1(A_37))
      | v1_xboole_0(k1_zfmisc_1(A_37)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_144])).

tff(c_149,plain,(
    ! [A_37] :
      ( k4_yellow_0(k3_yellow_1(A_37)) = A_37
      | v1_xboole_0(k1_zfmisc_1(A_37)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_37,c_28,c_147])).

tff(c_150,plain,(
    ! [A_37] : k4_yellow_0(k3_yellow_1(A_37)) = A_37 ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_149])).

tff(c_36,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_162,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_36])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.13/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:49:16 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.23  
% 2.05/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.23  %$ r2_hidden > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_tarski > #skF_1 > #skF_2
% 2.05/1.23  
% 2.05/1.23  %Foreground sorts:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Background operators:
% 2.05/1.23  
% 2.05/1.23  
% 2.05/1.23  %Foreground operators:
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.23  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.05/1.23  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.05/1.23  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.05/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.05/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.05/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.23  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.05/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.23  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.23  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.05/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.23  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.05/1.23  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.05/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.05/1.23  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.05/1.23  
% 2.14/1.24  tff(f_53, axiom, (![A]: r1_tarski(k1_tarski(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_zfmisc_1)).
% 2.14/1.24  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.14/1.24  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.14/1.24  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.14/1.24  tff(f_57, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.14/1.24  tff(f_66, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.14/1.24  tff(f_55, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.14/1.24  tff(f_64, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.14/1.24  tff(f_69, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.14/1.24  tff(c_26, plain, (![A_36]: (r1_tarski(k1_tarski(A_36), k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.24  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.24  tff(c_90, plain, (![A_51, C_52, B_53]: (r2_hidden(A_51, C_52) | ~r1_tarski(k2_tarski(A_51, B_53), C_52))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.14/1.24  tff(c_94, plain, (![A_54, C_55]: (r2_hidden(A_54, C_55) | ~r1_tarski(k1_tarski(A_54), C_55))), inference(superposition, [status(thm), theory('equality')], [c_6, c_90])).
% 2.14/1.24  tff(c_99, plain, (![A_56]: (r2_hidden(A_56, k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_26, c_94])).
% 2.14/1.24  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.14/1.24  tff(c_103, plain, (![A_56]: (~v1_xboole_0(k1_zfmisc_1(A_56)))), inference(resolution, [status(thm)], [c_99, c_2])).
% 2.14/1.24  tff(c_98, plain, (![A_36]: (r2_hidden(A_36, k1_zfmisc_1(A_36)))), inference(resolution, [status(thm)], [c_26, c_94])).
% 2.14/1.24  tff(c_30, plain, (![A_38]: (k9_setfam_1(A_38)=k1_zfmisc_1(A_38))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.14/1.24  tff(c_34, plain, (![A_40]: (k2_yellow_1(k9_setfam_1(A_40))=k3_yellow_1(A_40))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.14/1.24  tff(c_37, plain, (![A_40]: (k2_yellow_1(k1_zfmisc_1(A_40))=k3_yellow_1(A_40))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_34])).
% 2.14/1.24  tff(c_28, plain, (![A_37]: (k3_tarski(k1_zfmisc_1(A_37))=A_37)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.14/1.24  tff(c_144, plain, (![A_73]: (k4_yellow_0(k2_yellow_1(A_73))=k3_tarski(A_73) | ~r2_hidden(k3_tarski(A_73), A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.14/1.24  tff(c_147, plain, (![A_37]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_37)))=k3_tarski(k1_zfmisc_1(A_37)) | ~r2_hidden(A_37, k1_zfmisc_1(A_37)) | v1_xboole_0(k1_zfmisc_1(A_37)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_144])).
% 2.14/1.24  tff(c_149, plain, (![A_37]: (k4_yellow_0(k3_yellow_1(A_37))=A_37 | v1_xboole_0(k1_zfmisc_1(A_37)))), inference(demodulation, [status(thm), theory('equality')], [c_98, c_37, c_28, c_147])).
% 2.14/1.24  tff(c_150, plain, (![A_37]: (k4_yellow_0(k3_yellow_1(A_37))=A_37)), inference(negUnitSimplification, [status(thm)], [c_103, c_149])).
% 2.14/1.24  tff(c_36, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.14/1.24  tff(c_162, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_150, c_36])).
% 2.14/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.14/1.24  
% 2.14/1.24  Inference rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Ref     : 0
% 2.14/1.24  #Sup     : 26
% 2.14/1.24  #Fact    : 0
% 2.14/1.24  #Define  : 0
% 2.14/1.24  #Split   : 0
% 2.14/1.24  #Chain   : 0
% 2.14/1.24  #Close   : 0
% 2.14/1.24  
% 2.14/1.24  Ordering : KBO
% 2.14/1.24  
% 2.14/1.24  Simplification rules
% 2.14/1.24  ----------------------
% 2.14/1.24  #Subsume      : 1
% 2.14/1.24  #Demod        : 5
% 2.14/1.24  #Tautology    : 20
% 2.14/1.24  #SimpNegUnit  : 1
% 2.14/1.24  #BackRed      : 1
% 2.14/1.24  
% 2.14/1.24  #Partial instantiations: 0
% 2.14/1.24  #Strategies tried      : 1
% 2.14/1.24  
% 2.14/1.24  Timing (in seconds)
% 2.14/1.24  ----------------------
% 2.14/1.24  Preprocessing        : 0.33
% 2.14/1.24  Parsing              : 0.18
% 2.14/1.24  CNF conversion       : 0.02
% 2.14/1.24  Main loop            : 0.14
% 2.14/1.24  Inferencing          : 0.06
% 2.14/1.24  Reduction            : 0.04
% 2.14/1.24  Demodulation         : 0.03
% 2.14/1.24  BG Simplification    : 0.01
% 2.14/1.24  Subsumption          : 0.02
% 2.14/1.24  Abstraction          : 0.01
% 2.14/1.24  MUC search           : 0.00
% 2.14/1.24  Cooper               : 0.00
% 2.14/1.24  Total                : 0.49
% 2.14/1.24  Index Insertion      : 0.00
% 2.14/1.24  Index Deletion       : 0.00
% 2.14/1.24  Index Matching       : 0.00
% 2.14/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
