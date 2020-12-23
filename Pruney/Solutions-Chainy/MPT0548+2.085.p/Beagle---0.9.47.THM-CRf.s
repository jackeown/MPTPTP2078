%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:46 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   38 (  44 expanded)
%              Number of leaves         :   22 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  50 expanded)
%              Number of equality atoms :   14 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( ! [C] :
          ( r2_hidden(C,A)
        <=> r2_hidden(C,B) )
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_88,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26),B_26)
      | r2_hidden('#skF_2'(A_25,B_26),A_25)
      | B_26 = A_25 ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_69,plain,(
    ! [A_20,B_21] : ~ r2_hidden(A_20,k2_zfmisc_1(A_20,B_21)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_72,plain,(
    ! [A_4] : ~ r2_hidden(A_4,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_69])).

tff(c_95,plain,(
    ! [B_26] :
      ( r2_hidden('#skF_1'(k1_xboole_0,B_26),B_26)
      | k1_xboole_0 = B_26 ) ),
    inference(resolution,[status(thm)],[c_88,c_72])).

tff(c_42,plain,(
    ! [B_18] : k2_zfmisc_1(k1_xboole_0,B_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_18,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_46,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_18])).

tff(c_30,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_160,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden('#skF_3'(A_39,B_40,C_41),k1_relat_1(C_41))
      | ~ r2_hidden(A_39,k9_relat_1(C_41,B_40))
      | ~ v1_relat_1(C_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_163,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_3'(A_39,B_40,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_39,k9_relat_1(k1_xboole_0,B_40))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_160])).

tff(c_165,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_3'(A_39,B_40,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_39,k9_relat_1(k1_xboole_0,B_40)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_163])).

tff(c_167,plain,(
    ! [A_42,B_43] : ~ r2_hidden(A_42,k9_relat_1(k1_xboole_0,B_43)) ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_165])).

tff(c_190,plain,(
    ! [B_43] : k9_relat_1(k1_xboole_0,B_43) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_95,c_167])).

tff(c_32,plain,(
    k9_relat_1(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_196,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.32  % Computer   : n020.cluster.edu
% 0.12/0.32  % Model      : x86_64 x86_64
% 0.12/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.32  % Memory     : 8042.1875MB
% 0.12/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.32  % CPULimit   : 60
% 0.12/0.32  % DateTime   : Tue Dec  1 16:53:22 EST 2020
% 0.12/0.32  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.17  
% 1.92/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.17  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_4 > #skF_3 > #skF_2 > #skF_1
% 1.92/1.17  
% 1.92/1.17  %Foreground sorts:
% 1.92/1.17  
% 1.92/1.17  
% 1.92/1.17  %Background operators:
% 1.92/1.17  
% 1.92/1.17  
% 1.92/1.17  %Foreground operators:
% 1.92/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.17  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.92/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.17  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.92/1.17  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.92/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.17  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.92/1.17  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.92/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.92/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.17  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.92/1.17  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.92/1.17  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.92/1.17  
% 1.92/1.18  tff(f_32, axiom, (![A, B]: ((![C]: (r2_hidden(C, A) <=> r2_hidden(C, B))) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tarski)).
% 1.92/1.18  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.92/1.18  tff(f_41, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.92/1.18  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.92/1.18  tff(f_57, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.92/1.18  tff(f_54, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_relat_1)).
% 1.92/1.18  tff(f_60, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t150_relat_1)).
% 1.92/1.18  tff(c_88, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26), B_26) | r2_hidden('#skF_2'(A_25, B_26), A_25) | B_26=A_25)), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.92/1.18  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.92/1.18  tff(c_69, plain, (![A_20, B_21]: (~r2_hidden(A_20, k2_zfmisc_1(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.18  tff(c_72, plain, (![A_4]: (~r2_hidden(A_4, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_12, c_69])).
% 1.92/1.18  tff(c_95, plain, (![B_26]: (r2_hidden('#skF_1'(k1_xboole_0, B_26), B_26) | k1_xboole_0=B_26)), inference(resolution, [status(thm)], [c_88, c_72])).
% 1.92/1.18  tff(c_42, plain, (![B_18]: (k2_zfmisc_1(k1_xboole_0, B_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.92/1.18  tff(c_18, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.18  tff(c_46, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_42, c_18])).
% 1.92/1.18  tff(c_30, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.92/1.18  tff(c_160, plain, (![A_39, B_40, C_41]: (r2_hidden('#skF_3'(A_39, B_40, C_41), k1_relat_1(C_41)) | ~r2_hidden(A_39, k9_relat_1(C_41, B_40)) | ~v1_relat_1(C_41))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.92/1.18  tff(c_163, plain, (![A_39, B_40]: (r2_hidden('#skF_3'(A_39, B_40, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_39, k9_relat_1(k1_xboole_0, B_40)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_30, c_160])).
% 1.92/1.18  tff(c_165, plain, (![A_39, B_40]: (r2_hidden('#skF_3'(A_39, B_40, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_39, k9_relat_1(k1_xboole_0, B_40)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_163])).
% 1.92/1.18  tff(c_167, plain, (![A_42, B_43]: (~r2_hidden(A_42, k9_relat_1(k1_xboole_0, B_43)))), inference(negUnitSimplification, [status(thm)], [c_72, c_165])).
% 1.92/1.18  tff(c_190, plain, (![B_43]: (k9_relat_1(k1_xboole_0, B_43)=k1_xboole_0)), inference(resolution, [status(thm)], [c_95, c_167])).
% 1.92/1.18  tff(c_32, plain, (k9_relat_1(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.92/1.18  tff(c_196, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_32])).
% 1.92/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.18  
% 1.92/1.18  Inference rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Ref     : 0
% 1.92/1.18  #Sup     : 34
% 1.92/1.18  #Fact    : 0
% 1.92/1.18  #Define  : 0
% 1.92/1.18  #Split   : 0
% 1.92/1.18  #Chain   : 0
% 1.92/1.18  #Close   : 0
% 1.92/1.18  
% 1.92/1.18  Ordering : KBO
% 1.92/1.18  
% 1.92/1.18  Simplification rules
% 1.92/1.18  ----------------------
% 1.92/1.18  #Subsume      : 6
% 1.92/1.18  #Demod        : 4
% 1.92/1.18  #Tautology    : 16
% 1.92/1.18  #SimpNegUnit  : 1
% 1.92/1.18  #BackRed      : 2
% 1.92/1.18  
% 1.92/1.18  #Partial instantiations: 0
% 1.92/1.18  #Strategies tried      : 1
% 1.92/1.18  
% 1.92/1.18  Timing (in seconds)
% 1.92/1.18  ----------------------
% 1.92/1.18  Preprocessing        : 0.28
% 1.92/1.18  Parsing              : 0.15
% 1.92/1.18  CNF conversion       : 0.02
% 1.92/1.18  Main loop            : 0.16
% 1.92/1.18  Inferencing          : 0.07
% 1.92/1.18  Reduction            : 0.04
% 1.92/1.18  Demodulation         : 0.03
% 1.92/1.18  BG Simplification    : 0.01
% 1.92/1.18  Subsumption          : 0.03
% 1.92/1.18  Abstraction          : 0.01
% 1.92/1.18  MUC search           : 0.00
% 1.92/1.18  Cooper               : 0.00
% 1.92/1.18  Total                : 0.47
% 1.92/1.18  Index Insertion      : 0.00
% 1.92/1.18  Index Deletion       : 0.00
% 1.92/1.19  Index Matching       : 0.00
% 1.92/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------
