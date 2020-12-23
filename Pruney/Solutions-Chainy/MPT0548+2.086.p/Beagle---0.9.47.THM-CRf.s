%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:46 EST 2020

% Result     : Theorem 1.77s
% Output     : CNFRefutation 1.77s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   19 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   29 (  33 expanded)
%              Number of equality atoms :    9 (  13 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_33,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k9_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k1_relat_1(C))
            & r2_hidden(k4_tarski(D,A),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_relat_1)).

tff(f_42,axiom,(
    ! [A,B] : ~ r2_hidden(A,k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t152_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A] : k9_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t150_relat_1)).

tff(c_2,plain,(
    ! [A_1] :
      ( r2_hidden('#skF_1'(A_1),A_1)
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_45,plain,(
    ! [A_17,B_18] : v1_relat_1(k2_zfmisc_1(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_45])).

tff(c_174,plain,(
    ! [A_41,B_42,C_43] :
      ( r2_hidden(k4_tarski('#skF_2'(A_41,B_42,C_43),A_41),C_43)
      | ~ r2_hidden(A_41,k9_relat_1(C_43,B_42))
      | ~ v1_relat_1(C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_50,plain,(
    ! [A_19,B_20] : ~ r2_hidden(A_19,k2_zfmisc_1(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_53,plain,(
    ! [A_3] : ~ r2_hidden(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_50])).

tff(c_186,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,k9_relat_1(k1_xboole_0,B_42))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_174,c_53])).

tff(c_192,plain,(
    ! [A_44,B_45] : ~ r2_hidden(A_44,k9_relat_1(k1_xboole_0,B_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_186])).

tff(c_215,plain,(
    ! [B_45] : k9_relat_1(k1_xboole_0,B_45) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_192])).

tff(c_22,plain,(
    k9_relat_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n012.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:13:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.77/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  
% 1.77/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.14  %$ r2_hidden > v1_relat_1 > k9_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2
% 1.77/1.14  
% 1.77/1.14  %Foreground sorts:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Background operators:
% 1.77/1.14  
% 1.77/1.14  
% 1.77/1.14  %Foreground operators:
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.77/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.77/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.77/1.14  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.77/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.77/1.14  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.77/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.77/1.14  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.77/1.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.77/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.77/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.77/1.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.77/1.14  
% 1.77/1.15  tff(f_33, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 1.77/1.15  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.77/1.15  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.77/1.15  tff(f_55, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k9_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k1_relat_1(C)) & r2_hidden(k4_tarski(D, A), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_relat_1)).
% 1.77/1.15  tff(f_42, axiom, (![A, B]: ~r2_hidden(A, k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t152_zfmisc_1)).
% 1.77/1.15  tff(f_58, negated_conjecture, ~(![A]: (k9_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t150_relat_1)).
% 1.77/1.15  tff(c_2, plain, (![A_1]: (r2_hidden('#skF_1'(A_1), A_1) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.77/1.15  tff(c_6, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.77/1.15  tff(c_45, plain, (![A_17, B_18]: (v1_relat_1(k2_zfmisc_1(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.77/1.15  tff(c_47, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_45])).
% 1.77/1.15  tff(c_174, plain, (![A_41, B_42, C_43]: (r2_hidden(k4_tarski('#skF_2'(A_41, B_42, C_43), A_41), C_43) | ~r2_hidden(A_41, k9_relat_1(C_43, B_42)) | ~v1_relat_1(C_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.77/1.15  tff(c_50, plain, (![A_19, B_20]: (~r2_hidden(A_19, k2_zfmisc_1(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.77/1.15  tff(c_53, plain, (![A_3]: (~r2_hidden(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_6, c_50])).
% 1.77/1.15  tff(c_186, plain, (![A_41, B_42]: (~r2_hidden(A_41, k9_relat_1(k1_xboole_0, B_42)) | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_174, c_53])).
% 1.77/1.15  tff(c_192, plain, (![A_44, B_45]: (~r2_hidden(A_44, k9_relat_1(k1_xboole_0, B_45)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_186])).
% 1.77/1.15  tff(c_215, plain, (![B_45]: (k9_relat_1(k1_xboole_0, B_45)=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_192])).
% 1.77/1.15  tff(c_22, plain, (k9_relat_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.77/1.15  tff(c_220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_215, c_22])).
% 1.77/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.77/1.15  
% 1.77/1.15  Inference rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Ref     : 0
% 1.77/1.15  #Sup     : 43
% 1.77/1.15  #Fact    : 0
% 1.77/1.15  #Define  : 0
% 1.77/1.15  #Split   : 0
% 1.77/1.15  #Chain   : 0
% 1.77/1.15  #Close   : 0
% 1.77/1.15  
% 1.77/1.15  Ordering : KBO
% 1.77/1.15  
% 1.77/1.15  Simplification rules
% 1.77/1.15  ----------------------
% 1.77/1.15  #Subsume      : 11
% 1.77/1.15  #Demod        : 14
% 1.77/1.15  #Tautology    : 19
% 1.77/1.15  #SimpNegUnit  : 0
% 1.77/1.15  #BackRed      : 2
% 1.77/1.15  
% 1.77/1.15  #Partial instantiations: 0
% 1.77/1.15  #Strategies tried      : 1
% 1.77/1.15  
% 1.77/1.15  Timing (in seconds)
% 1.77/1.15  ----------------------
% 1.77/1.15  Preprocessing        : 0.26
% 1.77/1.15  Parsing              : 0.14
% 1.77/1.15  CNF conversion       : 0.02
% 1.77/1.15  Main loop            : 0.15
% 1.77/1.15  Inferencing          : 0.06
% 1.77/1.15  Reduction            : 0.04
% 1.77/1.15  Demodulation         : 0.03
% 1.77/1.15  BG Simplification    : 0.01
% 1.77/1.15  Subsumption          : 0.03
% 1.77/1.15  Abstraction          : 0.01
% 1.77/1.15  MUC search           : 0.00
% 1.77/1.15  Cooper               : 0.00
% 1.77/1.15  Total                : 0.43
% 1.77/1.15  Index Insertion      : 0.00
% 1.77/1.15  Index Deletion       : 0.00
% 1.77/1.15  Index Matching       : 0.00
% 1.77/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------
