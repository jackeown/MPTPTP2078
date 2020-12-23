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
% DateTime   : Thu Dec  3 10:07:13 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   27 (  34 expanded)
%              Number of leaves         :   15 (  19 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  51 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( ! [C] :
            ( r2_hidden(C,A)
           => r2_hidden(k4_tarski(C,C),B) )
       => r1_tarski(k6_relat_1(A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A] : r1_tarski(k6_relat_1(A),k2_zfmisc_1(A,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_relset_1)).

tff(c_8,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_7,B_8] :
      ( r2_hidden('#skF_1'(A_7,B_8),A_7)
      | r1_tarski(k6_relat_1(A_7),B_8)
      | ~ v1_relat_1(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( r2_hidden(k4_tarski(A_1,B_2),k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden(B_2,D_4)
      | ~ r2_hidden(A_1,C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [A_26,B_27] :
      ( ~ r2_hidden(k4_tarski('#skF_1'(A_26,B_27),'#skF_1'(A_26,B_27)),B_27)
      | r1_tarski(k6_relat_1(A_26),B_27)
      | ~ v1_relat_1(B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_32,plain,(
    ! [A_26,C_3,D_4] :
      ( r1_tarski(k6_relat_1(A_26),k2_zfmisc_1(C_3,D_4))
      | ~ v1_relat_1(k2_zfmisc_1(C_3,D_4))
      | ~ r2_hidden('#skF_1'(A_26,k2_zfmisc_1(C_3,D_4)),D_4)
      | ~ r2_hidden('#skF_1'(A_26,k2_zfmisc_1(C_3,D_4)),C_3) ) ),
    inference(resolution,[status(thm)],[c_2,c_28])).

tff(c_36,plain,(
    ! [A_28,C_29,D_30] :
      ( r1_tarski(k6_relat_1(A_28),k2_zfmisc_1(C_29,D_30))
      | ~ r2_hidden('#skF_1'(A_28,k2_zfmisc_1(C_29,D_30)),D_30)
      | ~ r2_hidden('#skF_1'(A_28,k2_zfmisc_1(C_29,D_30)),C_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_32])).

tff(c_39,plain,(
    ! [A_7,C_29] :
      ( ~ r2_hidden('#skF_1'(A_7,k2_zfmisc_1(C_29,A_7)),C_29)
      | r1_tarski(k6_relat_1(A_7),k2_zfmisc_1(C_29,A_7))
      | ~ v1_relat_1(k2_zfmisc_1(C_29,A_7)) ) ),
    inference(resolution,[status(thm)],[c_12,c_36])).

tff(c_43,plain,(
    ! [A_31,C_32] :
      ( ~ r2_hidden('#skF_1'(A_31,k2_zfmisc_1(C_32,A_31)),C_32)
      | r1_tarski(k6_relat_1(A_31),k2_zfmisc_1(C_32,A_31)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_39])).

tff(c_47,plain,(
    ! [A_7] :
      ( r1_tarski(k6_relat_1(A_7),k2_zfmisc_1(A_7,A_7))
      | ~ v1_relat_1(k2_zfmisc_1(A_7,A_7)) ) ),
    inference(resolution,[status(thm)],[c_12,c_43])).

tff(c_50,plain,(
    ! [A_7] : r1_tarski(k6_relat_1(A_7),k2_zfmisc_1(A_7,A_7)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_47])).

tff(c_14,plain,(
    ~ r1_tarski(k6_relat_1('#skF_2'),k2_zfmisc_1('#skF_2','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 14:00:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.10  
% 1.60/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.11  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k6_relat_1 > #skF_2 > #skF_1
% 1.60/1.11  
% 1.60/1.11  %Foreground sorts:
% 1.60/1.11  
% 1.60/1.11  
% 1.60/1.11  %Background operators:
% 1.60/1.11  
% 1.60/1.11  
% 1.60/1.11  %Foreground operators:
% 1.60/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.60/1.11  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.60/1.11  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.60/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.11  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.60/1.11  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 1.60/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.60/1.11  
% 1.60/1.12  tff(f_33, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 1.60/1.12  tff(f_42, axiom, (![A, B]: (v1_relat_1(B) => ((![C]: (r2_hidden(C, A) => r2_hidden(k4_tarski(C, C), B))) => r1_tarski(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_relat_1)).
% 1.60/1.12  tff(f_31, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 1.60/1.12  tff(f_45, negated_conjecture, ~(![A]: r1_tarski(k6_relat_1(A), k2_zfmisc_1(A, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_relset_1)).
% 1.60/1.12  tff(c_8, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.12  tff(c_12, plain, (![A_7, B_8]: (r2_hidden('#skF_1'(A_7, B_8), A_7) | r1_tarski(k6_relat_1(A_7), B_8) | ~v1_relat_1(B_8))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.12  tff(c_2, plain, (![A_1, B_2, C_3, D_4]: (r2_hidden(k4_tarski(A_1, B_2), k2_zfmisc_1(C_3, D_4)) | ~r2_hidden(B_2, D_4) | ~r2_hidden(A_1, C_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.12  tff(c_28, plain, (![A_26, B_27]: (~r2_hidden(k4_tarski('#skF_1'(A_26, B_27), '#skF_1'(A_26, B_27)), B_27) | r1_tarski(k6_relat_1(A_26), B_27) | ~v1_relat_1(B_27))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.60/1.12  tff(c_32, plain, (![A_26, C_3, D_4]: (r1_tarski(k6_relat_1(A_26), k2_zfmisc_1(C_3, D_4)) | ~v1_relat_1(k2_zfmisc_1(C_3, D_4)) | ~r2_hidden('#skF_1'(A_26, k2_zfmisc_1(C_3, D_4)), D_4) | ~r2_hidden('#skF_1'(A_26, k2_zfmisc_1(C_3, D_4)), C_3))), inference(resolution, [status(thm)], [c_2, c_28])).
% 1.60/1.12  tff(c_36, plain, (![A_28, C_29, D_30]: (r1_tarski(k6_relat_1(A_28), k2_zfmisc_1(C_29, D_30)) | ~r2_hidden('#skF_1'(A_28, k2_zfmisc_1(C_29, D_30)), D_30) | ~r2_hidden('#skF_1'(A_28, k2_zfmisc_1(C_29, D_30)), C_29))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_32])).
% 1.60/1.12  tff(c_39, plain, (![A_7, C_29]: (~r2_hidden('#skF_1'(A_7, k2_zfmisc_1(C_29, A_7)), C_29) | r1_tarski(k6_relat_1(A_7), k2_zfmisc_1(C_29, A_7)) | ~v1_relat_1(k2_zfmisc_1(C_29, A_7)))), inference(resolution, [status(thm)], [c_12, c_36])).
% 1.60/1.12  tff(c_43, plain, (![A_31, C_32]: (~r2_hidden('#skF_1'(A_31, k2_zfmisc_1(C_32, A_31)), C_32) | r1_tarski(k6_relat_1(A_31), k2_zfmisc_1(C_32, A_31)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_39])).
% 1.60/1.12  tff(c_47, plain, (![A_7]: (r1_tarski(k6_relat_1(A_7), k2_zfmisc_1(A_7, A_7)) | ~v1_relat_1(k2_zfmisc_1(A_7, A_7)))), inference(resolution, [status(thm)], [c_12, c_43])).
% 1.60/1.12  tff(c_50, plain, (![A_7]: (r1_tarski(k6_relat_1(A_7), k2_zfmisc_1(A_7, A_7)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_47])).
% 1.60/1.12  tff(c_14, plain, (~r1_tarski(k6_relat_1('#skF_2'), k2_zfmisc_1('#skF_2', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.12  tff(c_53, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 1.60/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.12  
% 1.60/1.12  Inference rules
% 1.60/1.12  ----------------------
% 1.60/1.12  #Ref     : 0
% 1.60/1.12  #Sup     : 5
% 1.60/1.12  #Fact    : 0
% 1.60/1.12  #Define  : 0
% 1.60/1.12  #Split   : 0
% 1.60/1.12  #Chain   : 0
% 1.60/1.12  #Close   : 0
% 1.60/1.12  
% 1.60/1.12  Ordering : KBO
% 1.60/1.12  
% 1.60/1.12  Simplification rules
% 1.60/1.12  ----------------------
% 1.60/1.12  #Subsume      : 0
% 1.60/1.12  #Demod        : 4
% 1.60/1.12  #Tautology    : 2
% 1.60/1.12  #SimpNegUnit  : 0
% 1.60/1.12  #BackRed      : 1
% 1.60/1.12  
% 1.60/1.12  #Partial instantiations: 0
% 1.60/1.12  #Strategies tried      : 1
% 1.60/1.12  
% 1.60/1.12  Timing (in seconds)
% 1.60/1.12  ----------------------
% 1.60/1.12  Preprocessing        : 0.24
% 1.60/1.12  Parsing              : 0.13
% 1.60/1.12  CNF conversion       : 0.02
% 1.60/1.12  Main loop            : 0.10
% 1.60/1.12  Inferencing          : 0.05
% 1.60/1.12  Reduction            : 0.03
% 1.60/1.12  Demodulation         : 0.02
% 1.60/1.12  BG Simplification    : 0.01
% 1.60/1.12  Subsumption          : 0.01
% 1.60/1.12  Abstraction          : 0.00
% 1.60/1.12  MUC search           : 0.00
% 1.60/1.12  Cooper               : 0.00
% 1.60/1.12  Total                : 0.37
% 1.60/1.12  Index Insertion      : 0.00
% 1.60/1.12  Index Deletion       : 0.00
% 1.60/1.12  Index Matching       : 0.00
% 1.60/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------
