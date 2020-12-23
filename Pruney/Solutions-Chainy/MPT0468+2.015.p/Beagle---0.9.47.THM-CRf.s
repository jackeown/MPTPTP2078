%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:51 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   24 (  26 expanded)
%              Number of leaves         :   15 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  29 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,k2_zfmisc_1(A,B))
        | r1_tarski(A,k2_zfmisc_1(B,A)) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t135_zfmisc_1)).

tff(c_12,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    v1_relat_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_30,B_31] :
      ( r2_hidden(k4_tarski('#skF_1'(A_30,B_31),'#skF_2'(A_30,B_31)),A_30)
      | r1_tarski(A_30,B_31)
      | ~ v1_relat_1(A_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_14,plain,(
    ! [B_22,C_23] : ~ r2_hidden(k4_tarski(B_22,C_23),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [B_31] :
      ( r1_tarski('#skF_3',B_31)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_20,c_14])).

tff(c_28,plain,(
    ! [B_32] : r1_tarski('#skF_3',B_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r1_tarski(A_1,k2_zfmisc_1(A_1,B_2))
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_28,c_4])).

tff(c_40,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:03:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.10  
% 1.64/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.10  %$ r2_hidden > r1_tarski > v1_relat_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_3 > #skF_2 > #skF_1
% 1.64/1.10  
% 1.64/1.10  %Foreground sorts:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Background operators:
% 1.64/1.10  
% 1.64/1.10  
% 1.64/1.10  %Foreground operators:
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.64/1.10  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.64/1.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.64/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.64/1.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.64/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.64/1.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.64/1.10  
% 1.64/1.11  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 1.64/1.11  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 1.64/1.11  tff(f_31, axiom, (![A, B]: ((r1_tarski(A, k2_zfmisc_1(A, B)) | r1_tarski(A, k2_zfmisc_1(B, A))) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t135_zfmisc_1)).
% 1.64/1.11  tff(c_12, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.11  tff(c_16, plain, (v1_relat_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.11  tff(c_20, plain, (![A_30, B_31]: (r2_hidden(k4_tarski('#skF_1'(A_30, B_31), '#skF_2'(A_30, B_31)), A_30) | r1_tarski(A_30, B_31) | ~v1_relat_1(A_30))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.64/1.11  tff(c_14, plain, (![B_22, C_23]: (~r2_hidden(k4_tarski(B_22, C_23), '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.11  tff(c_24, plain, (![B_31]: (r1_tarski('#skF_3', B_31) | ~v1_relat_1('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_14])).
% 1.64/1.11  tff(c_28, plain, (![B_32]: (r1_tarski('#skF_3', B_32))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 1.64/1.11  tff(c_4, plain, (![A_1, B_2]: (~r1_tarski(A_1, k2_zfmisc_1(A_1, B_2)) | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.11  tff(c_32, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_28, c_4])).
% 1.64/1.11  tff(c_40, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_32])).
% 1.64/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.11  
% 1.64/1.11  Inference rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Ref     : 0
% 1.64/1.11  #Sup     : 3
% 1.64/1.11  #Fact    : 0
% 1.64/1.11  #Define  : 0
% 1.64/1.11  #Split   : 0
% 1.64/1.11  #Chain   : 0
% 1.64/1.11  #Close   : 0
% 1.64/1.11  
% 1.64/1.11  Ordering : KBO
% 1.64/1.11  
% 1.64/1.11  Simplification rules
% 1.64/1.11  ----------------------
% 1.64/1.11  #Subsume      : 0
% 1.64/1.11  #Demod        : 1
% 1.64/1.11  #Tautology    : 0
% 1.64/1.11  #SimpNegUnit  : 1
% 1.64/1.11  #BackRed      : 0
% 1.64/1.11  
% 1.64/1.11  #Partial instantiations: 0
% 1.64/1.11  #Strategies tried      : 1
% 1.64/1.11  
% 1.64/1.11  Timing (in seconds)
% 1.64/1.11  ----------------------
% 1.64/1.11  Preprocessing        : 0.28
% 1.64/1.11  Parsing              : 0.15
% 1.64/1.11  CNF conversion       : 0.02
% 1.64/1.11  Main loop            : 0.07
% 1.64/1.11  Inferencing          : 0.03
% 1.64/1.11  Reduction            : 0.02
% 1.64/1.11  Demodulation         : 0.02
% 1.64/1.11  BG Simplification    : 0.01
% 1.64/1.11  Subsumption          : 0.01
% 1.64/1.11  Abstraction          : 0.00
% 1.64/1.11  MUC search           : 0.00
% 1.64/1.11  Cooper               : 0.00
% 1.64/1.11  Total                : 0.38
% 1.64/1.11  Index Insertion      : 0.00
% 1.64/1.11  Index Deletion       : 0.00
% 1.64/1.11  Index Matching       : 0.00
% 1.64/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------
