%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:49 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   35 (  37 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    6
%              Number of atoms          :   39 (  45 expanded)
%              Number of equality atoms :    6 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ! [B,C] : ~ r2_hidden(k4_tarski(B,C),A)
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t56_relat_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( r1_tarski(A,B)
        <=> ! [C,D] :
              ( r2_hidden(k4_tarski(C,D),A)
             => r2_hidden(k4_tarski(C,D),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_relat_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_28,plain,(
    v1_relat_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_107,plain,(
    ! [A_57,B_58] :
      ( r2_hidden(k4_tarski('#skF_2'(A_57,B_58),'#skF_3'(A_57,B_58)),A_57)
      | r1_tarski(A_57,B_58)
      | ~ v1_relat_1(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [B_30,C_31] : ~ r2_hidden(k4_tarski(B_30,C_31),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_121,plain,(
    ! [B_58] :
      ( r1_tarski('#skF_4',B_58)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_107,c_26])).

tff(c_130,plain,(
    ! [B_59] : r1_tarski('#skF_4',B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_121])).

tff(c_40,plain,(
    ! [A_39,B_40] :
      ( r2_hidden('#skF_1'(A_39,B_40),A_39)
      | r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_14,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_33,plain,(
    ! [A_36,B_37] :
      ( ~ r2_hidden(A_36,B_37)
      | ~ r1_xboole_0(k1_tarski(A_36),B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_38,plain,(
    ! [A_36] : ~ r2_hidden(A_36,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_33])).

tff(c_45,plain,(
    ! [B_40] : r1_tarski(k1_xboole_0,B_40) ),
    inference(resolution,[status(thm)],[c_40,c_38])).

tff(c_54,plain,(
    ! [B_44,A_45] :
      ( B_44 = A_45
      | ~ r1_tarski(B_44,A_45)
      | ~ r1_tarski(A_45,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    ! [B_40] :
      ( k1_xboole_0 = B_40
      | ~ r1_tarski(B_40,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_45,c_54])).

tff(c_137,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_130,c_59])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:08:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.20  
% 1.76/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.21  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_relat_1 > k4_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.76/1.21  
% 1.76/1.21  %Foreground sorts:
% 1.76/1.21  
% 1.76/1.21  
% 1.76/1.21  %Background operators:
% 1.76/1.21  
% 1.76/1.21  
% 1.76/1.21  %Foreground operators:
% 1.76/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.21  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.76/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.76/1.21  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 1.76/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.76/1.21  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.76/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.76/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.76/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.76/1.21  
% 1.76/1.21  tff(f_64, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((![B, C]: ~r2_hidden(k4_tarski(B, C), A)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t56_relat_1)).
% 1.76/1.21  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (![B]: (r1_tarski(A, B) <=> (![C, D]: (r2_hidden(k4_tarski(C, D), A) => r2_hidden(k4_tarski(C, D), B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_relat_1)).
% 1.76/1.21  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.76/1.21  tff(f_40, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.76/1.21  tff(f_45, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.76/1.21  tff(f_38, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.76/1.21  tff(c_24, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.21  tff(c_28, plain, (v1_relat_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.21  tff(c_107, plain, (![A_57, B_58]: (r2_hidden(k4_tarski('#skF_2'(A_57, B_58), '#skF_3'(A_57, B_58)), A_57) | r1_tarski(A_57, B_58) | ~v1_relat_1(A_57))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.76/1.21  tff(c_26, plain, (![B_30, C_31]: (~r2_hidden(k4_tarski(B_30, C_31), '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.21  tff(c_121, plain, (![B_58]: (r1_tarski('#skF_4', B_58) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_107, c_26])).
% 1.76/1.21  tff(c_130, plain, (![B_59]: (r1_tarski('#skF_4', B_59))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_121])).
% 1.76/1.21  tff(c_40, plain, (![A_39, B_40]: (r2_hidden('#skF_1'(A_39, B_40), A_39) | r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.76/1.21  tff(c_14, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.76/1.21  tff(c_33, plain, (![A_36, B_37]: (~r2_hidden(A_36, B_37) | ~r1_xboole_0(k1_tarski(A_36), B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.76/1.21  tff(c_38, plain, (![A_36]: (~r2_hidden(A_36, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_33])).
% 1.76/1.21  tff(c_45, plain, (![B_40]: (r1_tarski(k1_xboole_0, B_40))), inference(resolution, [status(thm)], [c_40, c_38])).
% 1.76/1.21  tff(c_54, plain, (![B_44, A_45]: (B_44=A_45 | ~r1_tarski(B_44, A_45) | ~r1_tarski(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.21  tff(c_59, plain, (![B_40]: (k1_xboole_0=B_40 | ~r1_tarski(B_40, k1_xboole_0))), inference(resolution, [status(thm)], [c_45, c_54])).
% 1.76/1.21  tff(c_137, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_130, c_59])).
% 1.76/1.21  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_137])).
% 1.76/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.21  
% 1.76/1.21  Inference rules
% 1.76/1.21  ----------------------
% 1.76/1.21  #Ref     : 0
% 1.76/1.21  #Sup     : 20
% 1.76/1.21  #Fact    : 0
% 1.76/1.21  #Define  : 0
% 1.76/1.21  #Split   : 0
% 1.76/1.21  #Chain   : 0
% 1.76/1.21  #Close   : 0
% 1.76/1.21  
% 1.76/1.21  Ordering : KBO
% 1.76/1.21  
% 1.76/1.21  Simplification rules
% 1.76/1.21  ----------------------
% 1.76/1.21  #Subsume      : 1
% 1.76/1.21  #Demod        : 9
% 1.76/1.21  #Tautology    : 11
% 1.76/1.21  #SimpNegUnit  : 1
% 1.76/1.21  #BackRed      : 0
% 1.76/1.21  
% 1.76/1.21  #Partial instantiations: 0
% 1.76/1.21  #Strategies tried      : 1
% 1.76/1.21  
% 1.76/1.21  Timing (in seconds)
% 1.76/1.21  ----------------------
% 1.76/1.22  Preprocessing        : 0.29
% 1.76/1.22  Parsing              : 0.16
% 1.76/1.22  CNF conversion       : 0.02
% 1.76/1.22  Main loop            : 0.11
% 1.76/1.22  Inferencing          : 0.04
% 1.76/1.22  Reduction            : 0.03
% 1.76/1.22  Demodulation         : 0.02
% 1.76/1.22  BG Simplification    : 0.01
% 1.76/1.22  Subsumption          : 0.02
% 1.76/1.22  Abstraction          : 0.00
% 1.76/1.22  MUC search           : 0.00
% 1.76/1.22  Cooper               : 0.00
% 1.76/1.22  Total                : 0.43
% 1.76/1.22  Index Insertion      : 0.00
% 1.76/1.22  Index Deletion       : 0.00
% 1.76/1.22  Index Matching       : 0.00
% 1.76/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
