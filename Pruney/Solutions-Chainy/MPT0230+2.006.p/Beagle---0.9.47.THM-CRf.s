%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:58 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :   53 (  67 expanded)
%              Number of leaves         :   29 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   62 (  97 expanded)
%              Number of equality atoms :   22 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_49,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_133,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = k1_xboole_0
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_152,plain,(
    ! [B_4] : k4_xboole_0(B_4,B_4) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_52,plain,(
    ! [B_35] : k4_xboole_0(k1_tarski(B_35),k1_tarski(B_35)) != k1_tarski(B_35) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_434,plain,(
    ! [B_35] : k1_tarski(B_35) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_52])).

tff(c_58,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_50,plain,(
    ! [A_32,B_33] :
      ( r1_xboole_0(k1_tarski(A_32),B_33)
      | r2_hidden(A_32,B_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_16,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,k2_xboole_0(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1747,plain,(
    ! [A_124,B_125,C_126] :
      ( r1_tarski(A_124,B_125)
      | ~ r1_xboole_0(A_124,C_126)
      | ~ r1_tarski(A_124,k2_xboole_0(B_125,C_126)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1983,plain,(
    ! [A_136,C_137,B_138] :
      ( r1_tarski(A_136,C_137)
      | ~ r1_xboole_0(A_136,B_138)
      | ~ r1_tarski(A_136,B_138) ) ),
    inference(resolution,[status(thm)],[c_16,c_1747])).

tff(c_8925,plain,(
    ! [A_9728,C_9729,B_9730] :
      ( r1_tarski(k1_tarski(A_9728),C_9729)
      | ~ r1_tarski(k1_tarski(A_9728),B_9730)
      | r2_hidden(A_9728,B_9730) ) ),
    inference(resolution,[status(thm)],[c_50,c_1983])).

tff(c_8978,plain,(
    ! [C_9729] :
      ( r1_tarski(k1_tarski('#skF_3'),C_9729)
      | r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_60,c_8925])).

tff(c_9050,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_8978])).

tff(c_26,plain,(
    ! [D_25,B_21,A_20] :
      ( D_25 = B_21
      | D_25 = A_20
      | ~ r2_hidden(D_25,k2_tarski(A_20,B_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_9053,plain,
    ( '#skF_5' = '#skF_3'
    | '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9050,c_26])).

tff(c_9128,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_56,c_9053])).

tff(c_9132,plain,(
    ! [C_9948] : r1_tarski(k1_tarski('#skF_3'),C_9948) ),
    inference(splitRight,[status(thm)],[c_8978])).

tff(c_20,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_436,plain,(
    ! [B_70,A_71] :
      ( B_70 = A_71
      | ~ r1_tarski(B_70,A_71)
      | ~ r1_tarski(A_71,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_457,plain,(
    ! [A_14] :
      ( k1_xboole_0 = A_14
      | ~ r1_tarski(A_14,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_20,c_436])).

tff(c_9190,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_9132,c_457])).

tff(c_9260,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_434,c_9190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:46:34 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.12/2.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.64  
% 7.12/2.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.64  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 7.12/2.64  
% 7.12/2.64  %Foreground sorts:
% 7.12/2.64  
% 7.12/2.64  
% 7.12/2.64  %Background operators:
% 7.12/2.64  
% 7.12/2.64  
% 7.12/2.64  %Foreground operators:
% 7.12/2.64  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.12/2.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.12/2.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.12/2.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.12/2.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.12/2.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.12/2.64  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.12/2.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.12/2.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.12/2.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.12/2.64  tff('#skF_5', type, '#skF_5': $i).
% 7.12/2.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.12/2.64  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.12/2.64  tff('#skF_3', type, '#skF_3': $i).
% 7.12/2.64  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.12/2.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.12/2.64  tff('#skF_4', type, '#skF_4': $i).
% 7.12/2.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.12/2.64  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.12/2.64  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.12/2.64  
% 7.12/2.65  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.12/2.65  tff(f_37, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.12/2.65  tff(f_82, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 7.12/2.65  tff(f_92, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 7.12/2.65  tff(f_77, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 7.12/2.65  tff(f_43, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 7.12/2.65  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_xboole_1)).
% 7.12/2.65  tff(f_66, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 7.12/2.65  tff(f_49, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 7.12/2.65  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.12/2.65  tff(c_133, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=k1_xboole_0 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.12/2.65  tff(c_152, plain, (![B_4]: (k4_xboole_0(B_4, B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_133])).
% 7.12/2.65  tff(c_52, plain, (![B_35]: (k4_xboole_0(k1_tarski(B_35), k1_tarski(B_35))!=k1_tarski(B_35))), inference(cnfTransformation, [status(thm)], [f_82])).
% 7.12/2.65  tff(c_434, plain, (![B_35]: (k1_tarski(B_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_52])).
% 7.12/2.65  tff(c_58, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.12/2.65  tff(c_56, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.12/2.65  tff(c_60, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.12/2.65  tff(c_50, plain, (![A_32, B_33]: (r1_xboole_0(k1_tarski(A_32), B_33) | r2_hidden(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.12/2.65  tff(c_16, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, k2_xboole_0(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.12/2.65  tff(c_1747, plain, (![A_124, B_125, C_126]: (r1_tarski(A_124, B_125) | ~r1_xboole_0(A_124, C_126) | ~r1_tarski(A_124, k2_xboole_0(B_125, C_126)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.12/2.65  tff(c_1983, plain, (![A_136, C_137, B_138]: (r1_tarski(A_136, C_137) | ~r1_xboole_0(A_136, B_138) | ~r1_tarski(A_136, B_138))), inference(resolution, [status(thm)], [c_16, c_1747])).
% 7.12/2.65  tff(c_8925, plain, (![A_9728, C_9729, B_9730]: (r1_tarski(k1_tarski(A_9728), C_9729) | ~r1_tarski(k1_tarski(A_9728), B_9730) | r2_hidden(A_9728, B_9730))), inference(resolution, [status(thm)], [c_50, c_1983])).
% 7.12/2.65  tff(c_8978, plain, (![C_9729]: (r1_tarski(k1_tarski('#skF_3'), C_9729) | r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_60, c_8925])).
% 7.12/2.65  tff(c_9050, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(splitLeft, [status(thm)], [c_8978])).
% 7.12/2.65  tff(c_26, plain, (![D_25, B_21, A_20]: (D_25=B_21 | D_25=A_20 | ~r2_hidden(D_25, k2_tarski(A_20, B_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.12/2.65  tff(c_9053, plain, ('#skF_5'='#skF_3' | '#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_9050, c_26])).
% 7.12/2.65  tff(c_9128, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_56, c_9053])).
% 7.12/2.65  tff(c_9132, plain, (![C_9948]: (r1_tarski(k1_tarski('#skF_3'), C_9948))), inference(splitRight, [status(thm)], [c_8978])).
% 7.12/2.65  tff(c_20, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 7.12/2.65  tff(c_436, plain, (![B_70, A_71]: (B_70=A_71 | ~r1_tarski(B_70, A_71) | ~r1_tarski(A_71, B_70))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.12/2.65  tff(c_457, plain, (![A_14]: (k1_xboole_0=A_14 | ~r1_tarski(A_14, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_436])).
% 7.12/2.65  tff(c_9190, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_9132, c_457])).
% 7.12/2.65  tff(c_9260, plain, $false, inference(negUnitSimplification, [status(thm)], [c_434, c_9190])).
% 7.12/2.65  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.65  
% 7.12/2.65  Inference rules
% 7.12/2.65  ----------------------
% 7.12/2.65  #Ref     : 0
% 7.12/2.65  #Sup     : 1853
% 7.12/2.65  #Fact    : 6
% 7.12/2.65  #Define  : 0
% 7.12/2.65  #Split   : 13
% 7.12/2.65  #Chain   : 0
% 7.12/2.65  #Close   : 0
% 7.12/2.65  
% 7.12/2.65  Ordering : KBO
% 7.12/2.65  
% 7.12/2.65  Simplification rules
% 7.12/2.65  ----------------------
% 7.12/2.65  #Subsume      : 512
% 7.12/2.65  #Demod        : 1754
% 7.12/2.65  #Tautology    : 870
% 7.12/2.65  #SimpNegUnit  : 13
% 7.12/2.65  #BackRed      : 0
% 7.12/2.65  
% 7.12/2.65  #Partial instantiations: 5670
% 7.12/2.65  #Strategies tried      : 1
% 7.12/2.65  
% 7.12/2.65  Timing (in seconds)
% 7.12/2.65  ----------------------
% 7.12/2.65  Preprocessing        : 0.33
% 7.12/2.65  Parsing              : 0.17
% 7.12/2.65  CNF conversion       : 0.02
% 7.12/2.65  Main loop            : 1.57
% 7.12/2.65  Inferencing          : 0.56
% 7.12/2.65  Reduction            : 0.63
% 7.12/2.65  Demodulation         : 0.52
% 7.12/2.65  BG Simplification    : 0.04
% 7.12/2.65  Subsumption          : 0.26
% 7.12/2.65  Abstraction          : 0.06
% 7.12/2.65  MUC search           : 0.00
% 7.12/2.65  Cooper               : 0.00
% 7.12/2.66  Total                : 1.92
% 7.12/2.66  Index Insertion      : 0.00
% 7.12/2.66  Index Deletion       : 0.00
% 7.12/2.66  Index Matching       : 0.00
% 7.12/2.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
