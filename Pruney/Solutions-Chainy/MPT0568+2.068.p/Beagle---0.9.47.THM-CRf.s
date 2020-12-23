%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:29 EST 2020

% Result     : Theorem 2.73s
% Output     : CNFRefutation 2.73s
% Verified   : 
% Statistics : Number of formulae       :   52 (  63 expanded)
%              Number of leaves         :   35 (  40 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  61 expanded)
%              Number of equality atoms :   11 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_78,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_relat_1(A)
    <=> ! [B] :
          ~ ( r2_hidden(B,A)
            & ! [C,D] : B != k4_tarski(C,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A] : k10_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t172_relat_1)).

tff(c_46,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_641,plain,(
    ! [A_193,B_194] :
      ( r2_hidden(k4_tarski('#skF_5'(A_193,B_194),'#skF_4'(A_193,B_194)),A_193)
      | r2_hidden('#skF_6'(A_193,B_194),B_194)
      | k2_relat_1(A_193) = B_194 ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_80,plain,(
    ! [A_83,B_84] :
      ( ~ r2_hidden(A_83,B_84)
      | ~ r1_xboole_0(k1_tarski(A_83),B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_85,plain,(
    ! [A_83] : ~ r2_hidden(A_83,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_704,plain,(
    ! [B_194] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_194),B_194)
      | k2_relat_1(k1_xboole_0) = B_194 ) ),
    inference(resolution,[status(thm)],[c_641,c_85])).

tff(c_722,plain,(
    ! [B_195] :
      ( r2_hidden('#skF_6'(k1_xboole_0,B_195),B_195)
      | k1_xboole_0 = B_195 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_704])).

tff(c_24,plain,(
    ! [A_32] :
      ( r2_hidden('#skF_1'(A_32),A_32)
      | v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_95,plain,(
    ! [A_88] : ~ r2_hidden(A_88,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_2,c_80])).

tff(c_100,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_24,c_95])).

tff(c_259,plain,(
    ! [A_127,B_128,C_129] :
      ( r2_hidden('#skF_8'(A_127,B_128,C_129),k2_relat_1(C_129))
      | ~ r2_hidden(A_127,k10_relat_1(C_129,B_128))
      | ~ v1_relat_1(C_129) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_274,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_8'(A_127,B_128,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_127,k10_relat_1(k1_xboole_0,B_128))
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_259])).

tff(c_279,plain,(
    ! [A_127,B_128] :
      ( r2_hidden('#skF_8'(A_127,B_128,k1_xboole_0),k1_xboole_0)
      | ~ r2_hidden(A_127,k10_relat_1(k1_xboole_0,B_128)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_100,c_274])).

tff(c_280,plain,(
    ! [A_127,B_128] : ~ r2_hidden(A_127,k10_relat_1(k1_xboole_0,B_128)) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_279])).

tff(c_792,plain,(
    ! [B_128] : k10_relat_1(k1_xboole_0,B_128) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_722,c_280])).

tff(c_50,plain,(
    k10_relat_1(k1_xboole_0,'#skF_9') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_792,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:43:23 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.73/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.41  
% 2.73/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.41  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_tarski > k2_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_6 > #skF_1 > #skF_3 > #skF_9 > #skF_7 > #skF_2 > #skF_8 > #skF_5 > #skF_4
% 2.73/1.41  
% 2.73/1.41  %Foreground sorts:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Background operators:
% 2.73/1.41  
% 2.73/1.41  
% 2.73/1.41  %Foreground operators:
% 2.73/1.41  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.73/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.73/1.41  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.73/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.73/1.41  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.73/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.73/1.41  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.73/1.41  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.73/1.41  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.73/1.41  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.73/1.41  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.73/1.41  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.73/1.41  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.73/1.41  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.73/1.41  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 2.73/1.41  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.73/1.41  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 2.73/1.41  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.73/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.73/1.41  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.73/1.41  tff('#skF_8', type, '#skF_8': ($i * $i * $i) > $i).
% 2.73/1.41  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.73/1.41  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.73/1.41  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.73/1.41  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.73/1.41  
% 2.73/1.42  tff(f_78, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 2.73/1.42  tff(f_64, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 2.73/1.42  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.73/1.42  tff(f_46, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.73/1.42  tff(f_56, axiom, (![A]: (v1_relat_1(A) <=> (![B]: ~(r2_hidden(B, A) & (![C, D]: ~(B = k4_tarski(C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_relat_1)).
% 2.73/1.42  tff(f_75, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 2.73/1.42  tff(f_81, negated_conjecture, ~(![A]: (k10_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t172_relat_1)).
% 2.73/1.42  tff(c_46, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.73/1.42  tff(c_641, plain, (![A_193, B_194]: (r2_hidden(k4_tarski('#skF_5'(A_193, B_194), '#skF_4'(A_193, B_194)), A_193) | r2_hidden('#skF_6'(A_193, B_194), B_194) | k2_relat_1(A_193)=B_194)), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.73/1.42  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.73/1.42  tff(c_80, plain, (![A_83, B_84]: (~r2_hidden(A_83, B_84) | ~r1_xboole_0(k1_tarski(A_83), B_84))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.73/1.42  tff(c_85, plain, (![A_83]: (~r2_hidden(A_83, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_80])).
% 2.73/1.42  tff(c_704, plain, (![B_194]: (r2_hidden('#skF_6'(k1_xboole_0, B_194), B_194) | k2_relat_1(k1_xboole_0)=B_194)), inference(resolution, [status(thm)], [c_641, c_85])).
% 2.73/1.42  tff(c_722, plain, (![B_195]: (r2_hidden('#skF_6'(k1_xboole_0, B_195), B_195) | k1_xboole_0=B_195)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_704])).
% 2.73/1.42  tff(c_24, plain, (![A_32]: (r2_hidden('#skF_1'(A_32), A_32) | v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.73/1.42  tff(c_95, plain, (![A_88]: (~r2_hidden(A_88, k1_xboole_0))), inference(resolution, [status(thm)], [c_2, c_80])).
% 2.73/1.42  tff(c_100, plain, (v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_95])).
% 2.73/1.42  tff(c_259, plain, (![A_127, B_128, C_129]: (r2_hidden('#skF_8'(A_127, B_128, C_129), k2_relat_1(C_129)) | ~r2_hidden(A_127, k10_relat_1(C_129, B_128)) | ~v1_relat_1(C_129))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.73/1.42  tff(c_274, plain, (![A_127, B_128]: (r2_hidden('#skF_8'(A_127, B_128, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_127, k10_relat_1(k1_xboole_0, B_128)) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_259])).
% 2.73/1.42  tff(c_279, plain, (![A_127, B_128]: (r2_hidden('#skF_8'(A_127, B_128, k1_xboole_0), k1_xboole_0) | ~r2_hidden(A_127, k10_relat_1(k1_xboole_0, B_128)))), inference(demodulation, [status(thm), theory('equality')], [c_100, c_274])).
% 2.73/1.42  tff(c_280, plain, (![A_127, B_128]: (~r2_hidden(A_127, k10_relat_1(k1_xboole_0, B_128)))), inference(negUnitSimplification, [status(thm)], [c_85, c_279])).
% 2.73/1.42  tff(c_792, plain, (![B_128]: (k10_relat_1(k1_xboole_0, B_128)=k1_xboole_0)), inference(resolution, [status(thm)], [c_722, c_280])).
% 2.73/1.42  tff(c_50, plain, (k10_relat_1(k1_xboole_0, '#skF_9')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.73/1.42  tff(c_836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_792, c_50])).
% 2.73/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.73/1.42  
% 2.73/1.42  Inference rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Ref     : 1
% 2.73/1.42  #Sup     : 142
% 2.73/1.42  #Fact    : 0
% 2.73/1.42  #Define  : 0
% 2.73/1.42  #Split   : 0
% 2.73/1.42  #Chain   : 0
% 2.73/1.42  #Close   : 0
% 2.73/1.42  
% 2.73/1.42  Ordering : KBO
% 2.73/1.42  
% 2.73/1.42  Simplification rules
% 2.73/1.42  ----------------------
% 2.73/1.42  #Subsume      : 32
% 2.73/1.42  #Demod        : 74
% 2.73/1.42  #Tautology    : 32
% 2.73/1.42  #SimpNegUnit  : 2
% 2.73/1.42  #BackRed      : 21
% 2.73/1.42  
% 2.73/1.42  #Partial instantiations: 0
% 2.73/1.42  #Strategies tried      : 1
% 2.73/1.42  
% 2.73/1.42  Timing (in seconds)
% 2.73/1.42  ----------------------
% 2.73/1.42  Preprocessing        : 0.32
% 2.73/1.42  Parsing              : 0.17
% 2.73/1.42  CNF conversion       : 0.02
% 2.73/1.42  Main loop            : 0.32
% 2.73/1.42  Inferencing          : 0.12
% 2.73/1.42  Reduction            : 0.09
% 2.73/1.42  Demodulation         : 0.06
% 2.73/1.42  BG Simplification    : 0.02
% 2.73/1.42  Subsumption          : 0.07
% 2.73/1.42  Abstraction          : 0.02
% 2.73/1.42  MUC search           : 0.00
% 2.73/1.42  Cooper               : 0.00
% 2.73/1.42  Total                : 0.66
% 2.73/1.42  Index Insertion      : 0.00
% 2.73/1.42  Index Deletion       : 0.00
% 2.73/1.42  Index Matching       : 0.00
% 2.73/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
