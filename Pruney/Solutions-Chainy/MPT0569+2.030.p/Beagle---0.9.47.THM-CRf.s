%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:01:39 EST 2020

% Result     : Theorem 7.69s
% Output     : CNFRefutation 7.78s
% Verified   : 
% Statistics : Number of formulae       :   59 (  79 expanded)
%              Number of leaves         :   27 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   89 ( 147 expanded)
%              Number of equality atoms :    9 (  22 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_relat_1(B)
       => ( k10_relat_1(B,A) = k1_xboole_0
        <=> r1_xboole_0(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( r2_hidden(A,k10_relat_1(C,B))
      <=> ? [D] :
            ( r2_hidden(D,k2_relat_1(C))
            & r2_hidden(k4_tarski(A,D),C)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t166_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_53,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( B = k2_relat_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> ? [D] : r2_hidden(k4_tarski(D,C),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_relat_1)).

tff(c_36,plain,
    ( ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8')
    | k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_58,plain,(
    k10_relat_1('#skF_9','#skF_8') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_34,plain,(
    v1_relat_1('#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_28,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_7'(A_30,B_31,C_32),B_31)
      | ~ r2_hidden(A_30,k10_relat_1(C_32,B_31))
      | ~ v1_relat_1(C_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_311,plain,(
    ! [A_75,B_76,C_77] :
      ( r2_hidden('#skF_7'(A_75,B_76,C_77),k2_relat_1(C_77))
      | ~ r2_hidden(A_75,k10_relat_1(C_77,B_76))
      | ~ v1_relat_1(C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_42,plain,
    ( k10_relat_1('#skF_9','#skF_8') = k1_xboole_0
    | r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_66,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_42])).

tff(c_75,plain,(
    ! [A_49,B_50,C_51] :
      ( ~ r1_xboole_0(A_49,B_50)
      | ~ r2_hidden(C_51,B_50)
      | ~ r2_hidden(C_51,A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82,plain,(
    ! [C_51] :
      ( ~ r2_hidden(C_51,'#skF_8')
      | ~ r2_hidden(C_51,k2_relat_1('#skF_9')) ) ),
    inference(resolution,[status(thm)],[c_66,c_75])).

tff(c_319,plain,(
    ! [A_75,B_76] :
      ( ~ r2_hidden('#skF_7'(A_75,B_76,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_75,k10_relat_1('#skF_9',B_76))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_311,c_82])).

tff(c_613,plain,(
    ! [A_100,B_101] :
      ( ~ r2_hidden('#skF_7'(A_100,B_101,'#skF_9'),'#skF_8')
      | ~ r2_hidden(A_100,k10_relat_1('#skF_9',B_101)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_319])).

tff(c_617,plain,(
    ! [A_30] :
      ( ~ r2_hidden(A_30,k10_relat_1('#skF_9','#skF_8'))
      | ~ v1_relat_1('#skF_9') ) ),
    inference(resolution,[status(thm)],[c_28,c_613])).

tff(c_621,plain,(
    ! [A_102] : ~ r2_hidden(A_102,k10_relat_1('#skF_9','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_617])).

tff(c_645,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_621])).

tff(c_654,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_645])).

tff(c_655,plain,(
    ~ r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ! [A_8] : r1_xboole_0(A_8,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_45,plain,(
    ! [A_38,B_39] :
      ( ~ r2_hidden(A_38,B_39)
      | ~ r1_xboole_0(k1_tarski(A_38),B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_50,plain,(
    ! [A_38] : ~ r2_hidden(A_38,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_45])).

tff(c_656,plain,(
    k10_relat_1('#skF_9','#skF_8') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_14,plain,(
    ! [A_11,C_26] :
      ( r2_hidden(k4_tarski('#skF_6'(A_11,k2_relat_1(A_11),C_26),C_26),A_11)
      | ~ r2_hidden(C_26,k2_relat_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1320,plain,(
    ! [A_176,C_177,B_178,D_179] :
      ( r2_hidden(A_176,k10_relat_1(C_177,B_178))
      | ~ r2_hidden(D_179,B_178)
      | ~ r2_hidden(k4_tarski(A_176,D_179),C_177)
      | ~ r2_hidden(D_179,k2_relat_1(C_177))
      | ~ v1_relat_1(C_177) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2411,plain,(
    ! [A_244,C_245,B_246,A_247] :
      ( r2_hidden(A_244,k10_relat_1(C_245,B_246))
      | ~ r2_hidden(k4_tarski(A_244,'#skF_1'(A_247,B_246)),C_245)
      | ~ r2_hidden('#skF_1'(A_247,B_246),k2_relat_1(C_245))
      | ~ v1_relat_1(C_245)
      | r1_xboole_0(A_247,B_246) ) ),
    inference(resolution,[status(thm)],[c_4,c_1320])).

tff(c_7962,plain,(
    ! [A_444,A_445,B_446] :
      ( r2_hidden('#skF_6'(A_444,k2_relat_1(A_444),'#skF_1'(A_445,B_446)),k10_relat_1(A_444,B_446))
      | ~ v1_relat_1(A_444)
      | r1_xboole_0(A_445,B_446)
      | ~ r2_hidden('#skF_1'(A_445,B_446),k2_relat_1(A_444)) ) ),
    inference(resolution,[status(thm)],[c_14,c_2411])).

tff(c_8071,plain,(
    ! [A_445] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'(A_445,'#skF_8')),k1_xboole_0)
      | ~ v1_relat_1('#skF_9')
      | r1_xboole_0(A_445,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_445,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_7962])).

tff(c_8090,plain,(
    ! [A_445] :
      ( r2_hidden('#skF_6'('#skF_9',k2_relat_1('#skF_9'),'#skF_1'(A_445,'#skF_8')),k1_xboole_0)
      | r1_xboole_0(A_445,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_445,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_8071])).

tff(c_8092,plain,(
    ! [A_447] :
      ( r1_xboole_0(A_447,'#skF_8')
      | ~ r2_hidden('#skF_1'(A_447,'#skF_8'),k2_relat_1('#skF_9')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_8090])).

tff(c_8096,plain,(
    r1_xboole_0(k2_relat_1('#skF_9'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_6,c_8092])).

tff(c_8100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_655,c_655,c_8096])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.01/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:18:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.69/2.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.60  
% 7.69/2.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.69/2.60  %$ r2_hidden > r1_xboole_0 > v1_relat_1 > k4_tarski > k10_relat_1 > #nlpp > k2_relat_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_6 > #skF_3 > #skF_9 > #skF_7 > #skF_8 > #skF_1 > #skF_5 > #skF_4
% 7.69/2.60  
% 7.69/2.60  %Foreground sorts:
% 7.69/2.60  
% 7.69/2.60  
% 7.69/2.60  %Background operators:
% 7.69/2.60  
% 7.69/2.60  
% 7.69/2.60  %Foreground operators:
% 7.69/2.60  tff('#skF_2', type, '#skF_2': $i > $i).
% 7.69/2.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.69/2.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.69/2.60  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 7.69/2.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.69/2.60  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.69/2.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.69/2.60  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 7.69/2.60  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 7.69/2.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.69/2.60  tff('#skF_9', type, '#skF_9': $i).
% 7.69/2.60  tff('#skF_7', type, '#skF_7': ($i * $i * $i) > $i).
% 7.69/2.60  tff('#skF_8', type, '#skF_8': $i).
% 7.69/2.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.69/2.60  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 7.69/2.60  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 7.69/2.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.69/2.60  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.69/2.60  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.69/2.60  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.69/2.60  
% 7.78/2.61  tff(f_84, negated_conjecture, ~(![A, B]: (v1_relat_1(B) => ((k10_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t173_relat_1)).
% 7.78/2.61  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 7.78/2.61  tff(f_77, axiom, (![A, B, C]: (v1_relat_1(C) => (r2_hidden(A, k10_relat_1(C, B)) <=> (?[D]: ((r2_hidden(D, k2_relat_1(C)) & r2_hidden(k4_tarski(A, D), C)) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t166_relat_1)).
% 7.78/2.61  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.78/2.61  tff(f_53, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.78/2.61  tff(f_58, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 7.78/2.61  tff(f_66, axiom, (![A, B]: ((B = k2_relat_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (?[D]: r2_hidden(k4_tarski(D, C), A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_relat_1)).
% 7.78/2.61  tff(c_36, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8') | k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.78/2.61  tff(c_58, plain, (k10_relat_1('#skF_9', '#skF_8')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 7.78/2.61  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.78/2.61  tff(c_34, plain, (v1_relat_1('#skF_9')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.78/2.61  tff(c_28, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_7'(A_30, B_31, C_32), B_31) | ~r2_hidden(A_30, k10_relat_1(C_32, B_31)) | ~v1_relat_1(C_32))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.78/2.61  tff(c_311, plain, (![A_75, B_76, C_77]: (r2_hidden('#skF_7'(A_75, B_76, C_77), k2_relat_1(C_77)) | ~r2_hidden(A_75, k10_relat_1(C_77, B_76)) | ~v1_relat_1(C_77))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.78/2.61  tff(c_42, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0 | r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.78/2.61  tff(c_66, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_58, c_42])).
% 7.78/2.61  tff(c_75, plain, (![A_49, B_50, C_51]: (~r1_xboole_0(A_49, B_50) | ~r2_hidden(C_51, B_50) | ~r2_hidden(C_51, A_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.78/2.61  tff(c_82, plain, (![C_51]: (~r2_hidden(C_51, '#skF_8') | ~r2_hidden(C_51, k2_relat_1('#skF_9')))), inference(resolution, [status(thm)], [c_66, c_75])).
% 7.78/2.61  tff(c_319, plain, (![A_75, B_76]: (~r2_hidden('#skF_7'(A_75, B_76, '#skF_9'), '#skF_8') | ~r2_hidden(A_75, k10_relat_1('#skF_9', B_76)) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_311, c_82])).
% 7.78/2.61  tff(c_613, plain, (![A_100, B_101]: (~r2_hidden('#skF_7'(A_100, B_101, '#skF_9'), '#skF_8') | ~r2_hidden(A_100, k10_relat_1('#skF_9', B_101)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_319])).
% 7.78/2.61  tff(c_617, plain, (![A_30]: (~r2_hidden(A_30, k10_relat_1('#skF_9', '#skF_8')) | ~v1_relat_1('#skF_9'))), inference(resolution, [status(thm)], [c_28, c_613])).
% 7.78/2.61  tff(c_621, plain, (![A_102]: (~r2_hidden(A_102, k10_relat_1('#skF_9', '#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_617])).
% 7.78/2.61  tff(c_645, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_621])).
% 7.78/2.61  tff(c_654, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_645])).
% 7.78/2.61  tff(c_655, plain, (~r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(splitRight, [status(thm)], [c_36])).
% 7.78/2.61  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.78/2.61  tff(c_10, plain, (![A_8]: (r1_xboole_0(A_8, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.78/2.61  tff(c_45, plain, (![A_38, B_39]: (~r2_hidden(A_38, B_39) | ~r1_xboole_0(k1_tarski(A_38), B_39))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.78/2.61  tff(c_50, plain, (![A_38]: (~r2_hidden(A_38, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_45])).
% 7.78/2.61  tff(c_656, plain, (k10_relat_1('#skF_9', '#skF_8')=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 7.78/2.61  tff(c_14, plain, (![A_11, C_26]: (r2_hidden(k4_tarski('#skF_6'(A_11, k2_relat_1(A_11), C_26), C_26), A_11) | ~r2_hidden(C_26, k2_relat_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.78/2.61  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.78/2.61  tff(c_1320, plain, (![A_176, C_177, B_178, D_179]: (r2_hidden(A_176, k10_relat_1(C_177, B_178)) | ~r2_hidden(D_179, B_178) | ~r2_hidden(k4_tarski(A_176, D_179), C_177) | ~r2_hidden(D_179, k2_relat_1(C_177)) | ~v1_relat_1(C_177))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.78/2.61  tff(c_2411, plain, (![A_244, C_245, B_246, A_247]: (r2_hidden(A_244, k10_relat_1(C_245, B_246)) | ~r2_hidden(k4_tarski(A_244, '#skF_1'(A_247, B_246)), C_245) | ~r2_hidden('#skF_1'(A_247, B_246), k2_relat_1(C_245)) | ~v1_relat_1(C_245) | r1_xboole_0(A_247, B_246))), inference(resolution, [status(thm)], [c_4, c_1320])).
% 7.78/2.61  tff(c_7962, plain, (![A_444, A_445, B_446]: (r2_hidden('#skF_6'(A_444, k2_relat_1(A_444), '#skF_1'(A_445, B_446)), k10_relat_1(A_444, B_446)) | ~v1_relat_1(A_444) | r1_xboole_0(A_445, B_446) | ~r2_hidden('#skF_1'(A_445, B_446), k2_relat_1(A_444)))), inference(resolution, [status(thm)], [c_14, c_2411])).
% 7.78/2.61  tff(c_8071, plain, (![A_445]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'(A_445, '#skF_8')), k1_xboole_0) | ~v1_relat_1('#skF_9') | r1_xboole_0(A_445, '#skF_8') | ~r2_hidden('#skF_1'(A_445, '#skF_8'), k2_relat_1('#skF_9')))), inference(superposition, [status(thm), theory('equality')], [c_656, c_7962])).
% 7.78/2.61  tff(c_8090, plain, (![A_445]: (r2_hidden('#skF_6'('#skF_9', k2_relat_1('#skF_9'), '#skF_1'(A_445, '#skF_8')), k1_xboole_0) | r1_xboole_0(A_445, '#skF_8') | ~r2_hidden('#skF_1'(A_445, '#skF_8'), k2_relat_1('#skF_9')))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_8071])).
% 7.78/2.61  tff(c_8092, plain, (![A_447]: (r1_xboole_0(A_447, '#skF_8') | ~r2_hidden('#skF_1'(A_447, '#skF_8'), k2_relat_1('#skF_9')))), inference(negUnitSimplification, [status(thm)], [c_50, c_8090])).
% 7.78/2.61  tff(c_8096, plain, (r1_xboole_0(k2_relat_1('#skF_9'), '#skF_8')), inference(resolution, [status(thm)], [c_6, c_8092])).
% 7.78/2.61  tff(c_8100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_655, c_655, c_8096])).
% 7.78/2.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.78/2.61  
% 7.78/2.61  Inference rules
% 7.78/2.61  ----------------------
% 7.78/2.61  #Ref     : 0
% 7.78/2.61  #Sup     : 1938
% 7.78/2.61  #Fact    : 0
% 7.78/2.61  #Define  : 0
% 7.78/2.61  #Split   : 9
% 7.78/2.61  #Chain   : 0
% 7.78/2.62  #Close   : 0
% 7.78/2.62  
% 7.78/2.62  Ordering : KBO
% 7.78/2.62  
% 7.78/2.62  Simplification rules
% 7.78/2.62  ----------------------
% 7.78/2.62  #Subsume      : 945
% 7.78/2.62  #Demod        : 1162
% 7.78/2.62  #Tautology    : 392
% 7.78/2.62  #SimpNegUnit  : 112
% 7.78/2.62  #BackRed      : 2
% 7.78/2.62  
% 7.78/2.62  #Partial instantiations: 0
% 7.78/2.62  #Strategies tried      : 1
% 7.78/2.62  
% 7.78/2.62  Timing (in seconds)
% 7.78/2.62  ----------------------
% 7.78/2.62  Preprocessing        : 0.28
% 7.78/2.62  Parsing              : 0.15
% 7.78/2.62  CNF conversion       : 0.02
% 7.78/2.62  Main loop            : 1.59
% 7.78/2.62  Inferencing          : 0.46
% 7.78/2.62  Reduction            : 0.36
% 7.78/2.62  Demodulation         : 0.24
% 7.78/2.62  BG Simplification    : 0.04
% 7.78/2.62  Subsumption          : 0.65
% 7.78/2.62  Abstraction          : 0.06
% 7.78/2.62  MUC search           : 0.00
% 7.78/2.62  Cooper               : 0.00
% 7.78/2.62  Total                : 1.89
% 7.78/2.62  Index Insertion      : 0.00
% 7.78/2.62  Index Deletion       : 0.00
% 7.78/2.62  Index Matching       : 0.00
% 7.78/2.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
