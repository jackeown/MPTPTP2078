%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:29 EST 2020

% Result     : Theorem 3.58s
% Output     : CNFRefutation 3.58s
% Verified   : 
% Statistics : Number of formulae       :   39 (  92 expanded)
%              Number of leaves         :   11 (  35 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 252 expanded)
%              Number of equality atoms :   27 (  79 expanded)
%              Maximal formula depth    :    8 (   5 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_37,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,k2_xboole_0(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_xboole_1)).

tff(c_75,plain,(
    ! [A_25,B_26,C_27] :
      ( r2_hidden('#skF_1'(A_25,B_26,C_27),B_26)
      | r2_hidden('#skF_1'(A_25,B_26,C_27),A_25)
      | r2_hidden('#skF_2'(A_25,B_26,C_27),C_27)
      | k2_xboole_0(A_25,B_26) = C_27 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_16,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26,B_26),A_25)
      | r2_hidden('#skF_2'(A_25,B_26,B_26),B_26)
      | k2_xboole_0(A_25,B_26) = B_26 ) ),
    inference(resolution,[status(thm)],[c_75,c_16])).

tff(c_155,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden('#skF_1'(A_30,B_31,C_32),B_31)
      | r2_hidden('#skF_1'(A_30,B_31,C_32),A_30)
      | ~ r2_hidden('#skF_2'(A_30,B_31,C_32),B_31)
      | k2_xboole_0(A_30,B_31) = C_32 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_453,plain,(
    ! [A_53,B_54] :
      ( r2_hidden('#skF_1'(A_53,B_54,B_54),A_53)
      | ~ r2_hidden('#skF_2'(A_53,B_54,B_54),B_54)
      | k2_xboole_0(A_53,B_54) = B_54 ) ),
    inference(resolution,[status(thm)],[c_155,c_8])).

tff(c_464,plain,(
    ! [A_25,B_26] :
      ( r2_hidden('#skF_1'(A_25,B_26,B_26),A_25)
      | k2_xboole_0(A_25,B_26) = B_26 ) ),
    inference(resolution,[status(thm)],[c_108,c_453])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( ~ r2_hidden(D_6,A_1)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_117,plain,(
    ! [B_28,C_29] :
      ( r2_hidden('#skF_2'(B_28,B_28,C_29),C_29)
      | k2_xboole_0(B_28,B_28) = C_29
      | r2_hidden('#skF_1'(B_28,B_28,C_29),B_28) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_18])).

tff(c_137,plain,(
    ! [B_28] :
      ( r2_hidden('#skF_2'(B_28,B_28,B_28),B_28)
      | k2_xboole_0(B_28,B_28) = B_28 ) ),
    inference(resolution,[status(thm)],[c_117,c_16])).

tff(c_10,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),B_2)
      | r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_246,plain,(
    ! [B_38,C_39] :
      ( ~ r2_hidden('#skF_2'(B_38,B_38,C_39),B_38)
      | k2_xboole_0(B_38,B_38) = C_39
      | r2_hidden('#skF_1'(B_38,B_38,C_39),B_38) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_10])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k2_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_316,plain,(
    ! [B_43] :
      ( ~ r2_hidden('#skF_2'(B_43,B_43,B_43),B_43)
      | k2_xboole_0(B_43,B_43) = B_43 ) ),
    inference(resolution,[status(thm)],[c_246,c_12])).

tff(c_336,plain,(
    ! [B_28] : k2_xboole_0(B_28,B_28) = B_28 ),
    inference(resolution,[status(thm)],[c_137,c_316])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | r2_hidden(D_6,k2_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_50,plain,(
    ! [A_22,B_23,C_24] :
      ( ~ r2_hidden('#skF_1'(A_22,B_23,C_24),C_24)
      | r2_hidden('#skF_2'(A_22,B_23,C_24),C_24)
      | k2_xboole_0(A_22,B_23) = C_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_726,plain,(
    ! [A_83,B_84,A_85,B_86] :
      ( r2_hidden('#skF_2'(A_83,B_84,k2_xboole_0(A_85,B_86)),k2_xboole_0(A_85,B_86))
      | k2_xboole_0(A_85,B_86) = k2_xboole_0(A_83,B_84)
      | ~ r2_hidden('#skF_1'(A_83,B_84,k2_xboole_0(A_85,B_86)),B_86) ) ),
    inference(resolution,[status(thm)],[c_4,c_50])).

tff(c_32,plain,(
    ! [A_16,B_17,C_18] :
      ( ~ r2_hidden('#skF_1'(A_16,B_17,C_18),C_18)
      | ~ r2_hidden('#skF_2'(A_16,B_17,C_18),B_17)
      | k2_xboole_0(A_16,B_17) = C_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_39,plain,(
    ! [A_16,B_17,A_1,B_2] :
      ( ~ r2_hidden('#skF_2'(A_16,B_17,k2_xboole_0(A_1,B_2)),B_17)
      | k2_xboole_0(A_16,B_17) = k2_xboole_0(A_1,B_2)
      | ~ r2_hidden('#skF_1'(A_16,B_17,k2_xboole_0(A_1,B_2)),B_2) ) ),
    inference(resolution,[status(thm)],[c_4,c_32])).

tff(c_785,plain,(
    ! [A_89,A_90,B_91] :
      ( k2_xboole_0(A_89,k2_xboole_0(A_90,B_91)) = k2_xboole_0(A_90,B_91)
      | ~ r2_hidden('#skF_1'(A_89,k2_xboole_0(A_90,B_91),k2_xboole_0(A_90,B_91)),B_91) ) ),
    inference(resolution,[status(thm)],[c_726,c_39])).

tff(c_806,plain,(
    ! [A_89,B_28] :
      ( k2_xboole_0(A_89,k2_xboole_0(B_28,B_28)) = k2_xboole_0(B_28,B_28)
      | ~ r2_hidden('#skF_1'(A_89,B_28,k2_xboole_0(B_28,B_28)),B_28) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_785])).

tff(c_922,plain,(
    ! [A_96,B_97] :
      ( k2_xboole_0(A_96,B_97) = B_97
      | ~ r2_hidden('#skF_1'(A_96,B_97,B_97),B_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_336,c_336,c_336,c_806])).

tff(c_1450,plain,(
    ! [A_116,A_117,B_118] :
      ( k2_xboole_0(A_116,k2_xboole_0(A_117,B_118)) = k2_xboole_0(A_117,B_118)
      | ~ r2_hidden('#skF_1'(A_116,k2_xboole_0(A_117,B_118),k2_xboole_0(A_117,B_118)),A_117) ) ),
    inference(resolution,[status(thm)],[c_6,c_922])).

tff(c_1519,plain,(
    ! [A_25,B_118] : k2_xboole_0(A_25,k2_xboole_0(A_25,B_118)) = k2_xboole_0(A_25,B_118) ),
    inference(resolution,[status(thm)],[c_464,c_1450])).

tff(c_20,plain,(
    k2_xboole_0('#skF_3',k2_xboole_0('#skF_3','#skF_4')) != k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1519,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.58/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.59  
% 3.58/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.59  %$ r2_hidden > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 3.58/1.59  
% 3.58/1.59  %Foreground sorts:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Background operators:
% 3.58/1.59  
% 3.58/1.59  
% 3.58/1.59  %Foreground operators:
% 3.58/1.59  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.58/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.58/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.58/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.58/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.58/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.58/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.58/1.59  
% 3.58/1.60  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.58/1.60  tff(f_37, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, k2_xboole_0(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_xboole_1)).
% 3.58/1.60  tff(c_75, plain, (![A_25, B_26, C_27]: (r2_hidden('#skF_1'(A_25, B_26, C_27), B_26) | r2_hidden('#skF_1'(A_25, B_26, C_27), A_25) | r2_hidden('#skF_2'(A_25, B_26, C_27), C_27) | k2_xboole_0(A_25, B_26)=C_27)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_16, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_108, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26, B_26), A_25) | r2_hidden('#skF_2'(A_25, B_26, B_26), B_26) | k2_xboole_0(A_25, B_26)=B_26)), inference(resolution, [status(thm)], [c_75, c_16])).
% 3.58/1.60  tff(c_155, plain, (![A_30, B_31, C_32]: (r2_hidden('#skF_1'(A_30, B_31, C_32), B_31) | r2_hidden('#skF_1'(A_30, B_31, C_32), A_30) | ~r2_hidden('#skF_2'(A_30, B_31, C_32), B_31) | k2_xboole_0(A_30, B_31)=C_32)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_453, plain, (![A_53, B_54]: (r2_hidden('#skF_1'(A_53, B_54, B_54), A_53) | ~r2_hidden('#skF_2'(A_53, B_54, B_54), B_54) | k2_xboole_0(A_53, B_54)=B_54)), inference(resolution, [status(thm)], [c_155, c_8])).
% 3.58/1.60  tff(c_464, plain, (![A_25, B_26]: (r2_hidden('#skF_1'(A_25, B_26, B_26), A_25) | k2_xboole_0(A_25, B_26)=B_26)), inference(resolution, [status(thm)], [c_108, c_453])).
% 3.58/1.60  tff(c_6, plain, (![D_6, A_1, B_2]: (~r2_hidden(D_6, A_1) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_117, plain, (![B_28, C_29]: (r2_hidden('#skF_2'(B_28, B_28, C_29), C_29) | k2_xboole_0(B_28, B_28)=C_29 | r2_hidden('#skF_1'(B_28, B_28, C_29), B_28))), inference(factorization, [status(thm), theory('equality')], [c_18])).
% 3.58/1.60  tff(c_137, plain, (![B_28]: (r2_hidden('#skF_2'(B_28, B_28, B_28), B_28) | k2_xboole_0(B_28, B_28)=B_28)), inference(resolution, [status(thm)], [c_117, c_16])).
% 3.58/1.60  tff(c_10, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), B_2) | r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_246, plain, (![B_38, C_39]: (~r2_hidden('#skF_2'(B_38, B_38, C_39), B_38) | k2_xboole_0(B_38, B_38)=C_39 | r2_hidden('#skF_1'(B_38, B_38, C_39), B_38))), inference(factorization, [status(thm), theory('equality')], [c_10])).
% 3.58/1.60  tff(c_12, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k2_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_316, plain, (![B_43]: (~r2_hidden('#skF_2'(B_43, B_43, B_43), B_43) | k2_xboole_0(B_43, B_43)=B_43)), inference(resolution, [status(thm)], [c_246, c_12])).
% 3.58/1.60  tff(c_336, plain, (![B_28]: (k2_xboole_0(B_28, B_28)=B_28)), inference(resolution, [status(thm)], [c_137, c_316])).
% 3.58/1.60  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | r2_hidden(D_6, k2_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_50, plain, (![A_22, B_23, C_24]: (~r2_hidden('#skF_1'(A_22, B_23, C_24), C_24) | r2_hidden('#skF_2'(A_22, B_23, C_24), C_24) | k2_xboole_0(A_22, B_23)=C_24)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_726, plain, (![A_83, B_84, A_85, B_86]: (r2_hidden('#skF_2'(A_83, B_84, k2_xboole_0(A_85, B_86)), k2_xboole_0(A_85, B_86)) | k2_xboole_0(A_85, B_86)=k2_xboole_0(A_83, B_84) | ~r2_hidden('#skF_1'(A_83, B_84, k2_xboole_0(A_85, B_86)), B_86))), inference(resolution, [status(thm)], [c_4, c_50])).
% 3.58/1.60  tff(c_32, plain, (![A_16, B_17, C_18]: (~r2_hidden('#skF_1'(A_16, B_17, C_18), C_18) | ~r2_hidden('#skF_2'(A_16, B_17, C_18), B_17) | k2_xboole_0(A_16, B_17)=C_18)), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.58/1.60  tff(c_39, plain, (![A_16, B_17, A_1, B_2]: (~r2_hidden('#skF_2'(A_16, B_17, k2_xboole_0(A_1, B_2)), B_17) | k2_xboole_0(A_16, B_17)=k2_xboole_0(A_1, B_2) | ~r2_hidden('#skF_1'(A_16, B_17, k2_xboole_0(A_1, B_2)), B_2))), inference(resolution, [status(thm)], [c_4, c_32])).
% 3.58/1.60  tff(c_785, plain, (![A_89, A_90, B_91]: (k2_xboole_0(A_89, k2_xboole_0(A_90, B_91))=k2_xboole_0(A_90, B_91) | ~r2_hidden('#skF_1'(A_89, k2_xboole_0(A_90, B_91), k2_xboole_0(A_90, B_91)), B_91))), inference(resolution, [status(thm)], [c_726, c_39])).
% 3.58/1.60  tff(c_806, plain, (![A_89, B_28]: (k2_xboole_0(A_89, k2_xboole_0(B_28, B_28))=k2_xboole_0(B_28, B_28) | ~r2_hidden('#skF_1'(A_89, B_28, k2_xboole_0(B_28, B_28)), B_28))), inference(superposition, [status(thm), theory('equality')], [c_336, c_785])).
% 3.58/1.60  tff(c_922, plain, (![A_96, B_97]: (k2_xboole_0(A_96, B_97)=B_97 | ~r2_hidden('#skF_1'(A_96, B_97, B_97), B_97))), inference(demodulation, [status(thm), theory('equality')], [c_336, c_336, c_336, c_806])).
% 3.58/1.60  tff(c_1450, plain, (![A_116, A_117, B_118]: (k2_xboole_0(A_116, k2_xboole_0(A_117, B_118))=k2_xboole_0(A_117, B_118) | ~r2_hidden('#skF_1'(A_116, k2_xboole_0(A_117, B_118), k2_xboole_0(A_117, B_118)), A_117))), inference(resolution, [status(thm)], [c_6, c_922])).
% 3.58/1.60  tff(c_1519, plain, (![A_25, B_118]: (k2_xboole_0(A_25, k2_xboole_0(A_25, B_118))=k2_xboole_0(A_25, B_118))), inference(resolution, [status(thm)], [c_464, c_1450])).
% 3.58/1.60  tff(c_20, plain, (k2_xboole_0('#skF_3', k2_xboole_0('#skF_3', '#skF_4'))!=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.58/1.60  tff(c_1638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1519, c_20])).
% 3.58/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.58/1.60  
% 3.58/1.60  Inference rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Ref     : 0
% 3.58/1.60  #Sup     : 324
% 3.58/1.60  #Fact    : 10
% 3.58/1.60  #Define  : 0
% 3.58/1.60  #Split   : 0
% 3.58/1.60  #Chain   : 0
% 3.58/1.60  #Close   : 0
% 3.58/1.60  
% 3.58/1.60  Ordering : KBO
% 3.58/1.60  
% 3.58/1.60  Simplification rules
% 3.58/1.60  ----------------------
% 3.58/1.60  #Subsume      : 97
% 3.58/1.60  #Demod        : 354
% 3.58/1.60  #Tautology    : 101
% 3.58/1.61  #SimpNegUnit  : 0
% 3.58/1.61  #BackRed      : 6
% 3.58/1.61  
% 3.58/1.61  #Partial instantiations: 0
% 3.58/1.61  #Strategies tried      : 1
% 3.58/1.61  
% 3.58/1.61  Timing (in seconds)
% 3.58/1.61  ----------------------
% 3.58/1.61  Preprocessing        : 0.26
% 3.58/1.61  Parsing              : 0.14
% 3.58/1.61  CNF conversion       : 0.02
% 3.58/1.61  Main loop            : 0.53
% 3.58/1.61  Inferencing          : 0.23
% 3.58/1.61  Reduction            : 0.12
% 3.58/1.61  Demodulation         : 0.08
% 3.58/1.61  BG Simplification    : 0.02
% 3.58/1.61  Subsumption          : 0.12
% 3.58/1.61  Abstraction          : 0.04
% 3.58/1.61  MUC search           : 0.00
% 3.58/1.61  Cooper               : 0.00
% 3.58/1.61  Total                : 0.82
% 3.58/1.61  Index Insertion      : 0.00
% 3.58/1.61  Index Deletion       : 0.00
% 3.58/1.61  Index Matching       : 0.00
% 3.58/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
