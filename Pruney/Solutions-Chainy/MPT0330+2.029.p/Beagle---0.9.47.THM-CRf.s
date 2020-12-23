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
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 9.45s
% Output     : CNFRefutation 9.65s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 117 expanded)
%              Number of leaves         :   24 (  51 expanded)
%              Depth                    :    7
%              Number of atoms          :   85 ( 216 expanded)
%              Number of equality atoms :    6 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_157,plain,(
    ! [A_59,C_60,B_61] :
      ( r1_tarski(k2_xboole_0(A_59,C_60),B_61)
      | ~ r1_tarski(C_60,B_61)
      | ~ r1_tarski(A_59,B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_55,plain,(
    ! [B_38,A_39] :
      ( B_38 = A_39
      | ~ r1_tarski(B_38,A_39)
      | ~ r1_tarski(A_39,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_68,plain,(
    ! [A_9,B_10] :
      ( k2_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(k2_xboole_0(A_9,B_10),A_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_55])).

tff(c_161,plain,(
    ! [B_61,C_60] :
      ( k2_xboole_0(B_61,C_60) = B_61
      | ~ r1_tarski(C_60,B_61)
      | ~ r1_tarski(B_61,B_61) ) ),
    inference(resolution,[status(thm)],[c_157,c_68])).

tff(c_175,plain,(
    ! [B_62,C_63] :
      ( k2_xboole_0(B_62,C_63) = B_62
      | ~ r1_tarski(C_63,B_62) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_161])).

tff(c_219,plain,(
    ! [B_2] : k2_xboole_0(B_2,B_2) = B_2 ),
    inference(resolution,[status(thm)],[c_6,c_175])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_74,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_347,plain,(
    ! [A_71,C_72,B_73,A_74] :
      ( r1_tarski(A_71,k2_xboole_0(C_72,B_73))
      | ~ r1_tarski(A_71,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(resolution,[status(thm)],[c_8,c_74])).

tff(c_522,plain,(
    ! [A_83,C_84,B_85,B_86] :
      ( r1_tarski(A_83,k2_xboole_0(C_84,B_85))
      | ~ r1_tarski(k2_xboole_0(A_83,B_86),B_85) ) ),
    inference(resolution,[status(thm)],[c_12,c_347])).

tff(c_610,plain,(
    ! [A_90,C_91,B_92] : r1_tarski(A_90,k2_xboole_0(C_91,k2_xboole_0(A_90,B_92))) ),
    inference(resolution,[status(thm)],[c_6,c_522])).

tff(c_645,plain,(
    ! [B_2,C_91] : r1_tarski(B_2,k2_xboole_0(C_91,B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_219,c_610])).

tff(c_30,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_150,plain,(
    ! [A_56,C_57,B_58] :
      ( r1_tarski(k2_zfmisc_1(A_56,C_57),k2_zfmisc_1(B_58,C_57))
      | ~ r1_tarski(A_56,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_10,plain,(
    ! [A_6,C_8,B_7] :
      ( r1_tarski(A_6,C_8)
      | ~ r1_tarski(B_7,C_8)
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1069,plain,(
    ! [A_110,B_111,C_112,A_113] :
      ( r1_tarski(A_110,k2_zfmisc_1(B_111,C_112))
      | ~ r1_tarski(A_110,k2_zfmisc_1(A_113,C_112))
      | ~ r1_tarski(A_113,B_111) ) ),
    inference(resolution,[status(thm)],[c_150,c_10])).

tff(c_1094,plain,(
    ! [B_111] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_111,'#skF_6'))
      | ~ r1_tarski('#skF_5',B_111) ) ),
    inference(resolution,[status(thm)],[c_30,c_1069])).

tff(c_141,plain,(
    ! [C_53,A_54,B_55] :
      ( r1_tarski(k2_zfmisc_1(C_53,A_54),k2_zfmisc_1(C_53,B_55))
      | ~ r1_tarski(A_54,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_9932,plain,(
    ! [A_306,C_307,B_308,A_309] :
      ( r1_tarski(A_306,k2_zfmisc_1(C_307,B_308))
      | ~ r1_tarski(A_306,k2_zfmisc_1(C_307,A_309))
      | ~ r1_tarski(A_309,B_308) ) ),
    inference(resolution,[status(thm)],[c_141,c_10])).

tff(c_15428,plain,(
    ! [B_460,B_461] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_460,B_461))
      | ~ r1_tarski('#skF_6',B_461)
      | ~ r1_tarski('#skF_5',B_460) ) ),
    inference(resolution,[status(thm)],[c_1094,c_9932])).

tff(c_32,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1093,plain,(
    ! [B_111] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_111,'#skF_4'))
      | ~ r1_tarski('#skF_3',B_111) ) ),
    inference(resolution,[status(thm)],[c_32,c_1069])).

tff(c_1250,plain,(
    ! [A_122,C_123,B_124,A_125] :
      ( r1_tarski(A_122,k2_zfmisc_1(C_123,B_124))
      | ~ r1_tarski(A_122,k2_zfmisc_1(C_123,A_125))
      | ~ r1_tarski(A_125,B_124) ) ),
    inference(resolution,[status(thm)],[c_141,c_10])).

tff(c_9862,plain,(
    ! [B_304,B_305] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_304,B_305))
      | ~ r1_tarski('#skF_4',B_305)
      | ~ r1_tarski('#skF_3',B_304) ) ),
    inference(resolution,[status(thm)],[c_1093,c_1250])).

tff(c_28,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_172,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_157,c_28])).

tff(c_1131,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_172])).

tff(c_9886,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_9862,c_1131])).

tff(c_9912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_12,c_9886])).

tff(c_9913,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_172])).

tff(c_15442,plain,
    ( ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_15428,c_9913])).

tff(c_15463,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_645,c_15442])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:18:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.45/3.46  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.46  
% 9.45/3.46  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.45/3.47  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.45/3.47  
% 9.45/3.47  %Foreground sorts:
% 9.45/3.47  
% 9.45/3.47  
% 9.45/3.47  %Background operators:
% 9.45/3.47  
% 9.45/3.47  
% 9.45/3.47  %Foreground operators:
% 9.45/3.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.45/3.47  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.45/3.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.45/3.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.45/3.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.45/3.47  tff('#skF_5', type, '#skF_5': $i).
% 9.45/3.47  tff('#skF_6', type, '#skF_6': $i).
% 9.45/3.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.45/3.47  tff('#skF_2', type, '#skF_2': $i).
% 9.45/3.47  tff('#skF_3', type, '#skF_3': $i).
% 9.45/3.47  tff('#skF_1', type, '#skF_1': $i).
% 9.45/3.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.45/3.47  tff(k3_tarski, type, k3_tarski: $i > $i).
% 9.45/3.47  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.45/3.47  tff('#skF_4', type, '#skF_4': $i).
% 9.45/3.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.45/3.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.45/3.47  
% 9.65/3.48  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.65/3.48  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 9.65/3.48  tff(f_43, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 9.65/3.48  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 9.65/3.48  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 9.65/3.48  tff(f_70, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 9.65/3.48  tff(f_63, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 9.65/3.48  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.65/3.48  tff(c_157, plain, (![A_59, C_60, B_61]: (r1_tarski(k2_xboole_0(A_59, C_60), B_61) | ~r1_tarski(C_60, B_61) | ~r1_tarski(A_59, B_61))), inference(cnfTransformation, [status(thm)], [f_49])).
% 9.65/3.48  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 9.65/3.48  tff(c_55, plain, (![B_38, A_39]: (B_38=A_39 | ~r1_tarski(B_38, A_39) | ~r1_tarski(A_39, B_38))), inference(cnfTransformation, [status(thm)], [f_31])).
% 9.65/3.48  tff(c_68, plain, (![A_9, B_10]: (k2_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(k2_xboole_0(A_9, B_10), A_9))), inference(resolution, [status(thm)], [c_12, c_55])).
% 9.65/3.48  tff(c_161, plain, (![B_61, C_60]: (k2_xboole_0(B_61, C_60)=B_61 | ~r1_tarski(C_60, B_61) | ~r1_tarski(B_61, B_61))), inference(resolution, [status(thm)], [c_157, c_68])).
% 9.65/3.48  tff(c_175, plain, (![B_62, C_63]: (k2_xboole_0(B_62, C_63)=B_62 | ~r1_tarski(C_63, B_62))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_161])).
% 9.65/3.48  tff(c_219, plain, (![B_2]: (k2_xboole_0(B_2, B_2)=B_2)), inference(resolution, [status(thm)], [c_6, c_175])).
% 9.65/3.48  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 9.65/3.48  tff(c_74, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.65/3.48  tff(c_347, plain, (![A_71, C_72, B_73, A_74]: (r1_tarski(A_71, k2_xboole_0(C_72, B_73)) | ~r1_tarski(A_71, A_74) | ~r1_tarski(A_74, B_73))), inference(resolution, [status(thm)], [c_8, c_74])).
% 9.65/3.48  tff(c_522, plain, (![A_83, C_84, B_85, B_86]: (r1_tarski(A_83, k2_xboole_0(C_84, B_85)) | ~r1_tarski(k2_xboole_0(A_83, B_86), B_85))), inference(resolution, [status(thm)], [c_12, c_347])).
% 9.65/3.48  tff(c_610, plain, (![A_90, C_91, B_92]: (r1_tarski(A_90, k2_xboole_0(C_91, k2_xboole_0(A_90, B_92))))), inference(resolution, [status(thm)], [c_6, c_522])).
% 9.65/3.48  tff(c_645, plain, (![B_2, C_91]: (r1_tarski(B_2, k2_xboole_0(C_91, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_219, c_610])).
% 9.65/3.48  tff(c_30, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.65/3.48  tff(c_150, plain, (![A_56, C_57, B_58]: (r1_tarski(k2_zfmisc_1(A_56, C_57), k2_zfmisc_1(B_58, C_57)) | ~r1_tarski(A_56, B_58))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.65/3.48  tff(c_10, plain, (![A_6, C_8, B_7]: (r1_tarski(A_6, C_8) | ~r1_tarski(B_7, C_8) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_41])).
% 9.65/3.48  tff(c_1069, plain, (![A_110, B_111, C_112, A_113]: (r1_tarski(A_110, k2_zfmisc_1(B_111, C_112)) | ~r1_tarski(A_110, k2_zfmisc_1(A_113, C_112)) | ~r1_tarski(A_113, B_111))), inference(resolution, [status(thm)], [c_150, c_10])).
% 9.65/3.48  tff(c_1094, plain, (![B_111]: (r1_tarski('#skF_2', k2_zfmisc_1(B_111, '#skF_6')) | ~r1_tarski('#skF_5', B_111))), inference(resolution, [status(thm)], [c_30, c_1069])).
% 9.65/3.48  tff(c_141, plain, (![C_53, A_54, B_55]: (r1_tarski(k2_zfmisc_1(C_53, A_54), k2_zfmisc_1(C_53, B_55)) | ~r1_tarski(A_54, B_55))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.65/3.48  tff(c_9932, plain, (![A_306, C_307, B_308, A_309]: (r1_tarski(A_306, k2_zfmisc_1(C_307, B_308)) | ~r1_tarski(A_306, k2_zfmisc_1(C_307, A_309)) | ~r1_tarski(A_309, B_308))), inference(resolution, [status(thm)], [c_141, c_10])).
% 9.65/3.48  tff(c_15428, plain, (![B_460, B_461]: (r1_tarski('#skF_2', k2_zfmisc_1(B_460, B_461)) | ~r1_tarski('#skF_6', B_461) | ~r1_tarski('#skF_5', B_460))), inference(resolution, [status(thm)], [c_1094, c_9932])).
% 9.65/3.48  tff(c_32, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.65/3.48  tff(c_1093, plain, (![B_111]: (r1_tarski('#skF_1', k2_zfmisc_1(B_111, '#skF_4')) | ~r1_tarski('#skF_3', B_111))), inference(resolution, [status(thm)], [c_32, c_1069])).
% 9.65/3.48  tff(c_1250, plain, (![A_122, C_123, B_124, A_125]: (r1_tarski(A_122, k2_zfmisc_1(C_123, B_124)) | ~r1_tarski(A_122, k2_zfmisc_1(C_123, A_125)) | ~r1_tarski(A_125, B_124))), inference(resolution, [status(thm)], [c_141, c_10])).
% 9.65/3.48  tff(c_9862, plain, (![B_304, B_305]: (r1_tarski('#skF_1', k2_zfmisc_1(B_304, B_305)) | ~r1_tarski('#skF_4', B_305) | ~r1_tarski('#skF_3', B_304))), inference(resolution, [status(thm)], [c_1093, c_1250])).
% 9.65/3.48  tff(c_28, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 9.65/3.48  tff(c_172, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_157, c_28])).
% 9.65/3.48  tff(c_1131, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_172])).
% 9.65/3.48  tff(c_9886, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_9862, c_1131])).
% 9.65/3.48  tff(c_9912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_12, c_9886])).
% 9.65/3.48  tff(c_9913, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_172])).
% 9.65/3.48  tff(c_15442, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_15428, c_9913])).
% 9.65/3.48  tff(c_15463, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_645, c_645, c_15442])).
% 9.65/3.48  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.65/3.48  
% 9.65/3.48  Inference rules
% 9.65/3.48  ----------------------
% 9.65/3.48  #Ref     : 0
% 9.65/3.48  #Sup     : 4101
% 9.65/3.48  #Fact    : 0
% 9.65/3.48  #Define  : 0
% 9.65/3.48  #Split   : 13
% 9.65/3.48  #Chain   : 0
% 9.65/3.48  #Close   : 0
% 9.65/3.48  
% 9.65/3.48  Ordering : KBO
% 9.65/3.48  
% 9.65/3.48  Simplification rules
% 9.65/3.48  ----------------------
% 9.65/3.48  #Subsume      : 854
% 9.65/3.48  #Demod        : 1221
% 9.65/3.48  #Tautology    : 1021
% 9.65/3.48  #SimpNegUnit  : 0
% 9.65/3.48  #BackRed      : 0
% 9.65/3.48  
% 9.65/3.48  #Partial instantiations: 0
% 9.65/3.48  #Strategies tried      : 1
% 9.65/3.48  
% 9.65/3.48  Timing (in seconds)
% 9.65/3.48  ----------------------
% 9.65/3.48  Preprocessing        : 0.31
% 9.65/3.48  Parsing              : 0.17
% 9.65/3.48  CNF conversion       : 0.02
% 9.65/3.48  Main loop            : 2.39
% 9.65/3.48  Inferencing          : 0.51
% 9.65/3.48  Reduction            : 0.92
% 9.65/3.48  Demodulation         : 0.74
% 9.65/3.48  BG Simplification    : 0.07
% 9.65/3.48  Subsumption          : 0.73
% 9.65/3.48  Abstraction          : 0.11
% 9.65/3.48  MUC search           : 0.00
% 9.65/3.48  Cooper               : 0.00
% 9.65/3.48  Total                : 2.73
% 9.65/3.48  Index Insertion      : 0.00
% 9.65/3.48  Index Deletion       : 0.00
% 9.65/3.48  Index Matching       : 0.00
% 9.65/3.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
