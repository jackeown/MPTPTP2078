%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:58 EST 2020

% Result     : Theorem 3.33s
% Output     : CNFRefutation 3.40s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 117 expanded)
%              Number of leaves         :   30 (  51 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 213 expanded)
%              Number of equality atoms :   22 (  59 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
    <=> ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_83,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_64,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_96,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_62,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_159,plain,(
    ! [A_65,C_66,B_67] :
      ( r2_hidden(k2_mcart_1(A_65),C_66)
      | ~ r2_hidden(A_65,k2_zfmisc_1(B_67,C_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_161,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_62,c_159])).

tff(c_165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_161])).

tff(c_166,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_167,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_66,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_169,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_66])).

tff(c_224,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden(k1_mcart_1(A_94),B_95)
      | ~ r2_hidden(A_94,k2_zfmisc_1(B_95,C_96)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_227,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_62,c_224])).

tff(c_26,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    ! [B_78,C_79,A_80] :
      ( r2_hidden(B_78,C_79)
      | ~ r1_tarski(k2_tarski(A_80,B_78),C_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_206,plain,(
    ! [B_84,A_85] : r2_hidden(B_84,k2_tarski(A_85,B_84)) ),
    inference(resolution,[status(thm)],[c_24,c_188])).

tff(c_209,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_206])).

tff(c_361,plain,(
    ! [A_137,B_138,C_139] :
      ( k4_xboole_0(k2_tarski(A_137,B_138),C_139) = k2_tarski(A_137,B_138)
      | r2_hidden(B_138,C_139)
      | r2_hidden(A_137,C_139) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_874,plain,(
    ! [D_188,C_189,A_190,B_191] :
      ( ~ r2_hidden(D_188,C_189)
      | ~ r2_hidden(D_188,k2_tarski(A_190,B_191))
      | r2_hidden(B_191,C_189)
      | r2_hidden(A_190,C_189) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_361,c_4])).

tff(c_939,plain,(
    ! [A_194,A_195,B_196] :
      ( ~ r2_hidden(A_194,k2_tarski(A_195,B_196))
      | r2_hidden(B_196,k1_tarski(A_194))
      | r2_hidden(A_195,k1_tarski(A_194)) ) ),
    inference(resolution,[status(thm)],[c_209,c_874])).

tff(c_967,plain,
    ( r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3')))
    | r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(resolution,[status(thm)],[c_227,c_939])).

tff(c_972,plain,(
    r2_hidden('#skF_4',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_967])).

tff(c_58,plain,(
    ! [A_31,B_32] : k1_mcart_1(k4_tarski(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_306,plain,(
    ! [A_129,B_130,C_131,D_132] :
      ( r2_hidden(k4_tarski(A_129,B_130),k2_zfmisc_1(C_131,D_132))
      | ~ r2_hidden(B_130,D_132)
      | ~ r2_hidden(A_129,C_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    ! [A_28,B_29,C_30] :
      ( k1_mcart_1(A_28) = B_29
      | ~ r2_hidden(A_28,k2_zfmisc_1(k1_tarski(B_29),C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_320,plain,(
    ! [A_129,B_130,B_29,D_132] :
      ( k1_mcart_1(k4_tarski(A_129,B_130)) = B_29
      | ~ r2_hidden(B_130,D_132)
      | ~ r2_hidden(A_129,k1_tarski(B_29)) ) ),
    inference(resolution,[status(thm)],[c_306,c_56])).

tff(c_328,plain,(
    ! [B_29,A_129,B_130,D_132] :
      ( B_29 = A_129
      | ~ r2_hidden(B_130,D_132)
      | ~ r2_hidden(A_129,k1_tarski(B_29)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_320])).

tff(c_329,plain,(
    ! [B_130,D_132] : ~ r2_hidden(B_130,D_132) ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_346,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_329,c_227])).

tff(c_347,plain,(
    ! [B_29,A_129] :
      ( B_29 = A_129
      | ~ r2_hidden(A_129,k1_tarski(B_29)) ) ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_991,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_972,c_347])).

tff(c_1003,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_169,c_991])).

tff(c_1004,plain,(
    r2_hidden('#skF_5',k1_tarski(k1_mcart_1('#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_967])).

tff(c_1037,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1004,c_347])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_166,c_1037])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.32  % Computer   : n010.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % DateTime   : Tue Dec  1 20:03:29 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.13/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.33/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  
% 3.40/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.55  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 3.40/1.55  
% 3.40/1.55  %Foreground sorts:
% 3.40/1.55  
% 3.40/1.55  
% 3.40/1.55  %Background operators:
% 3.40/1.55  
% 3.40/1.55  
% 3.40/1.55  %Foreground operators:
% 3.40/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.40/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.40/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.40/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.40/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.40/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.40/1.55  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.40/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.40/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.40/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.40/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.40/1.55  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.40/1.55  tff('#skF_3', type, '#skF_3': $i).
% 3.40/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.40/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.40/1.55  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.40/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.40/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.40/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.40/1.55  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.40/1.55  
% 3.40/1.56  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 3.40/1.56  tff(f_73, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.40/1.56  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.40/1.56  tff(f_41, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.40/1.56  tff(f_59, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.40/1.56  tff(f_67, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 3.40/1.56  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.40/1.56  tff(f_83, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.40/1.56  tff(f_53, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.40/1.56  tff(f_79, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 3.40/1.56  tff(c_64, plain, (k1_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.40/1.56  tff(c_96, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_64])).
% 3.40/1.56  tff(c_62, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.40/1.56  tff(c_159, plain, (![A_65, C_66, B_67]: (r2_hidden(k2_mcart_1(A_65), C_66) | ~r2_hidden(A_65, k2_zfmisc_1(B_67, C_66)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.56  tff(c_161, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_62, c_159])).
% 3.40/1.56  tff(c_165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_161])).
% 3.40/1.56  tff(c_166, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_64])).
% 3.40/1.56  tff(c_167, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_64])).
% 3.40/1.56  tff(c_66, plain, (k1_mcart_1('#skF_3')!='#skF_4' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.40/1.56  tff(c_169, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_167, c_66])).
% 3.40/1.56  tff(c_224, plain, (![A_94, B_95, C_96]: (r2_hidden(k1_mcart_1(A_94), B_95) | ~r2_hidden(A_94, k2_zfmisc_1(B_95, C_96)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.40/1.56  tff(c_227, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_62, c_224])).
% 3.40/1.56  tff(c_26, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.40/1.56  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.40/1.56  tff(c_188, plain, (![B_78, C_79, A_80]: (r2_hidden(B_78, C_79) | ~r1_tarski(k2_tarski(A_80, B_78), C_79))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.40/1.56  tff(c_206, plain, (![B_84, A_85]: (r2_hidden(B_84, k2_tarski(A_85, B_84)))), inference(resolution, [status(thm)], [c_24, c_188])).
% 3.40/1.56  tff(c_209, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_206])).
% 3.40/1.56  tff(c_361, plain, (![A_137, B_138, C_139]: (k4_xboole_0(k2_tarski(A_137, B_138), C_139)=k2_tarski(A_137, B_138) | r2_hidden(B_138, C_139) | r2_hidden(A_137, C_139))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.40/1.56  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.40/1.56  tff(c_874, plain, (![D_188, C_189, A_190, B_191]: (~r2_hidden(D_188, C_189) | ~r2_hidden(D_188, k2_tarski(A_190, B_191)) | r2_hidden(B_191, C_189) | r2_hidden(A_190, C_189))), inference(superposition, [status(thm), theory('equality')], [c_361, c_4])).
% 3.40/1.56  tff(c_939, plain, (![A_194, A_195, B_196]: (~r2_hidden(A_194, k2_tarski(A_195, B_196)) | r2_hidden(B_196, k1_tarski(A_194)) | r2_hidden(A_195, k1_tarski(A_194)))), inference(resolution, [status(thm)], [c_209, c_874])).
% 3.40/1.56  tff(c_967, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3'))) | r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(resolution, [status(thm)], [c_227, c_939])).
% 3.40/1.56  tff(c_972, plain, (r2_hidden('#skF_4', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitLeft, [status(thm)], [c_967])).
% 3.40/1.56  tff(c_58, plain, (![A_31, B_32]: (k1_mcart_1(k4_tarski(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.40/1.56  tff(c_306, plain, (![A_129, B_130, C_131, D_132]: (r2_hidden(k4_tarski(A_129, B_130), k2_zfmisc_1(C_131, D_132)) | ~r2_hidden(B_130, D_132) | ~r2_hidden(A_129, C_131))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.40/1.56  tff(c_56, plain, (![A_28, B_29, C_30]: (k1_mcart_1(A_28)=B_29 | ~r2_hidden(A_28, k2_zfmisc_1(k1_tarski(B_29), C_30)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.40/1.56  tff(c_320, plain, (![A_129, B_130, B_29, D_132]: (k1_mcart_1(k4_tarski(A_129, B_130))=B_29 | ~r2_hidden(B_130, D_132) | ~r2_hidden(A_129, k1_tarski(B_29)))), inference(resolution, [status(thm)], [c_306, c_56])).
% 3.40/1.56  tff(c_328, plain, (![B_29, A_129, B_130, D_132]: (B_29=A_129 | ~r2_hidden(B_130, D_132) | ~r2_hidden(A_129, k1_tarski(B_29)))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_320])).
% 3.40/1.56  tff(c_329, plain, (![B_130, D_132]: (~r2_hidden(B_130, D_132))), inference(splitLeft, [status(thm)], [c_328])).
% 3.40/1.56  tff(c_346, plain, $false, inference(negUnitSimplification, [status(thm)], [c_329, c_227])).
% 3.40/1.56  tff(c_347, plain, (![B_29, A_129]: (B_29=A_129 | ~r2_hidden(A_129, k1_tarski(B_29)))), inference(splitRight, [status(thm)], [c_328])).
% 3.40/1.56  tff(c_991, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_972, c_347])).
% 3.40/1.56  tff(c_1003, plain, $false, inference(negUnitSimplification, [status(thm)], [c_169, c_991])).
% 3.40/1.56  tff(c_1004, plain, (r2_hidden('#skF_5', k1_tarski(k1_mcart_1('#skF_3')))), inference(splitRight, [status(thm)], [c_967])).
% 3.40/1.56  tff(c_1037, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_1004, c_347])).
% 3.40/1.56  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_166, c_1037])).
% 3.40/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.40/1.56  
% 3.40/1.56  Inference rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Ref     : 0
% 3.40/1.56  #Sup     : 224
% 3.40/1.56  #Fact    : 0
% 3.40/1.56  #Define  : 0
% 3.40/1.56  #Split   : 3
% 3.40/1.56  #Chain   : 0
% 3.40/1.56  #Close   : 0
% 3.40/1.56  
% 3.40/1.56  Ordering : KBO
% 3.40/1.56  
% 3.40/1.56  Simplification rules
% 3.40/1.56  ----------------------
% 3.40/1.56  #Subsume      : 30
% 3.40/1.56  #Demod        : 33
% 3.40/1.56  #Tautology    : 67
% 3.40/1.56  #SimpNegUnit  : 19
% 3.40/1.56  #BackRed      : 9
% 3.40/1.56  
% 3.40/1.56  #Partial instantiations: 0
% 3.40/1.56  #Strategies tried      : 1
% 3.40/1.56  
% 3.40/1.56  Timing (in seconds)
% 3.40/1.56  ----------------------
% 3.40/1.56  Preprocessing        : 0.35
% 3.40/1.56  Parsing              : 0.18
% 3.40/1.56  CNF conversion       : 0.03
% 3.40/1.56  Main loop            : 0.43
% 3.40/1.56  Inferencing          : 0.16
% 3.40/1.56  Reduction            : 0.12
% 3.40/1.56  Demodulation         : 0.08
% 3.40/1.56  BG Simplification    : 0.02
% 3.40/1.57  Subsumption          : 0.09
% 3.40/1.57  Abstraction          : 0.03
% 3.40/1.57  MUC search           : 0.00
% 3.40/1.57  Cooper               : 0.00
% 3.40/1.57  Total                : 0.80
% 3.40/1.57  Index Insertion      : 0.00
% 3.40/1.57  Index Deletion       : 0.00
% 3.40/1.57  Index Matching       : 0.00
% 3.40/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
