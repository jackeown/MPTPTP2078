%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:46 EST 2020

% Result     : Theorem 3.76s
% Output     : CNFRefutation 3.76s
% Verified   : 
% Statistics : Number of formulae       :   50 ( 111 expanded)
%              Number of leaves         :   24 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   68 ( 206 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & r1_tarski(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_ordinal1)).

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

tff(c_42,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_400,plain,(
    ! [A_125,B_126,C_127] :
      ( r2_hidden('#skF_3'(A_125,B_126,C_127),A_125)
      | r2_hidden('#skF_5'(A_125,B_126,C_127),C_127)
      | k2_zfmisc_1(A_125,B_126) = C_127 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] : r1_tarski(k1_xboole_0,A_6) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_56,B_57] :
      ( r2_hidden('#skF_8'(A_56,B_57),B_57)
      | ~ r2_hidden(A_56,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [B_49,A_48] :
      ( ~ r1_tarski(B_49,A_48)
      | ~ r2_hidden(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_79,plain,(
    ! [B_65,A_66] :
      ( ~ r1_tarski(B_65,'#skF_8'(A_66,B_65))
      | ~ r2_hidden(A_66,B_65) ) ),
    inference(resolution,[status(thm)],[c_46,c_38])).

tff(c_84,plain,(
    ! [A_66] : ~ r2_hidden(A_66,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_79])).

tff(c_1364,plain,(
    ! [A_258,B_259] :
      ( r2_hidden('#skF_3'(A_258,B_259,k1_xboole_0),A_258)
      | k2_zfmisc_1(A_258,B_259) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_400,c_84])).

tff(c_1451,plain,(
    ! [B_259] : k2_zfmisc_1(k1_xboole_0,B_259) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1364,c_84])).

tff(c_1034,plain,(
    ! [A_194,B_195,C_196] :
      ( r2_hidden('#skF_4'(A_194,B_195,C_196),B_195)
      | r2_hidden('#skF_5'(A_194,B_195,C_196),C_196)
      | k2_zfmisc_1(A_194,B_195) = C_196 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1959,plain,(
    ! [A_272,C_273] :
      ( r2_hidden('#skF_5'(A_272,k1_xboole_0,C_273),C_273)
      | k2_zfmisc_1(A_272,k1_xboole_0) = C_273 ) ),
    inference(resolution,[status(thm)],[c_1034,c_84])).

tff(c_1991,plain,(
    ! [A_272] : k2_zfmisc_1(A_272,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1959,c_84])).

tff(c_229,plain,(
    ! [A_99,B_100,D_101] :
      ( r2_hidden('#skF_7'(A_99,B_100,k2_zfmisc_1(A_99,B_100),D_101),B_100)
      | ~ r2_hidden(D_101,k2_zfmisc_1(A_99,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_256,plain,(
    ! [D_101,A_99] : ~ r2_hidden(D_101,k2_zfmisc_1(A_99,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_229,c_84])).

tff(c_478,plain,(
    ! [A_99,B_126,C_127] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_99,k1_xboole_0),B_126,C_127),C_127)
      | k2_zfmisc_1(k2_zfmisc_1(A_99,k1_xboole_0),B_126) = C_127 ) ),
    inference(resolution,[status(thm)],[c_400,c_256])).

tff(c_2232,plain,(
    ! [B_126,C_127] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_126,C_127),C_127)
      | k1_xboole_0 = C_127 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1451,c_1991,c_1991,c_478])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_124,plain,(
    ! [D_77,A_78,B_79] :
      ( ~ r2_hidden(D_77,'#skF_8'(A_78,B_79))
      | ~ r2_hidden(D_77,B_79)
      | ~ r2_hidden(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_2278,plain,(
    ! [A_327,B_328,B_329] :
      ( ~ r2_hidden('#skF_1'('#skF_8'(A_327,B_328),B_329),B_328)
      | ~ r2_hidden(A_327,B_328)
      | r1_xboole_0('#skF_8'(A_327,B_328),B_329) ) ),
    inference(resolution,[status(thm)],[c_6,c_124])).

tff(c_2288,plain,(
    ! [A_332,B_333] :
      ( ~ r2_hidden(A_332,B_333)
      | r1_xboole_0('#skF_8'(A_332,B_333),B_333) ) ),
    inference(resolution,[status(thm)],[c_4,c_2278])).

tff(c_40,plain,(
    ! [B_51] :
      ( ~ r1_xboole_0(B_51,'#skF_9')
      | ~ r2_hidden(B_51,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_55,plain,(
    ! [A_56] :
      ( ~ r1_xboole_0('#skF_8'(A_56,'#skF_9'),'#skF_9')
      | ~ r2_hidden(A_56,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_46,c_40])).

tff(c_2297,plain,(
    ! [A_334] : ~ r2_hidden(A_334,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2288,c_55])).

tff(c_2301,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2232,c_2297])).

tff(c_2361,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2301])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n005.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:30:17 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.76/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.61  
% 3.76/1.61  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.62  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1
% 3.76/1.62  
% 3.76/1.62  %Foreground sorts:
% 3.76/1.62  
% 3.76/1.62  
% 3.76/1.62  %Background operators:
% 3.76/1.62  
% 3.76/1.62  
% 3.76/1.62  %Foreground operators:
% 3.76/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.76/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.76/1.62  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.76/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.76/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.76/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.76/1.62  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.76/1.62  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.76/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.76/1.62  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.76/1.62  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.76/1.62  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.76/1.62  tff('#skF_9', type, '#skF_9': $i).
% 3.76/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.76/1.62  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.76/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.76/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.76/1.62  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.76/1.62  
% 3.76/1.63  tff(f_86, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.76/1.63  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 3.76/1.63  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.76/1.63  tff(f_70, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 3.76/1.63  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & r1_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_ordinal1)).
% 3.76/1.63  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.76/1.63  tff(c_42, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.76/1.63  tff(c_400, plain, (![A_125, B_126, C_127]: (r2_hidden('#skF_3'(A_125, B_126, C_127), A_125) | r2_hidden('#skF_5'(A_125, B_126, C_127), C_127) | k2_zfmisc_1(A_125, B_126)=C_127)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.76/1.63  tff(c_8, plain, (![A_6]: (r1_tarski(k1_xboole_0, A_6))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.76/1.63  tff(c_46, plain, (![A_56, B_57]: (r2_hidden('#skF_8'(A_56, B_57), B_57) | ~r2_hidden(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.76/1.63  tff(c_38, plain, (![B_49, A_48]: (~r1_tarski(B_49, A_48) | ~r2_hidden(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.76/1.63  tff(c_79, plain, (![B_65, A_66]: (~r1_tarski(B_65, '#skF_8'(A_66, B_65)) | ~r2_hidden(A_66, B_65))), inference(resolution, [status(thm)], [c_46, c_38])).
% 3.76/1.63  tff(c_84, plain, (![A_66]: (~r2_hidden(A_66, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_79])).
% 3.76/1.63  tff(c_1364, plain, (![A_258, B_259]: (r2_hidden('#skF_3'(A_258, B_259, k1_xboole_0), A_258) | k2_zfmisc_1(A_258, B_259)=k1_xboole_0)), inference(resolution, [status(thm)], [c_400, c_84])).
% 3.76/1.63  tff(c_1451, plain, (![B_259]: (k2_zfmisc_1(k1_xboole_0, B_259)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1364, c_84])).
% 3.76/1.63  tff(c_1034, plain, (![A_194, B_195, C_196]: (r2_hidden('#skF_4'(A_194, B_195, C_196), B_195) | r2_hidden('#skF_5'(A_194, B_195, C_196), C_196) | k2_zfmisc_1(A_194, B_195)=C_196)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.76/1.63  tff(c_1959, plain, (![A_272, C_273]: (r2_hidden('#skF_5'(A_272, k1_xboole_0, C_273), C_273) | k2_zfmisc_1(A_272, k1_xboole_0)=C_273)), inference(resolution, [status(thm)], [c_1034, c_84])).
% 3.76/1.63  tff(c_1991, plain, (![A_272]: (k2_zfmisc_1(A_272, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1959, c_84])).
% 3.76/1.63  tff(c_229, plain, (![A_99, B_100, D_101]: (r2_hidden('#skF_7'(A_99, B_100, k2_zfmisc_1(A_99, B_100), D_101), B_100) | ~r2_hidden(D_101, k2_zfmisc_1(A_99, B_100)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.76/1.63  tff(c_256, plain, (![D_101, A_99]: (~r2_hidden(D_101, k2_zfmisc_1(A_99, k1_xboole_0)))), inference(resolution, [status(thm)], [c_229, c_84])).
% 3.76/1.63  tff(c_478, plain, (![A_99, B_126, C_127]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_99, k1_xboole_0), B_126, C_127), C_127) | k2_zfmisc_1(k2_zfmisc_1(A_99, k1_xboole_0), B_126)=C_127)), inference(resolution, [status(thm)], [c_400, c_256])).
% 3.76/1.63  tff(c_2232, plain, (![B_126, C_127]: (r2_hidden('#skF_5'(k1_xboole_0, B_126, C_127), C_127) | k1_xboole_0=C_127)), inference(demodulation, [status(thm), theory('equality')], [c_1451, c_1991, c_1991, c_478])).
% 3.76/1.63  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.76/1.63  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.76/1.63  tff(c_124, plain, (![D_77, A_78, B_79]: (~r2_hidden(D_77, '#skF_8'(A_78, B_79)) | ~r2_hidden(D_77, B_79) | ~r2_hidden(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.76/1.63  tff(c_2278, plain, (![A_327, B_328, B_329]: (~r2_hidden('#skF_1'('#skF_8'(A_327, B_328), B_329), B_328) | ~r2_hidden(A_327, B_328) | r1_xboole_0('#skF_8'(A_327, B_328), B_329))), inference(resolution, [status(thm)], [c_6, c_124])).
% 3.76/1.63  tff(c_2288, plain, (![A_332, B_333]: (~r2_hidden(A_332, B_333) | r1_xboole_0('#skF_8'(A_332, B_333), B_333))), inference(resolution, [status(thm)], [c_4, c_2278])).
% 3.76/1.63  tff(c_40, plain, (![B_51]: (~r1_xboole_0(B_51, '#skF_9') | ~r2_hidden(B_51, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.76/1.63  tff(c_55, plain, (![A_56]: (~r1_xboole_0('#skF_8'(A_56, '#skF_9'), '#skF_9') | ~r2_hidden(A_56, '#skF_9'))), inference(resolution, [status(thm)], [c_46, c_40])).
% 3.76/1.63  tff(c_2297, plain, (![A_334]: (~r2_hidden(A_334, '#skF_9'))), inference(resolution, [status(thm)], [c_2288, c_55])).
% 3.76/1.63  tff(c_2301, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2232, c_2297])).
% 3.76/1.63  tff(c_2361, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2301])).
% 3.76/1.63  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.76/1.63  
% 3.76/1.63  Inference rules
% 3.76/1.63  ----------------------
% 3.76/1.63  #Ref     : 0
% 3.76/1.63  #Sup     : 466
% 3.76/1.63  #Fact    : 0
% 3.76/1.63  #Define  : 0
% 3.76/1.63  #Split   : 0
% 3.76/1.63  #Chain   : 0
% 3.76/1.63  #Close   : 0
% 3.76/1.63  
% 3.76/1.63  Ordering : KBO
% 3.76/1.63  
% 3.76/1.63  Simplification rules
% 3.76/1.63  ----------------------
% 3.76/1.63  #Subsume      : 181
% 3.76/1.63  #Demod        : 375
% 3.76/1.63  #Tautology    : 132
% 3.76/1.63  #SimpNegUnit  : 15
% 3.76/1.63  #BackRed      : 46
% 3.76/1.63  
% 3.76/1.63  #Partial instantiations: 0
% 3.76/1.63  #Strategies tried      : 1
% 3.76/1.63  
% 3.76/1.63  Timing (in seconds)
% 3.76/1.63  ----------------------
% 4.09/1.63  Preprocessing        : 0.31
% 4.09/1.63  Parsing              : 0.16
% 4.09/1.63  CNF conversion       : 0.03
% 4.09/1.63  Main loop            : 0.57
% 4.09/1.63  Inferencing          : 0.21
% 4.09/1.63  Reduction            : 0.17
% 4.09/1.63  Demodulation         : 0.11
% 4.09/1.63  BG Simplification    : 0.03
% 4.09/1.63  Subsumption          : 0.11
% 4.09/1.63  Abstraction          : 0.03
% 4.09/1.63  MUC search           : 0.00
% 4.09/1.63  Cooper               : 0.00
% 4.09/1.63  Total                : 0.90
% 4.09/1.63  Index Insertion      : 0.00
% 4.09/1.63  Index Deletion       : 0.00
% 4.09/1.63  Index Matching       : 0.00
% 4.09/1.63  BG Taut test         : 0.00
%------------------------------------------------------------------------------
