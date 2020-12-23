%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:49 EST 2020

% Result     : Theorem 3.69s
% Output     : CNFRefutation 3.69s
% Verified   : 
% Statistics : Number of formulae       :   50 (  91 expanded)
%              Number of leaves         :   25 (  44 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 150 expanded)
%              Number of equality atoms :   17 (  54 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_setfam_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff(k3_setfam_1,type,(
    k3_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_86,negated_conjecture,(
    ~ ! [A] :
        ~ ( A != k1_xboole_0
          & ! [B] :
              ~ ( r2_hidden(B,A)
                & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( C = k3_setfam_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k3_xboole_0(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_setfam_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_tarski)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_604,plain,(
    ! [A_159,B_160,C_161] :
      ( r2_hidden('#skF_5'(A_159,B_160,C_161),B_160)
      | r2_hidden('#skF_6'(A_159,B_160,C_161),C_161)
      | k3_setfam_1(A_159,B_160) = C_161 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    ! [B_56,A_57] :
      ( ~ r2_hidden(B_56,A_57)
      | k4_xboole_0(A_57,k1_tarski(B_56)) != A_57 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_81,plain,(
    ! [B_56] : ~ r2_hidden(B_56,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_72])).

tff(c_1328,plain,(
    ! [A_254,B_255] :
      ( r2_hidden('#skF_5'(A_254,B_255,k1_xboole_0),B_255)
      | k3_setfam_1(A_254,B_255) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_604,c_81])).

tff(c_1412,plain,(
    ! [A_254] : k3_setfam_1(A_254,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1328,c_81])).

tff(c_1015,plain,(
    ! [A_196,B_197,C_198] :
      ( r2_hidden('#skF_4'(A_196,B_197,C_198),A_196)
      | r2_hidden('#skF_6'(A_196,B_197,C_198),C_198)
      | k3_setfam_1(A_196,B_197) = C_198 ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1929,plain,(
    ! [A_267,B_268] :
      ( r2_hidden('#skF_4'(A_267,B_268,k1_xboole_0),A_267)
      | k3_setfam_1(A_267,B_268) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_1015,c_81])).

tff(c_1958,plain,(
    ! [B_268] : k3_setfam_1(k1_xboole_0,B_268) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1929,c_81])).

tff(c_145,plain,(
    ! [A_80,B_81,D_82] :
      ( r2_hidden('#skF_7'(A_80,B_81,k3_setfam_1(A_80,B_81),D_82),A_80)
      | ~ r2_hidden(D_82,k3_setfam_1(A_80,B_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_159,plain,(
    ! [D_82,B_81] : ~ r2_hidden(D_82,k3_setfam_1(k1_xboole_0,B_81)) ),
    inference(resolution,[status(thm)],[c_145,c_81])).

tff(c_714,plain,(
    ! [A_159,B_81,C_161] :
      ( r2_hidden('#skF_6'(A_159,k3_setfam_1(k1_xboole_0,B_81),C_161),C_161)
      | k3_setfam_1(A_159,k3_setfam_1(k1_xboole_0,B_81)) = C_161 ) ),
    inference(resolution,[status(thm)],[c_604,c_159])).

tff(c_2073,plain,(
    ! [A_159,C_161] :
      ( r2_hidden('#skF_6'(A_159,k1_xboole_0,C_161),C_161)
      | k1_xboole_0 = C_161 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_1958,c_1958,c_714])).

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

tff(c_128,plain,(
    ! [D_73,A_74,B_75] :
      ( ~ r2_hidden(D_73,'#skF_2'(A_74,B_75))
      | ~ r2_hidden(D_73,B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_2095,plain,(
    ! [A_295,B_296,B_297] :
      ( ~ r2_hidden('#skF_1'('#skF_2'(A_295,B_296),B_297),B_296)
      | ~ r2_hidden(A_295,B_296)
      | r1_xboole_0('#skF_2'(A_295,B_296),B_297) ) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_2101,plain,(
    ! [A_298,B_299] :
      ( ~ r2_hidden(A_298,B_299)
      | r1_xboole_0('#skF_2'(A_298,B_299),B_299) ) ),
    inference(resolution,[status(thm)],[c_4,c_2095])).

tff(c_95,plain,(
    ! [A_62,B_63] :
      ( r2_hidden('#skF_2'(A_62,B_63),B_63)
      | ~ r2_hidden(A_62,B_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_42,plain,(
    ! [B_51] :
      ( ~ r1_xboole_0(B_51,'#skF_9')
      | ~ r2_hidden(B_51,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_105,plain,(
    ! [A_62] :
      ( ~ r1_xboole_0('#skF_2'(A_62,'#skF_9'),'#skF_9')
      | ~ r2_hidden(A_62,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_95,c_42])).

tff(c_2110,plain,(
    ! [A_300] : ~ r2_hidden(A_300,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2101,c_105])).

tff(c_2114,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2073,c_2110])).

tff(c_2170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:17:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.69/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.58  
% 3.69/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.58  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_setfam_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_4 > #skF_8 > #skF_5 > #skF_7 > #skF_9 > #skF_3 > #skF_2 > #skF_1
% 3.69/1.58  
% 3.69/1.58  %Foreground sorts:
% 3.69/1.58  
% 3.69/1.58  
% 3.69/1.58  %Background operators:
% 3.69/1.58  
% 3.69/1.58  
% 3.69/1.58  %Foreground operators:
% 3.69/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.69/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.69/1.58  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 3.69/1.58  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.69/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.69/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.69/1.58  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.69/1.58  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 3.69/1.58  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.69/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.69/1.58  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.69/1.58  tff('#skF_9', type, '#skF_9': $i).
% 3.69/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.69/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.69/1.58  tff(k3_setfam_1, type, k3_setfam_1: ($i * $i) > $i).
% 3.69/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.69/1.58  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.69/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.69/1.58  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.69/1.58  
% 3.69/1.59  tff(f_86, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 3.69/1.59  tff(f_75, axiom, (![A, B, C]: ((C = k3_setfam_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k3_xboole_0(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_setfam_1)).
% 3.69/1.59  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 3.69/1.59  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 3.69/1.59  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 3.69/1.59  tff(f_63, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 3.69/1.59  tff(c_44, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.59  tff(c_604, plain, (![A_159, B_160, C_161]: (r2_hidden('#skF_5'(A_159, B_160, C_161), B_160) | r2_hidden('#skF_6'(A_159, B_160, C_161), C_161) | k3_setfam_1(A_159, B_160)=C_161)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.59  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.69/1.59  tff(c_72, plain, (![B_56, A_57]: (~r2_hidden(B_56, A_57) | k4_xboole_0(A_57, k1_tarski(B_56))!=A_57)), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.69/1.59  tff(c_81, plain, (![B_56]: (~r2_hidden(B_56, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_72])).
% 3.69/1.59  tff(c_1328, plain, (![A_254, B_255]: (r2_hidden('#skF_5'(A_254, B_255, k1_xboole_0), B_255) | k3_setfam_1(A_254, B_255)=k1_xboole_0)), inference(resolution, [status(thm)], [c_604, c_81])).
% 3.69/1.59  tff(c_1412, plain, (![A_254]: (k3_setfam_1(A_254, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1328, c_81])).
% 3.69/1.59  tff(c_1015, plain, (![A_196, B_197, C_198]: (r2_hidden('#skF_4'(A_196, B_197, C_198), A_196) | r2_hidden('#skF_6'(A_196, B_197, C_198), C_198) | k3_setfam_1(A_196, B_197)=C_198)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.59  tff(c_1929, plain, (![A_267, B_268]: (r2_hidden('#skF_4'(A_267, B_268, k1_xboole_0), A_267) | k3_setfam_1(A_267, B_268)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1015, c_81])).
% 3.69/1.59  tff(c_1958, plain, (![B_268]: (k3_setfam_1(k1_xboole_0, B_268)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1929, c_81])).
% 3.69/1.59  tff(c_145, plain, (![A_80, B_81, D_82]: (r2_hidden('#skF_7'(A_80, B_81, k3_setfam_1(A_80, B_81), D_82), A_80) | ~r2_hidden(D_82, k3_setfam_1(A_80, B_81)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.69/1.59  tff(c_159, plain, (![D_82, B_81]: (~r2_hidden(D_82, k3_setfam_1(k1_xboole_0, B_81)))), inference(resolution, [status(thm)], [c_145, c_81])).
% 3.69/1.59  tff(c_714, plain, (![A_159, B_81, C_161]: (r2_hidden('#skF_6'(A_159, k3_setfam_1(k1_xboole_0, B_81), C_161), C_161) | k3_setfam_1(A_159, k3_setfam_1(k1_xboole_0, B_81))=C_161)), inference(resolution, [status(thm)], [c_604, c_159])).
% 3.69/1.59  tff(c_2073, plain, (![A_159, C_161]: (r2_hidden('#skF_6'(A_159, k1_xboole_0, C_161), C_161) | k1_xboole_0=C_161)), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_1958, c_1958, c_714])).
% 3.69/1.59  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.69/1.59  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.69/1.59  tff(c_128, plain, (![D_73, A_74, B_75]: (~r2_hidden(D_73, '#skF_2'(A_74, B_75)) | ~r2_hidden(D_73, B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.59  tff(c_2095, plain, (![A_295, B_296, B_297]: (~r2_hidden('#skF_1'('#skF_2'(A_295, B_296), B_297), B_296) | ~r2_hidden(A_295, B_296) | r1_xboole_0('#skF_2'(A_295, B_296), B_297))), inference(resolution, [status(thm)], [c_6, c_128])).
% 3.69/1.59  tff(c_2101, plain, (![A_298, B_299]: (~r2_hidden(A_298, B_299) | r1_xboole_0('#skF_2'(A_298, B_299), B_299))), inference(resolution, [status(thm)], [c_4, c_2095])).
% 3.69/1.59  tff(c_95, plain, (![A_62, B_63]: (r2_hidden('#skF_2'(A_62, B_63), B_63) | ~r2_hidden(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.69/1.59  tff(c_42, plain, (![B_51]: (~r1_xboole_0(B_51, '#skF_9') | ~r2_hidden(B_51, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.69/1.59  tff(c_105, plain, (![A_62]: (~r1_xboole_0('#skF_2'(A_62, '#skF_9'), '#skF_9') | ~r2_hidden(A_62, '#skF_9'))), inference(resolution, [status(thm)], [c_95, c_42])).
% 3.69/1.59  tff(c_2110, plain, (![A_300]: (~r2_hidden(A_300, '#skF_9'))), inference(resolution, [status(thm)], [c_2101, c_105])).
% 3.69/1.59  tff(c_2114, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2073, c_2110])).
% 3.69/1.59  tff(c_2170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2114])).
% 3.69/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.69/1.59  
% 3.69/1.59  Inference rules
% 3.69/1.59  ----------------------
% 3.69/1.59  #Ref     : 0
% 3.69/1.59  #Sup     : 430
% 3.69/1.59  #Fact    : 0
% 3.69/1.59  #Define  : 0
% 3.69/1.59  #Split   : 0
% 3.69/1.59  #Chain   : 0
% 3.69/1.59  #Close   : 0
% 3.69/1.59  
% 3.69/1.59  Ordering : KBO
% 3.69/1.59  
% 3.69/1.59  Simplification rules
% 3.69/1.59  ----------------------
% 3.69/1.59  #Subsume      : 164
% 3.69/1.59  #Demod        : 345
% 3.69/1.59  #Tautology    : 131
% 3.69/1.59  #SimpNegUnit  : 15
% 3.69/1.59  #BackRed      : 45
% 3.69/1.59  
% 3.69/1.59  #Partial instantiations: 0
% 3.69/1.59  #Strategies tried      : 1
% 3.69/1.59  
% 3.69/1.59  Timing (in seconds)
% 3.69/1.59  ----------------------
% 3.69/1.60  Preprocessing        : 0.30
% 3.69/1.60  Parsing              : 0.15
% 3.69/1.60  CNF conversion       : 0.03
% 3.69/1.60  Main loop            : 0.54
% 3.69/1.60  Inferencing          : 0.20
% 3.69/1.60  Reduction            : 0.16
% 3.69/1.60  Demodulation         : 0.11
% 3.69/1.60  BG Simplification    : 0.02
% 3.69/1.60  Subsumption          : 0.11
% 3.69/1.60  Abstraction          : 0.03
% 3.69/1.60  MUC search           : 0.00
% 3.69/1.60  Cooper               : 0.00
% 3.69/1.60  Total                : 0.87
% 3.69/1.60  Index Insertion      : 0.00
% 3.69/1.60  Index Deletion       : 0.00
% 3.69/1.60  Index Matching       : 0.00
% 3.69/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
