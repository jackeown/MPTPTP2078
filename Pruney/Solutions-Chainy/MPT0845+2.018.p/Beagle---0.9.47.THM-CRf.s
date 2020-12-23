%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:46 EST 2020

% Result     : Theorem 3.89s
% Output     : CNFRefutation 4.01s
% Verified   : 
% Statistics : Number of formulae       :   49 (  90 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :    7
%              Number of atoms          :   66 ( 150 expanded)
%              Number of equality atoms :   13 (  26 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

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

tff(f_75,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & ! [C] :
            ~ ( r2_hidden(C,B)
              & ! [D] :
                  ~ ( r2_hidden(D,B)
                    & r2_hidden(D,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_tarski)).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_426,plain,(
    ! [A_133,B_134,C_135] :
      ( r2_hidden('#skF_3'(A_133,B_134,C_135),A_133)
      | r2_hidden('#skF_5'(A_133,B_134,C_135),C_135)
      | k2_zfmisc_1(A_133,B_134) = C_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_51,plain,(
    ! [A_57,C_58,B_59] :
      ( ~ r2_hidden(A_57,C_58)
      | ~ r1_xboole_0(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    ! [A_57] : ~ r2_hidden(A_57,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_51])).

tff(c_1368,plain,(
    ! [A_254,B_255] :
      ( r2_hidden('#skF_3'(A_254,B_255,k1_xboole_0),A_254)
      | k2_zfmisc_1(A_254,B_255) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_426,c_56])).

tff(c_1452,plain,(
    ! [B_255] : k2_zfmisc_1(k1_xboole_0,B_255) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1368,c_56])).

tff(c_1042,plain,(
    ! [A_203,B_204,C_205] :
      ( r2_hidden('#skF_4'(A_203,B_204,C_205),B_204)
      | r2_hidden('#skF_5'(A_203,B_204,C_205),C_205)
      | k2_zfmisc_1(A_203,B_204) = C_205 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1969,plain,(
    ! [A_267,C_268] :
      ( r2_hidden('#skF_5'(A_267,k1_xboole_0,C_268),C_268)
      | k2_zfmisc_1(A_267,k1_xboole_0) = C_268 ) ),
    inference(resolution,[status(thm)],[c_1042,c_56])).

tff(c_1998,plain,(
    ! [A_267] : k2_zfmisc_1(A_267,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1969,c_56])).

tff(c_244,plain,(
    ! [A_107,B_108,D_109] :
      ( r2_hidden('#skF_7'(A_107,B_108,k2_zfmisc_1(A_107,B_108),D_109),B_108)
      | ~ r2_hidden(D_109,k2_zfmisc_1(A_107,B_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_273,plain,(
    ! [D_109,A_107] : ~ r2_hidden(D_109,k2_zfmisc_1(A_107,k1_xboole_0)) ),
    inference(resolution,[status(thm)],[c_244,c_56])).

tff(c_506,plain,(
    ! [A_107,B_134,C_135] :
      ( r2_hidden('#skF_5'(k2_zfmisc_1(A_107,k1_xboole_0),B_134,C_135),C_135)
      | k2_zfmisc_1(k2_zfmisc_1(A_107,k1_xboole_0),B_134) = C_135 ) ),
    inference(resolution,[status(thm)],[c_426,c_273])).

tff(c_2131,plain,(
    ! [B_134,C_135] :
      ( r2_hidden('#skF_5'(k1_xboole_0,B_134,C_135),C_135)
      | k1_xboole_0 = C_135 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1452,c_1998,c_1998,c_506])).

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

tff(c_97,plain,(
    ! [D_72,A_73,B_74] :
      ( ~ r2_hidden(D_72,'#skF_8'(A_73,B_74))
      | ~ r2_hidden(D_72,B_74)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2152,plain,(
    ! [A_296,B_297,B_298] :
      ( ~ r2_hidden('#skF_1'('#skF_8'(A_296,B_297),B_298),B_297)
      | ~ r2_hidden(A_296,B_297)
      | r1_xboole_0('#skF_8'(A_296,B_297),B_298) ) ),
    inference(resolution,[status(thm)],[c_6,c_97])).

tff(c_2158,plain,(
    ! [A_299,B_300] :
      ( ~ r2_hidden(A_299,B_300)
      | r1_xboole_0('#skF_8'(A_299,B_300),B_300) ) ),
    inference(resolution,[status(thm)],[c_4,c_2152])).

tff(c_76,plain,(
    ! [A_64,B_65] :
      ( r2_hidden('#skF_8'(A_64,B_65),B_65)
      | ~ r2_hidden(A_64,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [B_52] :
      ( ~ r1_xboole_0(B_52,'#skF_9')
      | ~ r2_hidden(B_52,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_86,plain,(
    ! [A_64] :
      ( ~ r1_xboole_0('#skF_8'(A_64,'#skF_9'),'#skF_9')
      | ~ r2_hidden(A_64,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_76,c_40])).

tff(c_2167,plain,(
    ! [A_301] : ~ r2_hidden(A_301,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2158,c_86])).

tff(c_2171,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2131,c_2167])).

tff(c_2227,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_2171])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:02:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.89/1.68  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.68  
% 3.89/1.68  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.89/1.68  %$ r2_hidden > r1_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1
% 3.89/1.68  
% 3.89/1.68  %Foreground sorts:
% 3.89/1.68  
% 3.89/1.68  
% 3.89/1.68  %Background operators:
% 3.89/1.68  
% 3.89/1.68  
% 3.89/1.68  %Foreground operators:
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.89/1.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.89/1.68  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.89/1.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.89/1.68  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.89/1.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.89/1.68  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 3.89/1.68  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.89/1.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.89/1.68  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 3.89/1.68  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 3.89/1.68  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 3.89/1.68  tff('#skF_9', type, '#skF_9': $i).
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.89/1.68  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.89/1.68  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.89/1.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.89/1.68  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.89/1.68  
% 4.01/1.69  tff(f_86, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_mcart_1)).
% 4.01/1.69  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.01/1.69  tff(f_45, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.01/1.69  tff(f_62, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 4.01/1.69  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.01/1.69  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_tarski)).
% 4.01/1.69  tff(c_42, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.01/1.69  tff(c_426, plain, (![A_133, B_134, C_135]: (r2_hidden('#skF_3'(A_133, B_134, C_135), A_133) | r2_hidden('#skF_5'(A_133, B_134, C_135), C_135) | k2_zfmisc_1(A_133, B_134)=C_135)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.69  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.01/1.69  tff(c_51, plain, (![A_57, C_58, B_59]: (~r2_hidden(A_57, C_58) | ~r1_xboole_0(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.01/1.69  tff(c_56, plain, (![A_57]: (~r2_hidden(A_57, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_51])).
% 4.01/1.69  tff(c_1368, plain, (![A_254, B_255]: (r2_hidden('#skF_3'(A_254, B_255, k1_xboole_0), A_254) | k2_zfmisc_1(A_254, B_255)=k1_xboole_0)), inference(resolution, [status(thm)], [c_426, c_56])).
% 4.01/1.69  tff(c_1452, plain, (![B_255]: (k2_zfmisc_1(k1_xboole_0, B_255)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1368, c_56])).
% 4.01/1.69  tff(c_1042, plain, (![A_203, B_204, C_205]: (r2_hidden('#skF_4'(A_203, B_204, C_205), B_204) | r2_hidden('#skF_5'(A_203, B_204, C_205), C_205) | k2_zfmisc_1(A_203, B_204)=C_205)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.69  tff(c_1969, plain, (![A_267, C_268]: (r2_hidden('#skF_5'(A_267, k1_xboole_0, C_268), C_268) | k2_zfmisc_1(A_267, k1_xboole_0)=C_268)), inference(resolution, [status(thm)], [c_1042, c_56])).
% 4.01/1.69  tff(c_1998, plain, (![A_267]: (k2_zfmisc_1(A_267, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1969, c_56])).
% 4.01/1.69  tff(c_244, plain, (![A_107, B_108, D_109]: (r2_hidden('#skF_7'(A_107, B_108, k2_zfmisc_1(A_107, B_108), D_109), B_108) | ~r2_hidden(D_109, k2_zfmisc_1(A_107, B_108)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.01/1.69  tff(c_273, plain, (![D_109, A_107]: (~r2_hidden(D_109, k2_zfmisc_1(A_107, k1_xboole_0)))), inference(resolution, [status(thm)], [c_244, c_56])).
% 4.01/1.69  tff(c_506, plain, (![A_107, B_134, C_135]: (r2_hidden('#skF_5'(k2_zfmisc_1(A_107, k1_xboole_0), B_134, C_135), C_135) | k2_zfmisc_1(k2_zfmisc_1(A_107, k1_xboole_0), B_134)=C_135)), inference(resolution, [status(thm)], [c_426, c_273])).
% 4.01/1.69  tff(c_2131, plain, (![B_134, C_135]: (r2_hidden('#skF_5'(k1_xboole_0, B_134, C_135), C_135) | k1_xboole_0=C_135)), inference(demodulation, [status(thm), theory('equality')], [c_1452, c_1998, c_1998, c_506])).
% 4.01/1.69  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.01/1.69  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.01/1.69  tff(c_97, plain, (![D_72, A_73, B_74]: (~r2_hidden(D_72, '#skF_8'(A_73, B_74)) | ~r2_hidden(D_72, B_74) | ~r2_hidden(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.69  tff(c_2152, plain, (![A_296, B_297, B_298]: (~r2_hidden('#skF_1'('#skF_8'(A_296, B_297), B_298), B_297) | ~r2_hidden(A_296, B_297) | r1_xboole_0('#skF_8'(A_296, B_297), B_298))), inference(resolution, [status(thm)], [c_6, c_97])).
% 4.01/1.69  tff(c_2158, plain, (![A_299, B_300]: (~r2_hidden(A_299, B_300) | r1_xboole_0('#skF_8'(A_299, B_300), B_300))), inference(resolution, [status(thm)], [c_4, c_2152])).
% 4.01/1.69  tff(c_76, plain, (![A_64, B_65]: (r2_hidden('#skF_8'(A_64, B_65), B_65) | ~r2_hidden(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.01/1.69  tff(c_40, plain, (![B_52]: (~r1_xboole_0(B_52, '#skF_9') | ~r2_hidden(B_52, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.01/1.69  tff(c_86, plain, (![A_64]: (~r1_xboole_0('#skF_8'(A_64, '#skF_9'), '#skF_9') | ~r2_hidden(A_64, '#skF_9'))), inference(resolution, [status(thm)], [c_76, c_40])).
% 4.01/1.69  tff(c_2167, plain, (![A_301]: (~r2_hidden(A_301, '#skF_9'))), inference(resolution, [status(thm)], [c_2158, c_86])).
% 4.01/1.69  tff(c_2171, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_2131, c_2167])).
% 4.01/1.69  tff(c_2227, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_2171])).
% 4.01/1.69  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.01/1.69  
% 4.01/1.69  Inference rules
% 4.01/1.69  ----------------------
% 4.01/1.69  #Ref     : 0
% 4.01/1.69  #Sup     : 440
% 4.01/1.69  #Fact    : 0
% 4.01/1.69  #Define  : 0
% 4.01/1.69  #Split   : 0
% 4.01/1.69  #Chain   : 0
% 4.01/1.69  #Close   : 0
% 4.01/1.69  
% 4.01/1.69  Ordering : KBO
% 4.01/1.69  
% 4.01/1.69  Simplification rules
% 4.01/1.69  ----------------------
% 4.01/1.69  #Subsume      : 179
% 4.01/1.69  #Demod        : 346
% 4.01/1.69  #Tautology    : 126
% 4.01/1.69  #SimpNegUnit  : 14
% 4.01/1.69  #BackRed      : 46
% 4.01/1.69  
% 4.01/1.69  #Partial instantiations: 0
% 4.01/1.69  #Strategies tried      : 1
% 4.01/1.69  
% 4.01/1.69  Timing (in seconds)
% 4.01/1.69  ----------------------
% 4.01/1.70  Preprocessing        : 0.33
% 4.01/1.70  Parsing              : 0.17
% 4.01/1.70  CNF conversion       : 0.03
% 4.01/1.70  Main loop            : 0.54
% 4.01/1.70  Inferencing          : 0.21
% 4.01/1.70  Reduction            : 0.16
% 4.01/1.70  Demodulation         : 0.11
% 4.01/1.70  BG Simplification    : 0.03
% 4.01/1.70  Subsumption          : 0.10
% 4.01/1.70  Abstraction          : 0.03
% 4.01/1.70  MUC search           : 0.00
% 4.01/1.70  Cooper               : 0.00
% 4.01/1.70  Total                : 0.89
% 4.01/1.70  Index Insertion      : 0.00
% 4.01/1.70  Index Deletion       : 0.00
% 4.01/1.70  Index Matching       : 0.00
% 4.01/1.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------
