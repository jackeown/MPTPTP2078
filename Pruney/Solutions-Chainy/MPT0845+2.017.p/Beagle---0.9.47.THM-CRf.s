%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:46 EST 2020

% Result     : Theorem 4.92s
% Output     : CNFRefutation 4.92s
% Verified   : 
% Statistics : Number of formulae       :   45 (  60 expanded)
%              Number of leaves         :   25 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   57 (  92 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_zfmisc_1(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ? [E,F] :
              ( r2_hidden(E,A)
              & r2_hidden(F,B)
              & D = k4_tarski(E,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_62,axiom,(
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

tff(f_75,axiom,(
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

tff(c_397,plain,(
    ! [A_126,B_127,C_128] :
      ( r2_hidden('#skF_4'(A_126,B_127,C_128),B_127)
      | r2_hidden('#skF_5'(A_126,B_127,C_128),C_128)
      | k2_zfmisc_1(A_126,B_127) = C_128 ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_8,plain,(
    ! [A_6] : k4_xboole_0(k1_xboole_0,A_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_84,plain,(
    ! [B_60,A_61] :
      ( ~ r2_hidden(B_60,A_61)
      | k4_xboole_0(A_61,k1_tarski(B_60)) != A_61 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_93,plain,(
    ! [B_60] : ~ r2_hidden(B_60,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_84])).

tff(c_1920,plain,(
    ! [A_269,C_270] :
      ( r2_hidden('#skF_5'(A_269,k1_xboole_0,C_270),C_270)
      | k2_zfmisc_1(A_269,k1_xboole_0) = C_270 ) ),
    inference(resolution,[status(thm)],[c_397,c_93])).

tff(c_1949,plain,(
    ! [A_269] : k2_zfmisc_1(A_269,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1920,c_93])).

tff(c_473,plain,(
    ! [A_126,C_128] :
      ( r2_hidden('#skF_5'(A_126,k1_xboole_0,C_128),C_128)
      | k2_zfmisc_1(A_126,k1_xboole_0) = C_128 ) ),
    inference(resolution,[status(thm)],[c_397,c_93])).

tff(c_1951,plain,(
    ! [A_126,C_128] :
      ( r2_hidden('#skF_5'(A_126,k1_xboole_0,C_128),C_128)
      | k1_xboole_0 = C_128 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1949,c_473])).

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
      ( ~ r2_hidden(D_73,'#skF_8'(A_74,B_75))
      | ~ r2_hidden(D_73,B_75)
      | ~ r2_hidden(A_74,B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2094,plain,(
    ! [A_294,B_295,B_296] :
      ( ~ r2_hidden('#skF_1'('#skF_8'(A_294,B_295),B_296),B_295)
      | ~ r2_hidden(A_294,B_295)
      | r1_xboole_0('#skF_8'(A_294,B_295),B_296) ) ),
    inference(resolution,[status(thm)],[c_6,c_128])).

tff(c_2100,plain,(
    ! [A_297,B_298] :
      ( ~ r2_hidden(A_297,B_298)
      | r1_xboole_0('#skF_8'(A_297,B_298),B_298) ) ),
    inference(resolution,[status(thm)],[c_4,c_2094])).

tff(c_108,plain,(
    ! [A_66,B_67] :
      ( r2_hidden('#skF_8'(A_66,B_67),B_67)
      | ~ r2_hidden(A_66,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    ! [B_51] :
      ( ~ r1_xboole_0(B_51,'#skF_9')
      | ~ r2_hidden(B_51,'#skF_9') ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_118,plain,(
    ! [A_66] :
      ( ~ r1_xboole_0('#skF_8'(A_66,'#skF_9'),'#skF_9')
      | ~ r2_hidden(A_66,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_108,c_42])).

tff(c_2109,plain,(
    ! [A_299] : ~ r2_hidden(A_299,'#skF_9') ),
    inference(resolution,[status(thm)],[c_2100,c_118])).

tff(c_2113,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_1951,c_2109])).

tff(c_2165,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_2113])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:54:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.92/2.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/2.26  
% 4.92/2.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/2.26  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_5 > #skF_2 > #skF_7 > #skF_6 > #skF_8 > #skF_9 > #skF_3 > #skF_1
% 4.92/2.26  
% 4.92/2.26  %Foreground sorts:
% 4.92/2.26  
% 4.92/2.26  
% 4.92/2.26  %Background operators:
% 4.92/2.26  
% 4.92/2.26  
% 4.92/2.26  %Foreground operators:
% 4.92/2.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.92/2.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.92/2.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.92/2.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.92/2.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.92/2.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.92/2.26  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 4.92/2.26  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 4.92/2.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.92/2.26  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.92/2.26  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 4.92/2.26  tff('#skF_6', type, '#skF_6': ($i * $i * $i * $i) > $i).
% 4.92/2.26  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 4.92/2.26  tff('#skF_9', type, '#skF_9': $i).
% 4.92/2.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.92/2.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.92/2.26  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.92/2.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.92/2.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.92/2.26  
% 4.92/2.28  tff(f_86, negated_conjecture, ~(![A]: ~(~(A = k1_xboole_0) & (![B]: ~(r2_hidden(B, A) & r1_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_mcart_1)).
% 4.92/2.28  tff(f_57, axiom, (![A, B, C]: ((C = k2_zfmisc_1(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (?[E, F]: ((r2_hidden(E, A) & r2_hidden(F, B)) & (D = k4_tarski(E, F)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_zfmisc_1)).
% 4.92/2.28  tff(f_45, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.92/2.28  tff(f_62, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 4.92/2.28  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.92/2.28  tff(f_75, axiom, (![A, B]: ~(r2_hidden(A, B) & (![C]: ~(r2_hidden(C, B) & (![D]: ~(r2_hidden(D, B) & r2_hidden(D, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_tarski)).
% 4.92/2.28  tff(c_44, plain, (k1_xboole_0!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.92/2.28  tff(c_397, plain, (![A_126, B_127, C_128]: (r2_hidden('#skF_4'(A_126, B_127, C_128), B_127) | r2_hidden('#skF_5'(A_126, B_127, C_128), C_128) | k2_zfmisc_1(A_126, B_127)=C_128)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.92/2.28  tff(c_8, plain, (![A_6]: (k4_xboole_0(k1_xboole_0, A_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.92/2.28  tff(c_84, plain, (![B_60, A_61]: (~r2_hidden(B_60, A_61) | k4_xboole_0(A_61, k1_tarski(B_60))!=A_61)), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.92/2.28  tff(c_93, plain, (![B_60]: (~r2_hidden(B_60, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_84])).
% 4.92/2.28  tff(c_1920, plain, (![A_269, C_270]: (r2_hidden('#skF_5'(A_269, k1_xboole_0, C_270), C_270) | k2_zfmisc_1(A_269, k1_xboole_0)=C_270)), inference(resolution, [status(thm)], [c_397, c_93])).
% 4.92/2.28  tff(c_1949, plain, (![A_269]: (k2_zfmisc_1(A_269, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_1920, c_93])).
% 4.92/2.28  tff(c_473, plain, (![A_126, C_128]: (r2_hidden('#skF_5'(A_126, k1_xboole_0, C_128), C_128) | k2_zfmisc_1(A_126, k1_xboole_0)=C_128)), inference(resolution, [status(thm)], [c_397, c_93])).
% 4.92/2.28  tff(c_1951, plain, (![A_126, C_128]: (r2_hidden('#skF_5'(A_126, k1_xboole_0, C_128), C_128) | k1_xboole_0=C_128)), inference(demodulation, [status(thm), theory('equality')], [c_1949, c_473])).
% 4.92/2.28  tff(c_4, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.92/2.28  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.92/2.28  tff(c_128, plain, (![D_73, A_74, B_75]: (~r2_hidden(D_73, '#skF_8'(A_74, B_75)) | ~r2_hidden(D_73, B_75) | ~r2_hidden(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.92/2.28  tff(c_2094, plain, (![A_294, B_295, B_296]: (~r2_hidden('#skF_1'('#skF_8'(A_294, B_295), B_296), B_295) | ~r2_hidden(A_294, B_295) | r1_xboole_0('#skF_8'(A_294, B_295), B_296))), inference(resolution, [status(thm)], [c_6, c_128])).
% 4.92/2.28  tff(c_2100, plain, (![A_297, B_298]: (~r2_hidden(A_297, B_298) | r1_xboole_0('#skF_8'(A_297, B_298), B_298))), inference(resolution, [status(thm)], [c_4, c_2094])).
% 4.92/2.28  tff(c_108, plain, (![A_66, B_67]: (r2_hidden('#skF_8'(A_66, B_67), B_67) | ~r2_hidden(A_66, B_67))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.92/2.28  tff(c_42, plain, (![B_51]: (~r1_xboole_0(B_51, '#skF_9') | ~r2_hidden(B_51, '#skF_9'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.92/2.28  tff(c_118, plain, (![A_66]: (~r1_xboole_0('#skF_8'(A_66, '#skF_9'), '#skF_9') | ~r2_hidden(A_66, '#skF_9'))), inference(resolution, [status(thm)], [c_108, c_42])).
% 4.92/2.28  tff(c_2109, plain, (![A_299]: (~r2_hidden(A_299, '#skF_9'))), inference(resolution, [status(thm)], [c_2100, c_118])).
% 4.92/2.28  tff(c_2113, plain, (k1_xboole_0='#skF_9'), inference(resolution, [status(thm)], [c_1951, c_2109])).
% 4.92/2.28  tff(c_2165, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_2113])).
% 4.92/2.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.92/2.28  
% 4.92/2.28  Inference rules
% 4.92/2.28  ----------------------
% 4.92/2.28  #Ref     : 0
% 4.92/2.28  #Sup     : 429
% 4.92/2.28  #Fact    : 0
% 4.92/2.28  #Define  : 0
% 4.92/2.28  #Split   : 0
% 4.92/2.28  #Chain   : 0
% 4.92/2.28  #Close   : 0
% 4.92/2.28  
% 4.92/2.28  Ordering : KBO
% 4.92/2.28  
% 4.92/2.28  Simplification rules
% 4.92/2.28  ----------------------
% 4.92/2.28  #Subsume      : 164
% 4.92/2.28  #Demod        : 342
% 4.92/2.28  #Tautology    : 131
% 4.92/2.28  #SimpNegUnit  : 14
% 4.92/2.28  #BackRed      : 45
% 4.92/2.28  
% 4.92/2.28  #Partial instantiations: 0
% 4.92/2.28  #Strategies tried      : 1
% 4.92/2.28  
% 4.92/2.28  Timing (in seconds)
% 4.92/2.28  ----------------------
% 4.92/2.28  Preprocessing        : 0.49
% 4.92/2.29  Parsing              : 0.25
% 4.92/2.29  CNF conversion       : 0.04
% 4.92/2.29  Main loop            : 0.93
% 4.92/2.29  Inferencing          : 0.36
% 4.92/2.29  Reduction            : 0.27
% 4.92/2.29  Demodulation         : 0.19
% 4.92/2.29  BG Simplification    : 0.04
% 4.92/2.29  Subsumption          : 0.18
% 4.92/2.29  Abstraction          : 0.05
% 4.92/2.29  MUC search           : 0.00
% 4.92/2.29  Cooper               : 0.00
% 4.92/2.29  Total                : 1.46
% 4.92/2.29  Index Insertion      : 0.00
% 4.92/2.29  Index Deletion       : 0.00
% 4.92/2.29  Index Matching       : 0.00
% 4.92/2.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
