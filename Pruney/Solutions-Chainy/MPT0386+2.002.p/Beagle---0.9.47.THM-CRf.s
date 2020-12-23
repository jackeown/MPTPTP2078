%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:08 EST 2020

% Result     : Theorem 7.99s
% Output     : CNFRefutation 7.99s
% Verified   : 
% Statistics : Number of formulae       :   52 (  72 expanded)
%              Number of leaves         :   29 (  39 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 106 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff(r2_tarski,type,(
    r2_tarski: ( $i * $i ) > $o )).

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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_129,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_66,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_56,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_68,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_52,axiom,(
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

tff(f_124,axiom,(
    ! [A,B] :
      ( ( A != k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> ! [C] :
              ( r2_hidden(C,B)
            <=> ! [D] :
                  ( r2_hidden(D,A)
                 => r2_hidden(C,D) ) ) ) )
      & ( A = k1_xboole_0
       => ( B = k1_setfam_1(A)
        <=> B = k1_xboole_0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_setfam_1)).

tff(c_64,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_10'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_24,plain,(
    ! [A_20] : k4_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | k4_xboole_0(A_13,B_14) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_66,plain,(
    r2_hidden('#skF_9','#skF_10') ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_438,plain,(
    ! [C_131,B_132,A_133] :
      ( r2_hidden(C_131,B_132)
      | ~ r2_hidden(C_131,A_133)
      | ~ r1_tarski(A_133,B_132) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_457,plain,(
    ! [B_134] :
      ( r2_hidden('#skF_9',B_134)
      | ~ r1_tarski('#skF_10',B_134) ) ),
    inference(resolution,[status(thm)],[c_66,c_438])).

tff(c_26,plain,(
    ! [A_21] : r1_xboole_0(A_21,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_280,plain,(
    ! [A_119,B_120,C_121] :
      ( ~ r1_xboole_0(A_119,B_120)
      | ~ r2_hidden(C_121,B_120)
      | ~ r2_hidden(C_121,A_119) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_283,plain,(
    ! [C_121,A_21] :
      ( ~ r2_hidden(C_121,k1_xboole_0)
      | ~ r2_hidden(C_121,A_21) ) ),
    inference(resolution,[status(thm)],[c_26,c_280])).

tff(c_464,plain,(
    ! [A_21] :
      ( ~ r2_hidden('#skF_9',A_21)
      | ~ r1_tarski('#skF_10',k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_457,c_283])).

tff(c_465,plain,(
    ~ r1_tarski('#skF_10',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_468,plain,(
    k4_xboole_0('#skF_10',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_465])).

tff(c_470,plain,(
    k1_xboole_0 != '#skF_10' ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_468])).

tff(c_1165,plain,(
    ! [C_190,D_191,A_192] :
      ( r2_hidden(C_190,D_191)
      | ~ r2_hidden(D_191,A_192)
      | ~ r2_hidden(C_190,k1_setfam_1(A_192))
      | k1_xboole_0 = A_192 ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1187,plain,(
    ! [C_190] :
      ( r2_hidden(C_190,'#skF_9')
      | ~ r2_hidden(C_190,k1_setfam_1('#skF_10'))
      | k1_xboole_0 = '#skF_10' ) ),
    inference(resolution,[status(thm)],[c_66,c_1165])).

tff(c_1207,plain,(
    ! [C_193] :
      ( r2_hidden(C_193,'#skF_9')
      | ~ r2_hidden(C_193,k1_setfam_1('#skF_10')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_470,c_1187])).

tff(c_4051,plain,(
    ! [B_340] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_10'),B_340),'#skF_9')
      | r1_tarski(k1_setfam_1('#skF_10'),B_340) ) ),
    inference(resolution,[status(thm)],[c_8,c_1207])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4064,plain,(
    r1_tarski(k1_setfam_1('#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_4051,c_6])).

tff(c_4074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_4064])).

tff(c_4075,plain,(
    ! [A_21] : ~ r2_hidden('#skF_9',A_21) ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_4079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4075,c_66])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:54:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.99/3.05  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/3.06  
% 7.99/3.06  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/3.06  %$ r2_tarski > r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_10 > #skF_5 > #skF_8 > #skF_9 > #skF_3 > #skF_2 > #skF_7 > #skF_1 > #skF_4
% 7.99/3.06  
% 7.99/3.06  %Foreground sorts:
% 7.99/3.06  
% 7.99/3.06  
% 7.99/3.06  %Background operators:
% 7.99/3.06  
% 7.99/3.06  
% 7.99/3.06  %Foreground operators:
% 7.99/3.06  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.99/3.06  tff(r2_tarski, type, r2_tarski: ($i * $i) > $o).
% 7.99/3.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.99/3.06  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.99/3.06  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.99/3.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.99/3.06  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.99/3.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.99/3.06  tff('#skF_10', type, '#skF_10': $i).
% 7.99/3.06  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 7.99/3.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 7.99/3.06  tff('#skF_8', type, '#skF_8': ($i * $i) > $i).
% 7.99/3.06  tff('#skF_9', type, '#skF_9': $i).
% 7.99/3.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.99/3.06  tff('#skF_3', type, '#skF_3': $i > $i).
% 7.99/3.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.99/3.06  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 7.99/3.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.99/3.06  tff('#skF_7', type, '#skF_7': ($i * $i) > $i).
% 7.99/3.06  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 7.99/3.06  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 7.99/3.06  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 7.99/3.06  
% 7.99/3.07  tff(f_129, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_setfam_1)).
% 7.99/3.07  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 7.99/3.07  tff(f_66, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 7.99/3.07  tff(f_56, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 7.99/3.07  tff(f_68, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 7.99/3.07  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 7.99/3.07  tff(f_124, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_setfam_1)).
% 7.99/3.07  tff(c_64, plain, (~r1_tarski(k1_setfam_1('#skF_10'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.99/3.07  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.99/3.07  tff(c_24, plain, (![A_20]: (k4_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.99/3.07  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | k4_xboole_0(A_13, B_14)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 7.99/3.07  tff(c_66, plain, (r2_hidden('#skF_9', '#skF_10')), inference(cnfTransformation, [status(thm)], [f_129])).
% 7.99/3.07  tff(c_438, plain, (![C_131, B_132, A_133]: (r2_hidden(C_131, B_132) | ~r2_hidden(C_131, A_133) | ~r1_tarski(A_133, B_132))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.99/3.07  tff(c_457, plain, (![B_134]: (r2_hidden('#skF_9', B_134) | ~r1_tarski('#skF_10', B_134))), inference(resolution, [status(thm)], [c_66, c_438])).
% 7.99/3.07  tff(c_26, plain, (![A_21]: (r1_xboole_0(A_21, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_68])).
% 7.99/3.07  tff(c_280, plain, (![A_119, B_120, C_121]: (~r1_xboole_0(A_119, B_120) | ~r2_hidden(C_121, B_120) | ~r2_hidden(C_121, A_119))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.99/3.07  tff(c_283, plain, (![C_121, A_21]: (~r2_hidden(C_121, k1_xboole_0) | ~r2_hidden(C_121, A_21))), inference(resolution, [status(thm)], [c_26, c_280])).
% 7.99/3.07  tff(c_464, plain, (![A_21]: (~r2_hidden('#skF_9', A_21) | ~r1_tarski('#skF_10', k1_xboole_0))), inference(resolution, [status(thm)], [c_457, c_283])).
% 7.99/3.07  tff(c_465, plain, (~r1_tarski('#skF_10', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_464])).
% 7.99/3.07  tff(c_468, plain, (k4_xboole_0('#skF_10', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_465])).
% 7.99/3.07  tff(c_470, plain, (k1_xboole_0!='#skF_10'), inference(demodulation, [status(thm), theory('equality')], [c_24, c_468])).
% 7.99/3.07  tff(c_1165, plain, (![C_190, D_191, A_192]: (r2_hidden(C_190, D_191) | ~r2_hidden(D_191, A_192) | ~r2_hidden(C_190, k1_setfam_1(A_192)) | k1_xboole_0=A_192)), inference(cnfTransformation, [status(thm)], [f_124])).
% 7.99/3.07  tff(c_1187, plain, (![C_190]: (r2_hidden(C_190, '#skF_9') | ~r2_hidden(C_190, k1_setfam_1('#skF_10')) | k1_xboole_0='#skF_10')), inference(resolution, [status(thm)], [c_66, c_1165])).
% 7.99/3.07  tff(c_1207, plain, (![C_193]: (r2_hidden(C_193, '#skF_9') | ~r2_hidden(C_193, k1_setfam_1('#skF_10')))), inference(negUnitSimplification, [status(thm)], [c_470, c_1187])).
% 7.99/3.07  tff(c_4051, plain, (![B_340]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_10'), B_340), '#skF_9') | r1_tarski(k1_setfam_1('#skF_10'), B_340))), inference(resolution, [status(thm)], [c_8, c_1207])).
% 7.99/3.07  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.99/3.07  tff(c_4064, plain, (r1_tarski(k1_setfam_1('#skF_10'), '#skF_9')), inference(resolution, [status(thm)], [c_4051, c_6])).
% 7.99/3.07  tff(c_4074, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_4064])).
% 7.99/3.07  tff(c_4075, plain, (![A_21]: (~r2_hidden('#skF_9', A_21))), inference(splitRight, [status(thm)], [c_464])).
% 7.99/3.07  tff(c_4079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4075, c_66])).
% 7.99/3.08  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.99/3.08  
% 7.99/3.08  Inference rules
% 7.99/3.08  ----------------------
% 7.99/3.08  #Ref     : 1
% 7.99/3.08  #Sup     : 959
% 7.99/3.08  #Fact    : 0
% 7.99/3.08  #Define  : 0
% 7.99/3.08  #Split   : 6
% 7.99/3.08  #Chain   : 0
% 7.99/3.08  #Close   : 0
% 7.99/3.08  
% 7.99/3.08  Ordering : KBO
% 7.99/3.08  
% 7.99/3.08  Simplification rules
% 7.99/3.08  ----------------------
% 7.99/3.08  #Subsume      : 271
% 7.99/3.08  #Demod        : 122
% 7.99/3.08  #Tautology    : 193
% 7.99/3.08  #SimpNegUnit  : 57
% 7.99/3.08  #BackRed      : 11
% 7.99/3.08  
% 7.99/3.08  #Partial instantiations: 0
% 7.99/3.08  #Strategies tried      : 1
% 7.99/3.08  
% 7.99/3.08  Timing (in seconds)
% 7.99/3.08  ----------------------
% 7.99/3.08  Preprocessing        : 0.52
% 7.99/3.08  Parsing              : 0.27
% 7.99/3.08  CNF conversion       : 0.05
% 7.99/3.08  Main loop            : 1.65
% 7.99/3.08  Inferencing          : 0.51
% 7.99/3.08  Reduction            : 0.52
% 7.99/3.08  Demodulation         : 0.35
% 7.99/3.08  BG Simplification    : 0.06
% 7.99/3.08  Subsumption          : 0.42
% 7.99/3.08  Abstraction          : 0.07
% 7.99/3.08  MUC search           : 0.00
% 7.99/3.08  Cooper               : 0.00
% 7.99/3.08  Total                : 2.22
% 7.99/3.08  Index Insertion      : 0.00
% 7.99/3.08  Index Deletion       : 0.00
% 7.99/3.08  Index Matching       : 0.00
% 7.99/3.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------
