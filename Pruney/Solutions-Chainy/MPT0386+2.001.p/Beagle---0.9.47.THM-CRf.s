%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:08 EST 2020

% Result     : Theorem 4.17s
% Output     : CNFRefutation 4.17s
% Verified   : 
% Statistics : Number of formulae       :   54 (  72 expanded)
%              Number of leaves         :   27 (  38 expanded)
%              Depth                    :    9
%              Number of atoms          :   69 ( 118 expanded)
%              Number of equality atoms :   10 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_104,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => r1_tarski(k1_setfam_1(B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_setfam_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_99,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_setfam_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_80,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t68_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_60,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_332,plain,(
    ! [A_86,B_87] :
      ( ~ r2_hidden('#skF_1'(A_86,B_87),B_87)
      | r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_337,plain,(
    ! [A_3] : r1_tarski(A_3,A_3) ),
    inference(resolution,[status(thm)],[c_8,c_332])).

tff(c_62,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_944,plain,(
    ! [C_129,D_130,A_131] :
      ( r2_hidden(C_129,D_130)
      | ~ r2_hidden(D_130,A_131)
      | ~ r2_hidden(C_129,k1_setfam_1(A_131))
      | k1_xboole_0 = A_131 ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_962,plain,(
    ! [C_129] :
      ( r2_hidden(C_129,'#skF_7')
      | ~ r2_hidden(C_129,k1_setfam_1('#skF_8'))
      | k1_xboole_0 = '#skF_8' ) ),
    inference(resolution,[status(thm)],[c_62,c_944])).

tff(c_965,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_962])).

tff(c_395,plain,(
    ! [C_96,B_97,A_98] :
      ( r2_hidden(C_96,B_97)
      | ~ r2_hidden(C_96,A_98)
      | ~ r1_tarski(A_98,B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_408,plain,(
    ! [B_99] :
      ( r2_hidden('#skF_7',B_99)
      | ~ r1_tarski('#skF_8',B_99) ) ),
    inference(resolution,[status(thm)],[c_62,c_395])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r2_hidden('#skF_2'(A_8,B_9),B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_225,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(k1_tarski(A_72),B_73) = k1_xboole_0
      | ~ r2_hidden(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_18,plain,(
    ! [A_15,B_16] : r1_xboole_0(k4_xboole_0(A_15,B_16),B_16) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_240,plain,(
    ! [B_74,A_75] :
      ( r1_xboole_0(k1_xboole_0,B_74)
      | ~ r2_hidden(A_75,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_18])).

tff(c_250,plain,(
    ! [B_9,A_8] :
      ( r1_xboole_0(k1_xboole_0,B_9)
      | r1_xboole_0(A_8,B_9) ) ),
    inference(resolution,[status(thm)],[c_12,c_240])).

tff(c_286,plain,(
    ! [B_9] : r1_xboole_0(k1_xboole_0,B_9) ),
    inference(factorization,[status(thm),theory(equality)],[c_250])).

tff(c_372,plain,(
    ! [A_91,B_92,C_93] :
      ( ~ r1_xboole_0(A_91,B_92)
      | ~ r2_hidden(C_93,B_92)
      | ~ r2_hidden(C_93,A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_382,plain,(
    ! [C_94,B_95] :
      ( ~ r2_hidden(C_94,B_95)
      | ~ r2_hidden(C_94,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_286,c_372])).

tff(c_394,plain,(
    ~ r2_hidden('#skF_7',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_62,c_382])).

tff(c_416,plain,(
    ~ r1_tarski('#skF_8',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_408,c_394])).

tff(c_976,plain,(
    ~ r1_tarski('#skF_8','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_965,c_416])).

tff(c_984,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_337,c_976])).

tff(c_987,plain,(
    ! [C_133] :
      ( r2_hidden(C_133,'#skF_7')
      | ~ r2_hidden(C_133,k1_setfam_1('#skF_8')) ) ),
    inference(splitRight,[status(thm)],[c_962])).

tff(c_3401,plain,(
    ! [B_209] :
      ( r2_hidden('#skF_1'(k1_setfam_1('#skF_8'),B_209),'#skF_7')
      | r1_tarski(k1_setfam_1('#skF_8'),B_209) ) ),
    inference(resolution,[status(thm)],[c_8,c_987])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_3409,plain,(
    r1_tarski(k1_setfam_1('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_3401,c_6])).

tff(c_3415,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_60,c_3409])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:44:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.17/1.69  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.69  
% 4.17/1.69  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.70  %$ r2_hidden > r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_6 > #skF_7 > #skF_8 > #skF_3 > #skF_2 > #skF_1 > #skF_5 > #skF_4
% 4.17/1.70  
% 4.17/1.70  %Foreground sorts:
% 4.17/1.70  
% 4.17/1.70  
% 4.17/1.70  %Background operators:
% 4.17/1.70  
% 4.17/1.70  
% 4.17/1.70  %Foreground operators:
% 4.17/1.70  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.17/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.17/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.17/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.17/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.17/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.17/1.70  tff('#skF_7', type, '#skF_7': $i).
% 4.17/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.17/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.17/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.17/1.70  tff('#skF_8', type, '#skF_8': $i).
% 4.17/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.17/1.70  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.17/1.70  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 4.17/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.17/1.70  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.17/1.70  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.17/1.70  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.17/1.70  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.17/1.70  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 4.17/1.70  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 4.17/1.70  
% 4.17/1.71  tff(f_104, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => r1_tarski(k1_setfam_1(B), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_setfam_1)).
% 4.17/1.71  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 4.17/1.71  tff(f_99, axiom, (![A, B]: ((~(A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (![C]: (r2_hidden(C, B) <=> (![D]: (r2_hidden(D, A) => r2_hidden(C, D))))))) & ((A = k1_xboole_0) => ((B = k1_setfam_1(A)) <=> (B = k1_xboole_0))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_setfam_1)).
% 4.17/1.71  tff(f_52, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_0)).
% 4.17/1.71  tff(f_80, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t68_zfmisc_1)).
% 4.17/1.71  tff(f_56, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.17/1.71  tff(c_60, plain, (~r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.17/1.71  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.17/1.71  tff(c_332, plain, (![A_86, B_87]: (~r2_hidden('#skF_1'(A_86, B_87), B_87) | r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.17/1.71  tff(c_337, plain, (![A_3]: (r1_tarski(A_3, A_3))), inference(resolution, [status(thm)], [c_8, c_332])).
% 4.17/1.71  tff(c_62, plain, (r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_104])).
% 4.17/1.71  tff(c_944, plain, (![C_129, D_130, A_131]: (r2_hidden(C_129, D_130) | ~r2_hidden(D_130, A_131) | ~r2_hidden(C_129, k1_setfam_1(A_131)) | k1_xboole_0=A_131)), inference(cnfTransformation, [status(thm)], [f_99])).
% 4.17/1.71  tff(c_962, plain, (![C_129]: (r2_hidden(C_129, '#skF_7') | ~r2_hidden(C_129, k1_setfam_1('#skF_8')) | k1_xboole_0='#skF_8')), inference(resolution, [status(thm)], [c_62, c_944])).
% 4.17/1.71  tff(c_965, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_962])).
% 4.17/1.71  tff(c_395, plain, (![C_96, B_97, A_98]: (r2_hidden(C_96, B_97) | ~r2_hidden(C_96, A_98) | ~r1_tarski(A_98, B_97))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.17/1.71  tff(c_408, plain, (![B_99]: (r2_hidden('#skF_7', B_99) | ~r1_tarski('#skF_8', B_99))), inference(resolution, [status(thm)], [c_62, c_395])).
% 4.17/1.71  tff(c_12, plain, (![A_8, B_9]: (r2_hidden('#skF_2'(A_8, B_9), B_9) | r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.17/1.71  tff(c_225, plain, (![A_72, B_73]: (k4_xboole_0(k1_tarski(A_72), B_73)=k1_xboole_0 | ~r2_hidden(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_80])).
% 4.17/1.71  tff(c_18, plain, (![A_15, B_16]: (r1_xboole_0(k4_xboole_0(A_15, B_16), B_16))), inference(cnfTransformation, [status(thm)], [f_56])).
% 4.17/1.71  tff(c_240, plain, (![B_74, A_75]: (r1_xboole_0(k1_xboole_0, B_74) | ~r2_hidden(A_75, B_74))), inference(superposition, [status(thm), theory('equality')], [c_225, c_18])).
% 4.17/1.71  tff(c_250, plain, (![B_9, A_8]: (r1_xboole_0(k1_xboole_0, B_9) | r1_xboole_0(A_8, B_9))), inference(resolution, [status(thm)], [c_12, c_240])).
% 4.17/1.71  tff(c_286, plain, (![B_9]: (r1_xboole_0(k1_xboole_0, B_9))), inference(factorization, [status(thm), theory('equality')], [c_250])).
% 4.17/1.71  tff(c_372, plain, (![A_91, B_92, C_93]: (~r1_xboole_0(A_91, B_92) | ~r2_hidden(C_93, B_92) | ~r2_hidden(C_93, A_91))), inference(cnfTransformation, [status(thm)], [f_52])).
% 4.17/1.71  tff(c_382, plain, (![C_94, B_95]: (~r2_hidden(C_94, B_95) | ~r2_hidden(C_94, k1_xboole_0))), inference(resolution, [status(thm)], [c_286, c_372])).
% 4.17/1.71  tff(c_394, plain, (~r2_hidden('#skF_7', k1_xboole_0)), inference(resolution, [status(thm)], [c_62, c_382])).
% 4.17/1.71  tff(c_416, plain, (~r1_tarski('#skF_8', k1_xboole_0)), inference(resolution, [status(thm)], [c_408, c_394])).
% 4.17/1.71  tff(c_976, plain, (~r1_tarski('#skF_8', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_965, c_416])).
% 4.17/1.71  tff(c_984, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_337, c_976])).
% 4.17/1.71  tff(c_987, plain, (![C_133]: (r2_hidden(C_133, '#skF_7') | ~r2_hidden(C_133, k1_setfam_1('#skF_8')))), inference(splitRight, [status(thm)], [c_962])).
% 4.17/1.71  tff(c_3401, plain, (![B_209]: (r2_hidden('#skF_1'(k1_setfam_1('#skF_8'), B_209), '#skF_7') | r1_tarski(k1_setfam_1('#skF_8'), B_209))), inference(resolution, [status(thm)], [c_8, c_987])).
% 4.17/1.71  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 4.17/1.71  tff(c_3409, plain, (r1_tarski(k1_setfam_1('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_3401, c_6])).
% 4.17/1.71  tff(c_3415, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_60, c_3409])).
% 4.17/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.17/1.71  
% 4.17/1.71  Inference rules
% 4.17/1.71  ----------------------
% 4.17/1.71  #Ref     : 0
% 4.17/1.71  #Sup     : 802
% 4.17/1.71  #Fact    : 2
% 4.17/1.71  #Define  : 0
% 4.17/1.71  #Split   : 3
% 4.17/1.71  #Chain   : 0
% 4.17/1.71  #Close   : 0
% 4.17/1.71  
% 4.17/1.71  Ordering : KBO
% 4.17/1.71  
% 4.17/1.71  Simplification rules
% 4.17/1.71  ----------------------
% 4.17/1.71  #Subsume      : 157
% 4.17/1.71  #Demod        : 625
% 4.17/1.71  #Tautology    : 453
% 4.17/1.71  #SimpNegUnit  : 6
% 4.17/1.71  #BackRed      : 19
% 4.17/1.71  
% 4.17/1.71  #Partial instantiations: 0
% 4.17/1.71  #Strategies tried      : 1
% 4.17/1.71  
% 4.17/1.71  Timing (in seconds)
% 4.17/1.71  ----------------------
% 4.17/1.71  Preprocessing        : 0.34
% 4.17/1.71  Parsing              : 0.17
% 4.17/1.71  CNF conversion       : 0.03
% 4.17/1.71  Main loop            : 0.68
% 4.17/1.71  Inferencing          : 0.23
% 4.17/1.71  Reduction            : 0.26
% 4.17/1.71  Demodulation         : 0.20
% 4.17/1.71  BG Simplification    : 0.03
% 4.17/1.71  Subsumption          : 0.12
% 4.17/1.71  Abstraction          : 0.04
% 4.17/1.71  MUC search           : 0.00
% 4.17/1.71  Cooper               : 0.00
% 4.17/1.71  Total                : 1.04
% 4.17/1.71  Index Insertion      : 0.00
% 4.17/1.71  Index Deletion       : 0.00
% 4.17/1.71  Index Matching       : 0.00
% 4.17/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------
