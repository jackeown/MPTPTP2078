%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:03 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 3.78s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 151 expanded)
%              Number of leaves         :   21 (  61 expanded)
%              Depth                    :   18
%              Number of atoms          :  104 ( 300 expanded)
%              Number of equality atoms :   44 ( 131 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( A != k1_tarski(B)
          & A != k1_xboole_0
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & C != B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k4_xboole_0(B,A)
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_xboole_1)).

tff(c_30,plain,(
    k1_tarski('#skF_4') != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_41,plain,(
    ! [A_24] :
      ( r2_hidden('#skF_2'(A_24),A_24)
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [C_21] :
      ( C_21 = '#skF_4'
      | ~ r2_hidden(C_21,'#skF_3') ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_45,plain,
    ( '#skF_2'('#skF_3') = '#skF_4'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_41,c_26])).

tff(c_48,plain,(
    '#skF_2'('#skF_3') = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_45])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,
    ( r2_hidden('#skF_4','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_8])).

tff(c_56,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_53])).

tff(c_87,plain,(
    ! [A_35,B_36] :
      ( r2_hidden('#skF_1'(A_35,B_36),A_35)
      | r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_131,plain,(
    ! [B_41] :
      ( '#skF_1'('#skF_3',B_41) = '#skF_4'
      | r1_tarski('#skF_3',B_41) ) ),
    inference(resolution,[status(thm)],[c_87,c_26])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = k1_xboole_0
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_135,plain,(
    ! [B_41] :
      ( k4_xboole_0('#skF_3',B_41) = k1_xboole_0
      | '#skF_1'('#skF_3',B_41) = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_131,c_12])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( k4_xboole_0(k1_tarski(A_18),B_19) = k1_xboole_0
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_124,plain,(
    ! [B_39,A_40] :
      ( B_39 = A_40
      | k4_xboole_0(B_39,A_40) != k4_xboole_0(A_40,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_231,plain,(
    ! [A_57,B_58] :
      ( k1_tarski(A_57) = B_58
      | k4_xboole_0(B_58,k1_tarski(A_57)) != k1_xboole_0
      | ~ r2_hidden(A_57,B_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_124])).

tff(c_244,plain,(
    ! [A_57] :
      ( k1_tarski(A_57) = '#skF_3'
      | ~ r2_hidden(A_57,'#skF_3')
      | '#skF_1'('#skF_3',k1_tarski(A_57)) = '#skF_4' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_231])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_98,plain,(
    ! [A_37] : r1_tarski(A_37,A_37) ),
    inference(resolution,[status(thm)],[c_87,c_4])).

tff(c_102,plain,(
    ! [A_37] : k4_xboole_0(A_37,A_37) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_98,c_12])).

tff(c_136,plain,(
    ! [A_42,B_43] :
      ( r2_hidden(A_42,B_43)
      | k4_xboole_0(k1_tarski(A_42),B_43) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_144,plain,(
    ! [A_42] : r2_hidden(A_42,k1_tarski(A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_136])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( r1_tarski(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_181,plain,(
    ! [C_49,B_50,A_51] :
      ( r2_hidden(C_49,B_50)
      | ~ r2_hidden(C_49,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_369,plain,(
    ! [A_69,B_70,B_71] :
      ( r2_hidden('#skF_1'(A_69,B_70),B_71)
      | ~ r1_tarski(A_69,B_71)
      | r1_tarski(A_69,B_70) ) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_383,plain,(
    ! [A_72,B_73] :
      ( '#skF_1'(A_72,B_73) = '#skF_4'
      | ~ r1_tarski(A_72,'#skF_3')
      | r1_tarski(A_72,B_73) ) ),
    inference(resolution,[status(thm)],[c_369,c_26])).

tff(c_418,plain,(
    ! [A_78,B_79] :
      ( '#skF_1'(A_78,B_79) = '#skF_4'
      | r1_tarski(A_78,B_79)
      | k4_xboole_0(A_78,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_383])).

tff(c_190,plain,(
    ! [A_42,B_50] :
      ( r2_hidden(A_42,B_50)
      | ~ r1_tarski(k1_tarski(A_42),B_50) ) ),
    inference(resolution,[status(thm)],[c_144,c_181])).

tff(c_1078,plain,(
    ! [A_127,B_128] :
      ( r2_hidden(A_127,B_128)
      | '#skF_1'(k1_tarski(A_127),B_128) = '#skF_4'
      | k4_xboole_0(k1_tarski(A_127),'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_418,c_190])).

tff(c_1087,plain,(
    ! [A_129,B_130] :
      ( r2_hidden(A_129,B_130)
      | '#skF_1'(k1_tarski(A_129),B_130) = '#skF_4'
      | ~ r2_hidden(A_129,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1078])).

tff(c_1455,plain,(
    ! [B_150,A_151] :
      ( ~ r2_hidden('#skF_4',B_150)
      | r1_tarski(k1_tarski(A_151),B_150)
      | r2_hidden(A_151,B_150)
      | ~ r2_hidden(A_151,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1087,c_4])).

tff(c_1511,plain,(
    ! [B_152,A_153] :
      ( ~ r2_hidden('#skF_4',B_152)
      | r2_hidden(A_153,B_152)
      | ~ r2_hidden(A_153,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1455,c_190])).

tff(c_1531,plain,(
    ! [A_154] :
      ( r2_hidden(A_154,k1_tarski('#skF_4'))
      | ~ r2_hidden(A_154,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_144,c_1511])).

tff(c_1725,plain,(
    ! [A_161] :
      ( r1_tarski(A_161,k1_tarski('#skF_4'))
      | ~ r2_hidden('#skF_1'(A_161,k1_tarski('#skF_4')),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_1531,c_4])).

tff(c_1745,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_4','#skF_3')
    | k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_1725])).

tff(c_1760,plain,
    ( r1_tarski('#skF_3',k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_1745])).

tff(c_1761,plain,(
    r1_tarski('#skF_3',k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1760])).

tff(c_1801,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1761,c_12])).

tff(c_127,plain,(
    ! [A_18,B_19] :
      ( k1_tarski(A_18) = B_19
      | k4_xboole_0(B_19,k1_tarski(A_18)) != k1_xboole_0
      | ~ r2_hidden(A_18,B_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_124])).

tff(c_1812,plain,
    ( k1_tarski('#skF_4') = '#skF_3'
    | ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1801,c_127])).

tff(c_1829,plain,(
    k1_tarski('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1812])).

tff(c_1831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_1829])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:16:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.63  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.64  
% 3.78/1.64  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.64  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.78/1.64  
% 3.78/1.64  %Foreground sorts:
% 3.78/1.64  
% 3.78/1.64  
% 3.78/1.64  %Background operators:
% 3.78/1.64  
% 3.78/1.64  
% 3.78/1.64  %Foreground operators:
% 3.78/1.64  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.78/1.64  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.78/1.64  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.78/1.64  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.78/1.64  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.78/1.64  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.78/1.64  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.78/1.64  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.78/1.64  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.78/1.64  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.78/1.64  tff('#skF_3', type, '#skF_3': $i).
% 3.78/1.64  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.78/1.64  tff('#skF_4', type, '#skF_4': $i).
% 3.78/1.64  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.78/1.64  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.78/1.64  
% 3.78/1.66  tff(f_73, negated_conjecture, ~(![A, B]: ~((~(A = k1_tarski(B)) & ~(A = k1_xboole_0)) & (![C]: ~(r2_hidden(C, A) & ~(C = B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_zfmisc_1)).
% 3.78/1.66  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.78/1.66  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.78/1.66  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.78/1.66  tff(f_58, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 3.78/1.66  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(A, B) = k4_xboole_0(B, A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_xboole_1)).
% 3.78/1.66  tff(c_30, plain, (k1_tarski('#skF_4')!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.78/1.66  tff(c_28, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.78/1.66  tff(c_41, plain, (![A_24]: (r2_hidden('#skF_2'(A_24), A_24) | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.78/1.66  tff(c_26, plain, (![C_21]: (C_21='#skF_4' | ~r2_hidden(C_21, '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.78/1.66  tff(c_45, plain, ('#skF_2'('#skF_3')='#skF_4' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_41, c_26])).
% 3.78/1.66  tff(c_48, plain, ('#skF_2'('#skF_3')='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_28, c_45])).
% 3.78/1.66  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.78/1.66  tff(c_53, plain, (r2_hidden('#skF_4', '#skF_3') | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_48, c_8])).
% 3.78/1.66  tff(c_56, plain, (r2_hidden('#skF_4', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_28, c_53])).
% 3.78/1.66  tff(c_87, plain, (![A_35, B_36]: (r2_hidden('#skF_1'(A_35, B_36), A_35) | r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.66  tff(c_131, plain, (![B_41]: ('#skF_1'('#skF_3', B_41)='#skF_4' | r1_tarski('#skF_3', B_41))), inference(resolution, [status(thm)], [c_87, c_26])).
% 3.78/1.66  tff(c_12, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=k1_xboole_0 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.78/1.66  tff(c_135, plain, (![B_41]: (k4_xboole_0('#skF_3', B_41)=k1_xboole_0 | '#skF_1'('#skF_3', B_41)='#skF_4')), inference(resolution, [status(thm)], [c_131, c_12])).
% 3.78/1.66  tff(c_24, plain, (![A_18, B_19]: (k4_xboole_0(k1_tarski(A_18), B_19)=k1_xboole_0 | ~r2_hidden(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.78/1.66  tff(c_124, plain, (![B_39, A_40]: (B_39=A_40 | k4_xboole_0(B_39, A_40)!=k4_xboole_0(A_40, B_39))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.78/1.66  tff(c_231, plain, (![A_57, B_58]: (k1_tarski(A_57)=B_58 | k4_xboole_0(B_58, k1_tarski(A_57))!=k1_xboole_0 | ~r2_hidden(A_57, B_58))), inference(superposition, [status(thm), theory('equality')], [c_24, c_124])).
% 3.78/1.66  tff(c_244, plain, (![A_57]: (k1_tarski(A_57)='#skF_3' | ~r2_hidden(A_57, '#skF_3') | '#skF_1'('#skF_3', k1_tarski(A_57))='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_135, c_231])).
% 3.78/1.66  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.66  tff(c_98, plain, (![A_37]: (r1_tarski(A_37, A_37))), inference(resolution, [status(thm)], [c_87, c_4])).
% 3.78/1.66  tff(c_102, plain, (![A_37]: (k4_xboole_0(A_37, A_37)=k1_xboole_0)), inference(resolution, [status(thm)], [c_98, c_12])).
% 3.78/1.66  tff(c_136, plain, (![A_42, B_43]: (r2_hidden(A_42, B_43) | k4_xboole_0(k1_tarski(A_42), B_43)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.78/1.66  tff(c_144, plain, (![A_42]: (r2_hidden(A_42, k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_136])).
% 3.78/1.66  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(A_8, B_9) | k4_xboole_0(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.78/1.66  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.66  tff(c_181, plain, (![C_49, B_50, A_51]: (r2_hidden(C_49, B_50) | ~r2_hidden(C_49, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.78/1.66  tff(c_369, plain, (![A_69, B_70, B_71]: (r2_hidden('#skF_1'(A_69, B_70), B_71) | ~r1_tarski(A_69, B_71) | r1_tarski(A_69, B_70))), inference(resolution, [status(thm)], [c_6, c_181])).
% 3.78/1.66  tff(c_383, plain, (![A_72, B_73]: ('#skF_1'(A_72, B_73)='#skF_4' | ~r1_tarski(A_72, '#skF_3') | r1_tarski(A_72, B_73))), inference(resolution, [status(thm)], [c_369, c_26])).
% 3.78/1.66  tff(c_418, plain, (![A_78, B_79]: ('#skF_1'(A_78, B_79)='#skF_4' | r1_tarski(A_78, B_79) | k4_xboole_0(A_78, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_383])).
% 3.78/1.66  tff(c_190, plain, (![A_42, B_50]: (r2_hidden(A_42, B_50) | ~r1_tarski(k1_tarski(A_42), B_50))), inference(resolution, [status(thm)], [c_144, c_181])).
% 3.78/1.66  tff(c_1078, plain, (![A_127, B_128]: (r2_hidden(A_127, B_128) | '#skF_1'(k1_tarski(A_127), B_128)='#skF_4' | k4_xboole_0(k1_tarski(A_127), '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_418, c_190])).
% 3.78/1.66  tff(c_1087, plain, (![A_129, B_130]: (r2_hidden(A_129, B_130) | '#skF_1'(k1_tarski(A_129), B_130)='#skF_4' | ~r2_hidden(A_129, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1078])).
% 3.78/1.66  tff(c_1455, plain, (![B_150, A_151]: (~r2_hidden('#skF_4', B_150) | r1_tarski(k1_tarski(A_151), B_150) | r2_hidden(A_151, B_150) | ~r2_hidden(A_151, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1087, c_4])).
% 3.78/1.66  tff(c_1511, plain, (![B_152, A_153]: (~r2_hidden('#skF_4', B_152) | r2_hidden(A_153, B_152) | ~r2_hidden(A_153, '#skF_3'))), inference(resolution, [status(thm)], [c_1455, c_190])).
% 3.78/1.66  tff(c_1531, plain, (![A_154]: (r2_hidden(A_154, k1_tarski('#skF_4')) | ~r2_hidden(A_154, '#skF_3'))), inference(resolution, [status(thm)], [c_144, c_1511])).
% 3.78/1.66  tff(c_1725, plain, (![A_161]: (r1_tarski(A_161, k1_tarski('#skF_4')) | ~r2_hidden('#skF_1'(A_161, k1_tarski('#skF_4')), '#skF_3'))), inference(resolution, [status(thm)], [c_1531, c_4])).
% 3.78/1.66  tff(c_1745, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | ~r2_hidden('#skF_4', '#skF_3') | k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_244, c_1725])).
% 3.78/1.66  tff(c_1760, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4')) | k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_1745])).
% 3.78/1.66  tff(c_1761, plain, (r1_tarski('#skF_3', k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_30, c_1760])).
% 3.78/1.66  tff(c_1801, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_1761, c_12])).
% 3.78/1.66  tff(c_127, plain, (![A_18, B_19]: (k1_tarski(A_18)=B_19 | k4_xboole_0(B_19, k1_tarski(A_18))!=k1_xboole_0 | ~r2_hidden(A_18, B_19))), inference(superposition, [status(thm), theory('equality')], [c_24, c_124])).
% 3.78/1.66  tff(c_1812, plain, (k1_tarski('#skF_4')='#skF_3' | ~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1801, c_127])).
% 3.78/1.66  tff(c_1829, plain, (k1_tarski('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1812])).
% 3.78/1.66  tff(c_1831, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_1829])).
% 3.78/1.66  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.78/1.66  
% 3.78/1.66  Inference rules
% 3.78/1.66  ----------------------
% 3.78/1.66  #Ref     : 1
% 3.78/1.66  #Sup     : 413
% 3.78/1.66  #Fact    : 0
% 3.78/1.66  #Define  : 0
% 3.78/1.66  #Split   : 0
% 3.78/1.66  #Chain   : 0
% 3.78/1.66  #Close   : 0
% 3.78/1.66  
% 3.78/1.66  Ordering : KBO
% 3.78/1.66  
% 3.78/1.66  Simplification rules
% 3.78/1.66  ----------------------
% 3.78/1.66  #Subsume      : 121
% 3.78/1.66  #Demod        : 52
% 3.78/1.66  #Tautology    : 91
% 3.78/1.66  #SimpNegUnit  : 18
% 3.78/1.66  #BackRed      : 0
% 3.78/1.66  
% 3.78/1.66  #Partial instantiations: 0
% 3.78/1.66  #Strategies tried      : 1
% 3.78/1.66  
% 3.78/1.66  Timing (in seconds)
% 3.78/1.66  ----------------------
% 3.78/1.66  Preprocessing        : 0.30
% 3.78/1.66  Parsing              : 0.16
% 3.78/1.66  CNF conversion       : 0.02
% 3.78/1.66  Main loop            : 0.59
% 3.78/1.66  Inferencing          : 0.20
% 3.78/1.66  Reduction            : 0.15
% 3.78/1.66  Demodulation         : 0.09
% 3.78/1.66  BG Simplification    : 0.02
% 3.78/1.66  Subsumption          : 0.17
% 3.78/1.66  Abstraction          : 0.03
% 3.78/1.66  MUC search           : 0.00
% 3.78/1.66  Cooper               : 0.00
% 3.78/1.66  Total                : 0.92
% 3.78/1.66  Index Insertion      : 0.00
% 3.78/1.66  Index Deletion       : 0.00
% 3.78/1.66  Index Matching       : 0.00
% 3.78/1.66  BG Taut test         : 0.00
%------------------------------------------------------------------------------
