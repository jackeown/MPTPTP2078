%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:02 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 2.95s
% Verified   : 
% Statistics : Number of formulae       :   64 (  85 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   77 ( 125 expanded)
%              Number of equality atoms :   27 (  44 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_79,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(k3_xboole_0(A,B),k1_tarski(D))
          & r2_hidden(D,C)
          & r1_xboole_0(C,B) )
       => r1_xboole_0(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t77_xboole_1)).

tff(f_64,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(c_38,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_40,plain,(
    r1_tarski(k3_xboole_0('#skF_1','#skF_2'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_372,plain,(
    ! [B_64,A_65] :
      ( k1_tarski(B_64) = A_65
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_tarski(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_394,plain,
    ( k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4')
    | k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_40,c_372])).

tff(c_419,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_394])).

tff(c_148,plain,(
    ! [A_43,B_44] :
      ( r1_xboole_0(A_43,B_44)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( r1_xboole_0(B_8,A_7)
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_154,plain,(
    ! [B_44,A_43] :
      ( r1_xboole_0(B_44,A_43)
      | k3_xboole_0(A_43,B_44) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_148,c_10])).

tff(c_36,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_161,plain,(
    ! [A_45,B_46] :
      ( k3_xboole_0(A_45,B_46) = k1_xboole_0
      | ~ r1_xboole_0(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_181,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_36,c_161])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_623,plain,(
    ! [A_79,B_80,C_81] :
      ( k3_xboole_0(A_79,k2_xboole_0(B_80,C_81)) = k3_xboole_0(A_79,C_81)
      | ~ r1_xboole_0(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_34,plain,(
    ~ r1_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_153,plain,(
    k3_xboole_0(k2_xboole_0('#skF_1','#skF_3'),'#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_148,c_34])).

tff(c_156,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_1','#skF_3')) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_153])).

tff(c_642,plain,
    ( k3_xboole_0('#skF_2','#skF_3') != k1_xboole_0
    | ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_623,c_156])).

tff(c_680,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_181,c_4,c_642])).

tff(c_696,plain,(
    k3_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_154,c_680])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_696])).

tff(c_707,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_tarski('#skF_4') ),
    inference(splitRight,[status(thm)],[c_394])).

tff(c_54,plain,(
    ! [B_34,A_35] : k3_xboole_0(B_34,A_35) = k3_xboole_0(A_35,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_12,plain,(
    ! [A_9,B_10] : r1_tarski(k3_xboole_0(A_9,B_10),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_69,plain,(
    ! [B_34,A_35] : r1_tarski(k3_xboole_0(B_34,A_35),A_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_12])).

tff(c_717,plain,(
    r1_tarski(k1_tarski('#skF_4'),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_707,c_69])).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_725,plain,(
    ! [A_82,B_83,C_84] :
      ( ~ r1_xboole_0(A_82,k3_xboole_0(B_83,C_84))
      | ~ r1_tarski(A_82,C_84)
      | r1_xboole_0(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_744,plain,(
    ! [A_82] :
      ( ~ r1_xboole_0(A_82,k1_xboole_0)
      | ~ r1_tarski(A_82,'#skF_2')
      | r1_xboole_0(A_82,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_725])).

tff(c_870,plain,(
    ! [A_90] :
      ( ~ r1_tarski(A_90,'#skF_2')
      | r1_xboole_0(A_90,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_744])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = k1_xboole_0
      | ~ r1_xboole_0(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1063,plain,(
    ! [A_99] :
      ( k3_xboole_0(A_99,'#skF_3') = k1_xboole_0
      | ~ r1_tarski(A_99,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_870,c_6])).

tff(c_1079,plain,(
    k3_xboole_0(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_717,c_1063])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k3_xboole_0(A_5,B_6) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    ! [A_49,B_50] :
      ( ~ r2_hidden(A_49,B_50)
      | ~ r1_xboole_0(k1_tarski(A_49),B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_233,plain,(
    ! [A_49,B_6] :
      ( ~ r2_hidden(A_49,B_6)
      | k3_xboole_0(k1_tarski(A_49),B_6) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_224])).

tff(c_1095,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1079,c_233])).

tff(c_1127,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:40:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.47  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.47  
% 2.95/1.47  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.47  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.95/1.47  
% 2.95/1.47  %Foreground sorts:
% 2.95/1.47  
% 2.95/1.47  
% 2.95/1.47  %Background operators:
% 2.95/1.47  
% 2.95/1.47  
% 2.95/1.47  %Foreground operators:
% 2.95/1.47  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.47  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.95/1.47  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.95/1.47  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.47  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.95/1.47  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.95/1.47  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.95/1.47  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.95/1.47  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.95/1.47  tff('#skF_2', type, '#skF_2': $i).
% 2.95/1.47  tff('#skF_3', type, '#skF_3': $i).
% 2.95/1.47  tff('#skF_1', type, '#skF_1': $i).
% 2.95/1.47  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.47  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.47  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.47  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.95/1.47  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.95/1.47  
% 2.95/1.49  tff(f_79, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(k3_xboole_0(A, B), k1_tarski(D)) & r2_hidden(D, C)) & r1_xboole_0(C, B)) => r1_xboole_0(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_zfmisc_1)).
% 2.95/1.49  tff(f_70, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.95/1.49  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.95/1.49  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.95/1.49  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.95/1.49  tff(f_53, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 2.95/1.49  tff(f_39, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.95/1.49  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.95/1.49  tff(f_49, axiom, (![A, B, C]: ~((~r1_xboole_0(A, B) & r1_tarski(A, C)) & r1_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t77_xboole_1)).
% 2.95/1.49  tff(f_64, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.95/1.49  tff(c_38, plain, (r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.49  tff(c_40, plain, (r1_tarski(k3_xboole_0('#skF_1', '#skF_2'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.49  tff(c_372, plain, (![B_64, A_65]: (k1_tarski(B_64)=A_65 | k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_tarski(B_64)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.95/1.49  tff(c_394, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4') | k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_40, c_372])).
% 2.95/1.49  tff(c_419, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_394])).
% 2.95/1.49  tff(c_148, plain, (![A_43, B_44]: (r1_xboole_0(A_43, B_44) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.49  tff(c_10, plain, (![B_8, A_7]: (r1_xboole_0(B_8, A_7) | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.95/1.49  tff(c_154, plain, (![B_44, A_43]: (r1_xboole_0(B_44, A_43) | k3_xboole_0(A_43, B_44)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_148, c_10])).
% 2.95/1.49  tff(c_36, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.49  tff(c_161, plain, (![A_45, B_46]: (k3_xboole_0(A_45, B_46)=k1_xboole_0 | ~r1_xboole_0(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.49  tff(c_181, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_36, c_161])).
% 2.95/1.49  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.95/1.49  tff(c_623, plain, (![A_79, B_80, C_81]: (k3_xboole_0(A_79, k2_xboole_0(B_80, C_81))=k3_xboole_0(A_79, C_81) | ~r1_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.95/1.49  tff(c_34, plain, (~r1_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.95/1.49  tff(c_153, plain, (k3_xboole_0(k2_xboole_0('#skF_1', '#skF_3'), '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_148, c_34])).
% 2.95/1.49  tff(c_156, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_1', '#skF_3'))!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_4, c_153])).
% 2.95/1.49  tff(c_642, plain, (k3_xboole_0('#skF_2', '#skF_3')!=k1_xboole_0 | ~r1_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_623, c_156])).
% 2.95/1.49  tff(c_680, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_181, c_4, c_642])).
% 2.95/1.49  tff(c_696, plain, (k3_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_154, c_680])).
% 2.95/1.49  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_419, c_696])).
% 2.95/1.49  tff(c_707, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_tarski('#skF_4')), inference(splitRight, [status(thm)], [c_394])).
% 2.95/1.49  tff(c_54, plain, (![B_34, A_35]: (k3_xboole_0(B_34, A_35)=k3_xboole_0(A_35, B_34))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.95/1.49  tff(c_12, plain, (![A_9, B_10]: (r1_tarski(k3_xboole_0(A_9, B_10), A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.95/1.49  tff(c_69, plain, (![B_34, A_35]: (r1_tarski(k3_xboole_0(B_34, A_35), A_35))), inference(superposition, [status(thm), theory('equality')], [c_54, c_12])).
% 2.95/1.49  tff(c_717, plain, (r1_tarski(k1_tarski('#skF_4'), '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_707, c_69])).
% 2.95/1.49  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.95/1.49  tff(c_725, plain, (![A_82, B_83, C_84]: (~r1_xboole_0(A_82, k3_xboole_0(B_83, C_84)) | ~r1_tarski(A_82, C_84) | r1_xboole_0(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.95/1.49  tff(c_744, plain, (![A_82]: (~r1_xboole_0(A_82, k1_xboole_0) | ~r1_tarski(A_82, '#skF_2') | r1_xboole_0(A_82, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_181, c_725])).
% 2.95/1.49  tff(c_870, plain, (![A_90]: (~r1_tarski(A_90, '#skF_2') | r1_xboole_0(A_90, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_744])).
% 2.95/1.49  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=k1_xboole_0 | ~r1_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.49  tff(c_1063, plain, (![A_99]: (k3_xboole_0(A_99, '#skF_3')=k1_xboole_0 | ~r1_tarski(A_99, '#skF_2'))), inference(resolution, [status(thm)], [c_870, c_6])).
% 2.95/1.49  tff(c_1079, plain, (k3_xboole_0(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_717, c_1063])).
% 2.95/1.49  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k3_xboole_0(A_5, B_6)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.95/1.49  tff(c_224, plain, (![A_49, B_50]: (~r2_hidden(A_49, B_50) | ~r1_xboole_0(k1_tarski(A_49), B_50))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.95/1.49  tff(c_233, plain, (![A_49, B_6]: (~r2_hidden(A_49, B_6) | k3_xboole_0(k1_tarski(A_49), B_6)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_224])).
% 2.95/1.49  tff(c_1095, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1079, c_233])).
% 2.95/1.49  tff(c_1127, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_1095])).
% 2.95/1.49  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.49  
% 2.95/1.49  Inference rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Ref     : 0
% 2.95/1.49  #Sup     : 258
% 2.95/1.49  #Fact    : 1
% 2.95/1.49  #Define  : 0
% 2.95/1.49  #Split   : 2
% 2.95/1.49  #Chain   : 0
% 2.95/1.49  #Close   : 0
% 2.95/1.49  
% 2.95/1.49  Ordering : KBO
% 2.95/1.49  
% 2.95/1.49  Simplification rules
% 2.95/1.49  ----------------------
% 2.95/1.49  #Subsume      : 20
% 2.95/1.49  #Demod        : 89
% 2.95/1.49  #Tautology    : 107
% 2.95/1.49  #SimpNegUnit  : 2
% 2.95/1.49  #BackRed      : 3
% 2.95/1.49  
% 2.95/1.49  #Partial instantiations: 0
% 2.95/1.49  #Strategies tried      : 1
% 2.95/1.49  
% 2.95/1.49  Timing (in seconds)
% 2.95/1.49  ----------------------
% 2.95/1.49  Preprocessing        : 0.32
% 2.95/1.49  Parsing              : 0.18
% 2.95/1.49  CNF conversion       : 0.02
% 2.95/1.49  Main loop            : 0.38
% 2.95/1.49  Inferencing          : 0.14
% 2.95/1.49  Reduction            : 0.13
% 2.95/1.49  Demodulation         : 0.10
% 2.95/1.49  BG Simplification    : 0.02
% 2.95/1.49  Subsumption          : 0.07
% 2.95/1.49  Abstraction          : 0.02
% 2.95/1.49  MUC search           : 0.00
% 2.95/1.49  Cooper               : 0.00
% 2.95/1.49  Total                : 0.73
% 2.95/1.49  Index Insertion      : 0.00
% 2.95/1.49  Index Deletion       : 0.00
% 2.95/1.49  Index Matching       : 0.00
% 2.95/1.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
