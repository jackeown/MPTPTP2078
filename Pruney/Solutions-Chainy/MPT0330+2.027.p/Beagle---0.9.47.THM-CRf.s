%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:43 EST 2020

% Result     : Theorem 7.35s
% Output     : CNFRefutation 7.35s
% Verified   : 
% Statistics : Number of formulae       :   58 (  72 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :    9
%              Number of atoms          :   63 (  97 expanded)
%              Number of equality atoms :    7 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_38,plain,(
    ! [A_51,C_53,B_52] : k2_xboole_0(k2_zfmisc_1(A_51,C_53),k2_zfmisc_1(B_52,C_53)) = k2_zfmisc_1(k2_xboole_0(A_51,B_52),C_53) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_46,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_18,plain,(
    ! [A_17,B_18] : r1_tarski(A_17,k2_xboole_0(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_115,plain,(
    ! [A_70,C_71,B_72] :
      ( r1_tarski(A_70,C_71)
      | ~ r1_tarski(B_72,C_71)
      | ~ r1_tarski(A_70,B_72) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_128,plain,(
    ! [A_73,A_74,B_75] :
      ( r1_tarski(A_73,k2_xboole_0(A_74,B_75))
      | ~ r1_tarski(A_73,A_74) ) ),
    inference(resolution,[status(thm)],[c_18,c_115])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_490,plain,(
    ! [A_128,A_129,B_130,A_131] :
      ( r1_tarski(A_128,k2_xboole_0(A_129,B_130))
      | ~ r1_tarski(A_128,A_131)
      | ~ r1_tarski(A_131,A_129) ) ),
    inference(resolution,[status(thm)],[c_128,c_12])).

tff(c_730,plain,(
    ! [A_148,B_149] :
      ( r1_tarski('#skF_1',k2_xboole_0(A_148,B_149))
      | ~ r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),A_148) ) ),
    inference(resolution,[status(thm)],[c_46,c_490])).

tff(c_799,plain,(
    ! [B_150] : r1_tarski('#skF_1',k2_xboole_0(k2_zfmisc_1('#skF_3','#skF_4'),B_150)) ),
    inference(resolution,[status(thm)],[c_6,c_730])).

tff(c_811,plain,(
    ! [B_52] : r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3',B_52),'#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_799])).

tff(c_44,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_14,plain,(
    ! [A_12,B_13] : k2_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_181,plain,(
    ! [A_83,B_84,C_85] :
      ( r1_tarski(A_83,k2_xboole_0(B_84,C_85))
      | ~ r1_tarski(k4_xboole_0(A_83,B_84),C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_201,plain,(
    ! [A_83,B_84] : r1_tarski(A_83,k2_xboole_0(B_84,k4_xboole_0(A_83,B_84))) ),
    inference(resolution,[status(thm)],[c_6,c_181])).

tff(c_208,plain,(
    ! [A_86,B_87] : r1_tarski(A_86,k2_xboole_0(B_87,A_86)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_201])).

tff(c_259,plain,(
    ! [A_95,B_96,A_97] :
      ( r1_tarski(A_95,k2_xboole_0(B_96,A_97))
      | ~ r1_tarski(A_95,A_97) ) ),
    inference(resolution,[status(thm)],[c_208,c_12])).

tff(c_5793,plain,(
    ! [A_386,B_387,A_388,A_389] :
      ( r1_tarski(A_386,k2_xboole_0(B_387,A_388))
      | ~ r1_tarski(A_386,A_389)
      | ~ r1_tarski(A_389,A_388) ) ),
    inference(resolution,[status(thm)],[c_259,c_12])).

tff(c_6317,plain,(
    ! [B_397,A_398] :
      ( r1_tarski('#skF_2',k2_xboole_0(B_397,A_398))
      | ~ r1_tarski(k2_zfmisc_1('#skF_5','#skF_6'),A_398) ) ),
    inference(resolution,[status(thm)],[c_44,c_5793])).

tff(c_6466,plain,(
    ! [B_399] : r1_tarski('#skF_2',k2_xboole_0(B_399,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_6,c_6317])).

tff(c_6490,plain,(
    ! [A_51] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_51,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_6466])).

tff(c_40,plain,(
    ! [C_53,A_51,B_52] : k2_xboole_0(k2_zfmisc_1(C_53,A_51),k2_zfmisc_1(C_53,B_52)) = k2_zfmisc_1(C_53,k2_xboole_0(A_51,B_52)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1301,plain,(
    ! [A_179,C_180,B_181,D_182] :
      ( r1_tarski(k2_xboole_0(A_179,C_180),k2_xboole_0(B_181,D_182))
      | ~ r1_tarski(C_180,D_182)
      | ~ r1_tarski(A_179,B_181) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_7221,plain,(
    ! [B_431,A_432,A_430,C_434,C_433] :
      ( r1_tarski(k2_xboole_0(A_432,C_434),k2_zfmisc_1(C_433,k2_xboole_0(A_430,B_431)))
      | ~ r1_tarski(C_434,k2_zfmisc_1(C_433,B_431))
      | ~ r1_tarski(A_432,k2_zfmisc_1(C_433,A_430)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1301])).

tff(c_42,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_7270,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_7221,c_42])).

tff(c_7318,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_811,c_6490,c_7270])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:34:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.35/2.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.35/2.80  
% 7.35/2.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.35/2.80  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.35/2.80  
% 7.35/2.80  %Foreground sorts:
% 7.35/2.80  
% 7.35/2.80  
% 7.35/2.80  %Background operators:
% 7.35/2.80  
% 7.35/2.80  
% 7.35/2.80  %Foreground operators:
% 7.35/2.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.35/2.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.35/2.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.35/2.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.35/2.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.35/2.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.35/2.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.35/2.80  tff('#skF_5', type, '#skF_5': $i).
% 7.35/2.80  tff('#skF_6', type, '#skF_6': $i).
% 7.35/2.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.35/2.80  tff('#skF_2', type, '#skF_2': $i).
% 7.35/2.80  tff('#skF_3', type, '#skF_3': $i).
% 7.35/2.80  tff('#skF_1', type, '#skF_1': $i).
% 7.35/2.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.35/2.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.35/2.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.35/2.80  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.35/2.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.35/2.80  tff('#skF_4', type, '#skF_4': $i).
% 7.35/2.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.35/2.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.35/2.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.35/2.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.35/2.80  
% 7.35/2.82  tff(f_77, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 7.35/2.82  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 7.35/2.82  tff(f_84, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 7.35/2.82  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.35/2.82  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.35/2.82  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 7.35/2.82  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.35/2.82  tff(f_39, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.35/2.82  tff(c_38, plain, (![A_51, C_53, B_52]: (k2_xboole_0(k2_zfmisc_1(A_51, C_53), k2_zfmisc_1(B_52, C_53))=k2_zfmisc_1(k2_xboole_0(A_51, B_52), C_53))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.35/2.82  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.35/2.82  tff(c_46, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.35/2.82  tff(c_18, plain, (![A_17, B_18]: (r1_tarski(A_17, k2_xboole_0(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.35/2.82  tff(c_115, plain, (![A_70, C_71, B_72]: (r1_tarski(A_70, C_71) | ~r1_tarski(B_72, C_71) | ~r1_tarski(A_70, B_72))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.35/2.82  tff(c_128, plain, (![A_73, A_74, B_75]: (r1_tarski(A_73, k2_xboole_0(A_74, B_75)) | ~r1_tarski(A_73, A_74))), inference(resolution, [status(thm)], [c_18, c_115])).
% 7.35/2.82  tff(c_12, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.35/2.82  tff(c_490, plain, (![A_128, A_129, B_130, A_131]: (r1_tarski(A_128, k2_xboole_0(A_129, B_130)) | ~r1_tarski(A_128, A_131) | ~r1_tarski(A_131, A_129))), inference(resolution, [status(thm)], [c_128, c_12])).
% 7.35/2.82  tff(c_730, plain, (![A_148, B_149]: (r1_tarski('#skF_1', k2_xboole_0(A_148, B_149)) | ~r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), A_148))), inference(resolution, [status(thm)], [c_46, c_490])).
% 7.35/2.82  tff(c_799, plain, (![B_150]: (r1_tarski('#skF_1', k2_xboole_0(k2_zfmisc_1('#skF_3', '#skF_4'), B_150)))), inference(resolution, [status(thm)], [c_6, c_730])).
% 7.35/2.82  tff(c_811, plain, (![B_52]: (r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', B_52), '#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_799])).
% 7.35/2.82  tff(c_44, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.35/2.82  tff(c_14, plain, (![A_12, B_13]: (k2_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.35/2.82  tff(c_181, plain, (![A_83, B_84, C_85]: (r1_tarski(A_83, k2_xboole_0(B_84, C_85)) | ~r1_tarski(k4_xboole_0(A_83, B_84), C_85))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.35/2.82  tff(c_201, plain, (![A_83, B_84]: (r1_tarski(A_83, k2_xboole_0(B_84, k4_xboole_0(A_83, B_84))))), inference(resolution, [status(thm)], [c_6, c_181])).
% 7.35/2.82  tff(c_208, plain, (![A_86, B_87]: (r1_tarski(A_86, k2_xboole_0(B_87, A_86)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_201])).
% 7.35/2.82  tff(c_259, plain, (![A_95, B_96, A_97]: (r1_tarski(A_95, k2_xboole_0(B_96, A_97)) | ~r1_tarski(A_95, A_97))), inference(resolution, [status(thm)], [c_208, c_12])).
% 7.35/2.82  tff(c_5793, plain, (![A_386, B_387, A_388, A_389]: (r1_tarski(A_386, k2_xboole_0(B_387, A_388)) | ~r1_tarski(A_386, A_389) | ~r1_tarski(A_389, A_388))), inference(resolution, [status(thm)], [c_259, c_12])).
% 7.35/2.82  tff(c_6317, plain, (![B_397, A_398]: (r1_tarski('#skF_2', k2_xboole_0(B_397, A_398)) | ~r1_tarski(k2_zfmisc_1('#skF_5', '#skF_6'), A_398))), inference(resolution, [status(thm)], [c_44, c_5793])).
% 7.35/2.82  tff(c_6466, plain, (![B_399]: (r1_tarski('#skF_2', k2_xboole_0(B_399, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(resolution, [status(thm)], [c_6, c_6317])).
% 7.35/2.82  tff(c_6490, plain, (![A_51]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_51, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_38, c_6466])).
% 7.35/2.82  tff(c_40, plain, (![C_53, A_51, B_52]: (k2_xboole_0(k2_zfmisc_1(C_53, A_51), k2_zfmisc_1(C_53, B_52))=k2_zfmisc_1(C_53, k2_xboole_0(A_51, B_52)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 7.35/2.82  tff(c_1301, plain, (![A_179, C_180, B_181, D_182]: (r1_tarski(k2_xboole_0(A_179, C_180), k2_xboole_0(B_181, D_182)) | ~r1_tarski(C_180, D_182) | ~r1_tarski(A_179, B_181))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.35/2.82  tff(c_7221, plain, (![B_431, A_432, A_430, C_434, C_433]: (r1_tarski(k2_xboole_0(A_432, C_434), k2_zfmisc_1(C_433, k2_xboole_0(A_430, B_431))) | ~r1_tarski(C_434, k2_zfmisc_1(C_433, B_431)) | ~r1_tarski(A_432, k2_zfmisc_1(C_433, A_430)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1301])).
% 7.35/2.82  tff(c_42, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 7.35/2.82  tff(c_7270, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_7221, c_42])).
% 7.35/2.82  tff(c_7318, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_811, c_6490, c_7270])).
% 7.35/2.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 7.35/2.82  
% 7.35/2.82  Inference rules
% 7.35/2.82  ----------------------
% 7.35/2.82  #Ref     : 0
% 7.35/2.82  #Sup     : 1964
% 7.35/2.82  #Fact    : 0
% 7.35/2.82  #Define  : 0
% 7.35/2.82  #Split   : 6
% 7.35/2.82  #Chain   : 0
% 7.35/2.82  #Close   : 0
% 7.35/2.82  
% 7.35/2.82  Ordering : KBO
% 7.35/2.82  
% 7.35/2.82  Simplification rules
% 7.35/2.82  ----------------------
% 7.35/2.82  #Subsume      : 156
% 7.35/2.82  #Demod        : 221
% 7.35/2.82  #Tautology    : 219
% 7.35/2.82  #SimpNegUnit  : 0
% 7.35/2.82  #BackRed      : 0
% 7.35/2.82  
% 7.35/2.82  #Partial instantiations: 0
% 7.35/2.82  #Strategies tried      : 1
% 7.35/2.82  
% 7.35/2.82  Timing (in seconds)
% 7.35/2.82  ----------------------
% 7.35/2.82  Preprocessing        : 0.34
% 7.35/2.82  Parsing              : 0.18
% 7.35/2.82  CNF conversion       : 0.02
% 7.35/2.82  Main loop            : 1.73
% 7.35/2.82  Inferencing          : 0.39
% 7.35/2.82  Reduction            : 0.69
% 7.35/2.82  Demodulation         : 0.57
% 7.35/2.82  BG Simplification    : 0.06
% 7.35/2.82  Subsumption          : 0.49
% 7.35/2.82  Abstraction          : 0.06
% 7.35/2.82  MUC search           : 0.00
% 7.35/2.82  Cooper               : 0.00
% 7.35/2.82  Total                : 2.09
% 7.35/2.82  Index Insertion      : 0.00
% 7.35/2.82  Index Deletion       : 0.00
% 7.35/2.82  Index Matching       : 0.00
% 7.35/2.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
