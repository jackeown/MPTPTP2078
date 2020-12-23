%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:39 EST 2020

% Result     : Theorem 4.69s
% Output     : CNFRefutation 4.69s
% Verified   : 
% Statistics : Number of formulae       :   66 (  82 expanded)
%              Number of leaves         :   36 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   63 (  89 expanded)
%              Number of equality atoms :   39 (  61 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_82,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(A,C,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_68,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_64,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_62,plain,(
    '#skF_6' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_60,plain,(
    ! [A_56,C_58,B_57] : k1_enumset1(A_56,C_58,B_57) = k1_enumset1(A_56,B_57,C_58) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_50,plain,(
    ! [A_31,B_32,C_33] : k2_enumset1(A_31,A_31,B_32,C_33) = k1_enumset1(A_31,B_32,C_33) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_48,plain,(
    ! [A_29,B_30] : k1_enumset1(A_29,A_29,B_30) = k2_tarski(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_812,plain,(
    ! [A_147,B_148,C_149,D_150] : k2_xboole_0(k1_enumset1(A_147,B_148,C_149),k1_tarski(D_150)) = k2_enumset1(A_147,B_148,C_149,D_150) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_878,plain,(
    ! [A_29,B_30,D_150] : k2_xboole_0(k2_tarski(A_29,B_30),k1_tarski(D_150)) = k2_enumset1(A_29,A_29,B_30,D_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_812])).

tff(c_886,plain,(
    ! [A_29,B_30,D_150] : k2_xboole_0(k2_tarski(A_29,B_30),k1_tarski(D_150)) = k1_enumset1(A_29,B_30,D_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_878])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_46,plain,(
    ! [A_28] : k2_tarski(A_28,A_28) = k1_tarski(A_28) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_888,plain,(
    ! [A_151,B_152,D_153] : k2_xboole_0(k2_tarski(A_151,B_152),k1_tarski(D_153)) = k1_enumset1(A_151,B_152,D_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_878])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_tarski(A_13,k2_xboole_0(A_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_954,plain,(
    ! [A_154,B_155,D_156] : r1_tarski(k2_tarski(A_154,B_155),k1_enumset1(A_154,B_155,D_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_16])).

tff(c_976,plain,(
    ! [A_29,B_30] : r1_tarski(k2_tarski(A_29,A_29),k2_tarski(A_29,B_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_954])).

tff(c_984,plain,(
    ! [A_29,B_30] : r1_tarski(k1_tarski(A_29),k2_tarski(A_29,B_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_976])).

tff(c_66,plain,(
    r1_tarski(k2_tarski('#skF_3','#skF_4'),k2_tarski('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_431,plain,(
    ! [A_110,C_111,B_112] :
      ( r1_tarski(A_110,C_111)
      | ~ r1_tarski(B_112,C_111)
      | ~ r1_tarski(A_110,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_522,plain,(
    ! [A_122] :
      ( r1_tarski(A_122,k2_tarski('#skF_5','#skF_6'))
      | ~ r1_tarski(A_122,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_66,c_431])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1211,plain,(
    ! [A_172] :
      ( k4_xboole_0(A_172,k2_tarski('#skF_5','#skF_6')) = k1_xboole_0
      | ~ r1_tarski(A_172,k2_tarski('#skF_3','#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_522,c_4])).

tff(c_1230,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_5','#skF_6')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_984,c_1211])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1240,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_3')) = k5_xboole_0(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_18])).

tff(c_1244,plain,(
    k1_enumset1('#skF_5','#skF_3','#skF_6') = k2_tarski('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_886,c_14,c_1240])).

tff(c_24,plain,(
    ! [E_23,A_17,C_19] : r2_hidden(E_23,k1_enumset1(A_17,E_23,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1258,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1244,c_24])).

tff(c_1082,plain,(
    ! [E_164,C_165,B_166,A_167] :
      ( E_164 = C_165
      | E_164 = B_166
      | E_164 = A_167
      | ~ r2_hidden(E_164,k1_enumset1(A_167,B_166,C_165)) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_3811,plain,(
    ! [E_351,B_352,A_353] :
      ( E_351 = B_352
      | E_351 = A_353
      | E_351 = A_353
      | ~ r2_hidden(E_351,k2_tarski(A_353,B_352)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1082])).

tff(c_3822,plain,
    ( '#skF_6' = '#skF_3'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1258,c_3811])).

tff(c_3837,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_62,c_3822])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:37:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.69/1.89  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.89  
% 4.69/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.89  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 4.69/1.89  
% 4.69/1.89  %Foreground sorts:
% 4.69/1.89  
% 4.69/1.89  
% 4.69/1.89  %Background operators:
% 4.69/1.89  
% 4.69/1.89  
% 4.69/1.89  %Foreground operators:
% 4.69/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.69/1.89  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.69/1.89  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.69/1.89  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.69/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.69/1.89  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.69/1.89  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.69/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.69/1.89  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.69/1.89  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.69/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.69/1.89  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.69/1.89  tff('#skF_6', type, '#skF_6': $i).
% 4.69/1.89  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.69/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.69/1.89  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.89  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.69/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.69/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.69/1.89  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.69/1.89  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.69/1.89  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.69/1.89  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.69/1.89  
% 4.69/1.90  tff(f_92, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 4.69/1.90  tff(f_82, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(A, C, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_enumset1)).
% 4.69/1.90  tff(f_72, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.69/1.90  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.69/1.90  tff(f_66, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.69/1.90  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.69/1.90  tff(f_68, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.69/1.91  tff(f_47, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.69/1.91  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 4.69/1.91  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 4.69/1.91  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.69/1.91  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.69/1.91  tff(c_64, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.69/1.91  tff(c_62, plain, ('#skF_6'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.69/1.91  tff(c_60, plain, (![A_56, C_58, B_57]: (k1_enumset1(A_56, C_58, B_57)=k1_enumset1(A_56, B_57, C_58))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.69/1.91  tff(c_50, plain, (![A_31, B_32, C_33]: (k2_enumset1(A_31, A_31, B_32, C_33)=k1_enumset1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_72])).
% 4.69/1.91  tff(c_48, plain, (![A_29, B_30]: (k1_enumset1(A_29, A_29, B_30)=k2_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_70])).
% 4.69/1.91  tff(c_812, plain, (![A_147, B_148, C_149, D_150]: (k2_xboole_0(k1_enumset1(A_147, B_148, C_149), k1_tarski(D_150))=k2_enumset1(A_147, B_148, C_149, D_150))), inference(cnfTransformation, [status(thm)], [f_66])).
% 4.69/1.91  tff(c_878, plain, (![A_29, B_30, D_150]: (k2_xboole_0(k2_tarski(A_29, B_30), k1_tarski(D_150))=k2_enumset1(A_29, A_29, B_30, D_150))), inference(superposition, [status(thm), theory('equality')], [c_48, c_812])).
% 4.69/1.91  tff(c_886, plain, (![A_29, B_30, D_150]: (k2_xboole_0(k2_tarski(A_29, B_30), k1_tarski(D_150))=k1_enumset1(A_29, B_30, D_150))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_878])).
% 4.69/1.91  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.69/1.91  tff(c_46, plain, (![A_28]: (k2_tarski(A_28, A_28)=k1_tarski(A_28))), inference(cnfTransformation, [status(thm)], [f_68])).
% 4.69/1.91  tff(c_888, plain, (![A_151, B_152, D_153]: (k2_xboole_0(k2_tarski(A_151, B_152), k1_tarski(D_153))=k1_enumset1(A_151, B_152, D_153))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_878])).
% 4.69/1.91  tff(c_16, plain, (![A_13, B_14]: (r1_tarski(A_13, k2_xboole_0(A_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.69/1.91  tff(c_954, plain, (![A_154, B_155, D_156]: (r1_tarski(k2_tarski(A_154, B_155), k1_enumset1(A_154, B_155, D_156)))), inference(superposition, [status(thm), theory('equality')], [c_888, c_16])).
% 4.69/1.91  tff(c_976, plain, (![A_29, B_30]: (r1_tarski(k2_tarski(A_29, A_29), k2_tarski(A_29, B_30)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_954])).
% 4.69/1.91  tff(c_984, plain, (![A_29, B_30]: (r1_tarski(k1_tarski(A_29), k2_tarski(A_29, B_30)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_976])).
% 4.69/1.91  tff(c_66, plain, (r1_tarski(k2_tarski('#skF_3', '#skF_4'), k2_tarski('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.69/1.91  tff(c_431, plain, (![A_110, C_111, B_112]: (r1_tarski(A_110, C_111) | ~r1_tarski(B_112, C_111) | ~r1_tarski(A_110, B_112))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.69/1.91  tff(c_522, plain, (![A_122]: (r1_tarski(A_122, k2_tarski('#skF_5', '#skF_6')) | ~r1_tarski(A_122, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_66, c_431])).
% 4.69/1.91  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.69/1.91  tff(c_1211, plain, (![A_172]: (k4_xboole_0(A_172, k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0 | ~r1_tarski(A_172, k2_tarski('#skF_3', '#skF_4')))), inference(resolution, [status(thm)], [c_522, c_4])).
% 4.69/1.91  tff(c_1230, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_5', '#skF_6'))=k1_xboole_0), inference(resolution, [status(thm)], [c_984, c_1211])).
% 4.69/1.91  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.69/1.91  tff(c_1240, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_3'))=k5_xboole_0(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1230, c_18])).
% 4.69/1.91  tff(c_1244, plain, (k1_enumset1('#skF_5', '#skF_3', '#skF_6')=k2_tarski('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_60, c_886, c_14, c_1240])).
% 4.69/1.91  tff(c_24, plain, (![E_23, A_17, C_19]: (r2_hidden(E_23, k1_enumset1(A_17, E_23, C_19)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.69/1.91  tff(c_1258, plain, (r2_hidden('#skF_3', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_1244, c_24])).
% 4.69/1.91  tff(c_1082, plain, (![E_164, C_165, B_166, A_167]: (E_164=C_165 | E_164=B_166 | E_164=A_167 | ~r2_hidden(E_164, k1_enumset1(A_167, B_166, C_165)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.69/1.91  tff(c_3811, plain, (![E_351, B_352, A_353]: (E_351=B_352 | E_351=A_353 | E_351=A_353 | ~r2_hidden(E_351, k2_tarski(A_353, B_352)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1082])).
% 4.69/1.91  tff(c_3822, plain, ('#skF_6'='#skF_3' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_1258, c_3811])).
% 4.69/1.91  tff(c_3837, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_62, c_3822])).
% 4.69/1.91  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.69/1.91  
% 4.69/1.91  Inference rules
% 4.69/1.91  ----------------------
% 4.69/1.91  #Ref     : 0
% 4.69/1.91  #Sup     : 959
% 4.69/1.91  #Fact    : 0
% 4.69/1.91  #Define  : 0
% 4.69/1.91  #Split   : 0
% 4.69/1.91  #Chain   : 0
% 4.69/1.91  #Close   : 0
% 4.69/1.91  
% 4.69/1.91  Ordering : KBO
% 4.69/1.91  
% 4.69/1.91  Simplification rules
% 4.69/1.91  ----------------------
% 4.69/1.91  #Subsume      : 51
% 4.69/1.91  #Demod        : 603
% 4.69/1.91  #Tautology    : 552
% 4.69/1.91  #SimpNegUnit  : 1
% 4.69/1.91  #BackRed      : 0
% 4.69/1.91  
% 4.69/1.91  #Partial instantiations: 0
% 4.69/1.91  #Strategies tried      : 1
% 4.69/1.91  
% 4.69/1.91  Timing (in seconds)
% 4.69/1.91  ----------------------
% 4.69/1.91  Preprocessing        : 0.33
% 4.69/1.91  Parsing              : 0.17
% 4.69/1.91  CNF conversion       : 0.02
% 4.69/1.91  Main loop            : 0.82
% 4.69/1.91  Inferencing          : 0.26
% 4.69/1.91  Reduction            : 0.33
% 4.69/1.91  Demodulation         : 0.26
% 4.69/1.91  BG Simplification    : 0.03
% 4.69/1.91  Subsumption          : 0.14
% 4.69/1.91  Abstraction          : 0.04
% 4.69/1.91  MUC search           : 0.00
% 4.69/1.91  Cooper               : 0.00
% 4.69/1.91  Total                : 1.17
% 4.69/1.91  Index Insertion      : 0.00
% 4.69/1.91  Index Deletion       : 0.00
% 4.69/1.91  Index Matching       : 0.00
% 4.69/1.91  BG Taut test         : 0.00
%------------------------------------------------------------------------------
