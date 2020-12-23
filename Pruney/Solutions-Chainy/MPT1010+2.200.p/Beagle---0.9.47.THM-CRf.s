%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:32 EST 2020

% Result     : Theorem 2.61s
% Output     : CNFRefutation 2.61s
% Verified   : 
% Statistics : Number of formulae       :   68 (  80 expanded)
%              Number of leaves         :   40 (  48 expanded)
%              Depth                    :    7
%              Number of atoms          :   93 ( 137 expanded)
%              Number of equality atoms :   59 (  71 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_96,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,k1_tarski(B))
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,k1_tarski(B)))) )
       => ( r2_hidden(C,A)
         => k1_funct_1(D,C) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_2)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_71,axiom,(
    ! [A,B,C,D,E,F] :
      ( F = k3_enumset1(A,B,C,D,E)
    <=> ! [G] :
          ( r2_hidden(G,F)
        <=> ~ ( G != A
              & G != B
              & G != C
              & G != D
              & G != E ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_enumset1)).

tff(c_66,plain,(
    k1_funct_1('#skF_6','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_132,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_141,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_144,plain,(
    ! [A_1] : k4_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_22,plain,(
    ! [B_35] : k4_xboole_0(k1_tarski(B_35),k1_tarski(B_35)) != k1_tarski(B_35) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    ! [B_35] : k1_tarski(B_35) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_22])).

tff(c_74,plain,(
    v1_funct_1('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_72,plain,(
    v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_70,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1(k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_68,plain,(
    r2_hidden('#skF_5','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_335,plain,(
    ! [D_157,C_158,B_159,A_160] :
      ( r2_hidden(k1_funct_1(D_157,C_158),B_159)
      | k1_xboole_0 = B_159
      | ~ r2_hidden(C_158,A_160)
      | ~ m1_subset_1(D_157,k1_zfmisc_1(k2_zfmisc_1(A_160,B_159)))
      | ~ v1_funct_2(D_157,A_160,B_159)
      | ~ v1_funct_1(D_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_423,plain,(
    ! [D_170,B_171] :
      ( r2_hidden(k1_funct_1(D_170,'#skF_5'),B_171)
      | k1_xboole_0 = B_171
      | ~ m1_subset_1(D_170,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_171)))
      | ~ v1_funct_2(D_170,'#skF_3',B_171)
      | ~ v1_funct_1(D_170) ) ),
    inference(resolution,[status(thm)],[c_68,c_335])).

tff(c_426,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0
    | ~ v1_funct_2('#skF_6','#skF_3',k1_tarski('#skF_4'))
    | ~ v1_funct_1('#skF_6') ),
    inference(resolution,[status(thm)],[c_70,c_423])).

tff(c_429,plain,
    ( r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4'))
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_72,c_426])).

tff(c_430,plain,(
    r2_hidden(k1_funct_1('#skF_6','#skF_5'),k1_tarski('#skF_4')) ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_429])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8] : k1_enumset1(A_7,A_7,B_8) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k2_enumset1(A_9,A_9,B_10,C_11) = k1_enumset1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14,D_15] : k3_enumset1(A_12,A_12,B_13,C_14,D_15) = k2_enumset1(A_12,B_13,C_14,D_15) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_282,plain,(
    ! [E_151,G_147,D_148,B_149,A_146,C_150] :
      ( G_147 = E_151
      | G_147 = D_148
      | G_147 = C_150
      | G_147 = B_149
      | G_147 = A_146
      | ~ r2_hidden(G_147,k3_enumset1(A_146,B_149,C_150,D_148,E_151)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_311,plain,(
    ! [G_156,C_155,B_152,A_153,D_154] :
      ( G_156 = D_154
      | G_156 = C_155
      | G_156 = B_152
      | G_156 = A_153
      | G_156 = A_153
      | ~ r2_hidden(G_156,k2_enumset1(A_153,B_152,C_155,D_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_282])).

tff(c_384,plain,(
    ! [G_161,C_162,B_163,A_164] :
      ( G_161 = C_162
      | G_161 = B_163
      | G_161 = A_164
      | G_161 = A_164
      | G_161 = A_164
      | ~ r2_hidden(G_161,k1_enumset1(A_164,B_163,C_162)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_311])).

tff(c_403,plain,(
    ! [G_165,B_166,A_167] :
      ( G_165 = B_166
      | G_165 = A_167
      | G_165 = A_167
      | G_165 = A_167
      | G_165 = A_167
      | ~ r2_hidden(G_165,k2_tarski(A_167,B_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_384])).

tff(c_412,plain,(
    ! [G_165,A_6] :
      ( G_165 = A_6
      | G_165 = A_6
      | G_165 = A_6
      | G_165 = A_6
      | G_165 = A_6
      | ~ r2_hidden(G_165,k1_tarski(A_6)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_403])).

tff(c_433,plain,(
    k1_funct_1('#skF_6','#skF_5') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_430,c_412])).

tff(c_439,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_66,c_66,c_66,c_66,c_433])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.61/1.34  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.34  
% 2.61/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.34  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.61/1.34  
% 2.61/1.34  %Foreground sorts:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Background operators:
% 2.61/1.34  
% 2.61/1.34  
% 2.61/1.34  %Foreground operators:
% 2.61/1.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.61/1.34  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.61/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.61/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.61/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.61/1.34  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.61/1.34  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.61/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.61/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.61/1.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.61/1.34  tff('#skF_6', type, '#skF_6': $i).
% 2.61/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.61/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.61/1.34  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.61/1.34  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.61/1.34  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.61/1.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.61/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.61/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.61/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.61/1.34  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.61/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.61/1.34  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.61/1.34  
% 2.61/1.36  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.61/1.36  tff(f_31, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.61/1.36  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.61/1.36  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.61/1.36  tff(f_50, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.61/1.36  tff(f_85, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.61/1.36  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.61/1.36  tff(f_35, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.61/1.36  tff(f_37, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.61/1.36  tff(f_39, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.61/1.36  tff(f_71, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.61/1.36  tff(c_66, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.36  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.61/1.36  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.61/1.36  tff(c_132, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.61/1.36  tff(c_141, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_132])).
% 2.61/1.36  tff(c_144, plain, (![A_1]: (k4_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_141])).
% 2.61/1.36  tff(c_22, plain, (![B_35]: (k4_xboole_0(k1_tarski(B_35), k1_tarski(B_35))!=k1_tarski(B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.61/1.36  tff(c_145, plain, (![B_35]: (k1_tarski(B_35)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_144, c_22])).
% 2.61/1.36  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.36  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.36  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.36  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.61/1.36  tff(c_335, plain, (![D_157, C_158, B_159, A_160]: (r2_hidden(k1_funct_1(D_157, C_158), B_159) | k1_xboole_0=B_159 | ~r2_hidden(C_158, A_160) | ~m1_subset_1(D_157, k1_zfmisc_1(k2_zfmisc_1(A_160, B_159))) | ~v1_funct_2(D_157, A_160, B_159) | ~v1_funct_1(D_157))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.61/1.36  tff(c_423, plain, (![D_170, B_171]: (r2_hidden(k1_funct_1(D_170, '#skF_5'), B_171) | k1_xboole_0=B_171 | ~m1_subset_1(D_170, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_171))) | ~v1_funct_2(D_170, '#skF_3', B_171) | ~v1_funct_1(D_170))), inference(resolution, [status(thm)], [c_68, c_335])).
% 2.61/1.36  tff(c_426, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_423])).
% 2.61/1.36  tff(c_429, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_426])).
% 2.61/1.36  tff(c_430, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_145, c_429])).
% 2.61/1.36  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.61/1.36  tff(c_10, plain, (![A_7, B_8]: (k1_enumset1(A_7, A_7, B_8)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.61/1.36  tff(c_12, plain, (![A_9, B_10, C_11]: (k2_enumset1(A_9, A_9, B_10, C_11)=k1_enumset1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.61/1.36  tff(c_14, plain, (![A_12, B_13, C_14, D_15]: (k3_enumset1(A_12, A_12, B_13, C_14, D_15)=k2_enumset1(A_12, B_13, C_14, D_15))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.61/1.36  tff(c_282, plain, (![E_151, G_147, D_148, B_149, A_146, C_150]: (G_147=E_151 | G_147=D_148 | G_147=C_150 | G_147=B_149 | G_147=A_146 | ~r2_hidden(G_147, k3_enumset1(A_146, B_149, C_150, D_148, E_151)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.61/1.36  tff(c_311, plain, (![G_156, C_155, B_152, A_153, D_154]: (G_156=D_154 | G_156=C_155 | G_156=B_152 | G_156=A_153 | G_156=A_153 | ~r2_hidden(G_156, k2_enumset1(A_153, B_152, C_155, D_154)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_282])).
% 2.61/1.36  tff(c_384, plain, (![G_161, C_162, B_163, A_164]: (G_161=C_162 | G_161=B_163 | G_161=A_164 | G_161=A_164 | G_161=A_164 | ~r2_hidden(G_161, k1_enumset1(A_164, B_163, C_162)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_311])).
% 2.61/1.36  tff(c_403, plain, (![G_165, B_166, A_167]: (G_165=B_166 | G_165=A_167 | G_165=A_167 | G_165=A_167 | G_165=A_167 | ~r2_hidden(G_165, k2_tarski(A_167, B_166)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_384])).
% 2.61/1.36  tff(c_412, plain, (![G_165, A_6]: (G_165=A_6 | G_165=A_6 | G_165=A_6 | G_165=A_6 | G_165=A_6 | ~r2_hidden(G_165, k1_tarski(A_6)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_403])).
% 2.61/1.36  tff(c_433, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_430, c_412])).
% 2.61/1.36  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_66, c_66, c_66, c_433])).
% 2.61/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.61/1.36  
% 2.61/1.36  Inference rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Ref     : 0
% 2.61/1.36  #Sup     : 84
% 2.61/1.36  #Fact    : 0
% 2.61/1.36  #Define  : 0
% 2.61/1.36  #Split   : 0
% 2.61/1.36  #Chain   : 0
% 2.61/1.36  #Close   : 0
% 2.61/1.36  
% 2.61/1.36  Ordering : KBO
% 2.61/1.36  
% 2.61/1.36  Simplification rules
% 2.61/1.36  ----------------------
% 2.61/1.36  #Subsume      : 0
% 2.61/1.36  #Demod        : 9
% 2.61/1.36  #Tautology    : 49
% 2.61/1.36  #SimpNegUnit  : 4
% 2.61/1.36  #BackRed      : 1
% 2.61/1.36  
% 2.61/1.36  #Partial instantiations: 0
% 2.61/1.36  #Strategies tried      : 1
% 2.61/1.36  
% 2.61/1.36  Timing (in seconds)
% 2.61/1.36  ----------------------
% 2.61/1.36  Preprocessing        : 0.34
% 2.61/1.36  Parsing              : 0.17
% 2.61/1.36  CNF conversion       : 0.02
% 2.61/1.36  Main loop            : 0.26
% 2.61/1.36  Inferencing          : 0.09
% 2.61/1.36  Reduction            : 0.08
% 2.61/1.36  Demodulation         : 0.06
% 2.61/1.36  BG Simplification    : 0.02
% 2.61/1.36  Subsumption          : 0.06
% 2.61/1.36  Abstraction          : 0.02
% 2.61/1.36  MUC search           : 0.00
% 2.61/1.36  Cooper               : 0.00
% 2.61/1.36  Total                : 0.63
% 2.61/1.36  Index Insertion      : 0.00
% 2.61/1.36  Index Deletion       : 0.00
% 2.61/1.36  Index Matching       : 0.00
% 2.61/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
