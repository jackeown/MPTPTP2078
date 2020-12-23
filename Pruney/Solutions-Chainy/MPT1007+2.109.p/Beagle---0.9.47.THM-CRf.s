%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:25 EST 2020

% Result     : Theorem 3.25s
% Output     : CNFRefutation 3.25s
% Verified   : 
% Statistics : Number of formulae       :   59 (  63 expanded)
%              Number of leaves         :   34 (  38 expanded)
%              Depth                    :   12
%              Number of atoms          :   66 (  86 expanded)
%              Number of equality atoms :   30 (  34 expanded)
%              Maximal formula depth    :   22 (   5 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_93,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_33,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_39,axiom,(
    ! [A,B,C,D,E,F,G] : k6_enumset1(A,A,B,C,D,E,F,G) = k5_enumset1(A,B,C,D,E,F,G) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_enumset1)).

tff(f_69,axiom,(
    ! [A,B,C,D,E,F,G,H,I] :
      ( I = k6_enumset1(A,B,C,D,E,F,G,H)
    <=> ! [J] :
          ( r2_hidden(J,I)
        <=> ~ ( J != A
              & J != B
              & J != C
              & J != D
              & J != E
              & J != F
              & J != G
              & J != H ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d6_enumset1)).

tff(f_81,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_hidden(C,A)
       => ( B = k1_xboole_0
          | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(c_74,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_72,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_80,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_78,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_76,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_4,B_5,C_6] : k2_enumset1(A_4,A_4,B_5,C_6) = k1_enumset1(A_4,B_5,C_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] : k3_enumset1(A_7,A_7,B_8,C_9,D_10) = k2_enumset1(A_7,B_8,C_9,D_10) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] : k4_enumset1(A_11,A_11,B_12,C_13,D_14,E_15) = k3_enumset1(A_11,B_12,C_13,D_14,E_15) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] : k5_enumset1(A_16,A_16,B_17,C_18,D_19,E_20,F_21) = k4_enumset1(A_16,B_17,C_18,D_19,E_20,F_21) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_143,plain,(
    ! [E_132,A_130,B_136,G_134,D_135,F_133,C_131] : k6_enumset1(A_130,A_130,B_136,C_131,D_135,E_132,F_133,G_134) = k5_enumset1(A_130,B_136,C_131,D_135,E_132,F_133,G_134) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [G_35,H_36,J_40,A_29,F_34,D_32,C_31,B_30] : r2_hidden(J_40,k6_enumset1(A_29,B_30,C_31,D_32,J_40,F_34,G_35,H_36)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_176,plain,(
    ! [B_140,F_138,D_142,G_143,C_141,A_137,E_139] : r2_hidden(D_142,k5_enumset1(A_137,B_140,C_141,D_142,E_139,F_138,G_143)) ),
    inference(superposition,[status(thm),theory(equality)],[c_143,c_24])).

tff(c_180,plain,(
    ! [D_148,E_146,F_144,C_149,B_145,A_147] : r2_hidden(C_149,k4_enumset1(A_147,B_145,C_149,D_148,E_146,F_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_184,plain,(
    ! [B_152,D_153,C_150,E_154,A_151] : r2_hidden(B_152,k3_enumset1(A_151,B_152,C_150,D_153,E_154)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_180])).

tff(c_188,plain,(
    ! [A_155,B_156,C_157,D_158] : r2_hidden(A_155,k2_enumset1(A_155,B_156,C_157,D_158)) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_184])).

tff(c_192,plain,(
    ! [A_159,B_160,C_161] : r2_hidden(A_159,k1_enumset1(A_159,B_160,C_161)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_188])).

tff(c_236,plain,(
    ! [A_166,B_167] : r2_hidden(A_166,k2_tarski(A_166,B_167)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_192])).

tff(c_243,plain,(
    ! [A_168] : r2_hidden(A_168,k1_tarski(A_168)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_236])).

tff(c_70,plain,(
    ! [D_44,C_43,B_42,A_41] :
      ( r2_hidden(k1_funct_1(D_44,C_43),B_42)
      | k1_xboole_0 = B_42
      | ~ r2_hidden(C_43,A_41)
      | ~ m1_subset_1(D_44,k1_zfmisc_1(k2_zfmisc_1(A_41,B_42)))
      | ~ v1_funct_2(D_44,A_41,B_42)
      | ~ v1_funct_1(D_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_450,plain,(
    ! [D_335,A_336,B_337] :
      ( r2_hidden(k1_funct_1(D_335,A_336),B_337)
      | k1_xboole_0 = B_337
      | ~ m1_subset_1(D_335,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_336),B_337)))
      | ~ v1_funct_2(D_335,k1_tarski(A_336),B_337)
      | ~ v1_funct_1(D_335) ) ),
    inference(resolution,[status(thm)],[c_243,c_70])).

tff(c_453,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4'
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4')
    | ~ v1_funct_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_76,c_450])).

tff(c_456,plain,
    ( r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_78,c_453])).

tff(c_458,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_72,c_456])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:16:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.25/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.48  
% 3.25/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.48  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.25/1.48  
% 3.25/1.48  %Foreground sorts:
% 3.25/1.48  
% 3.25/1.48  
% 3.25/1.48  %Background operators:
% 3.25/1.48  
% 3.25/1.48  
% 3.25/1.48  %Foreground operators:
% 3.25/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.25/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.25/1.48  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.25/1.48  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.25/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.25/1.48  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.25/1.48  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.25/1.48  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.25/1.48  tff('#skF_5', type, '#skF_5': $i).
% 3.25/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.25/1.48  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.48  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.25/1.48  tff('#skF_3', type, '#skF_3': $i).
% 3.25/1.48  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.25/1.48  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 3.25/1.48  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.25/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.25/1.48  tff('#skF_4', type, '#skF_4': $i).
% 3.25/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.25/1.48  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.48  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.25/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.25/1.48  
% 3.25/1.50  tff(f_93, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_2)).
% 3.25/1.50  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.25/1.50  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.25/1.50  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.25/1.50  tff(f_33, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_enumset1)).
% 3.25/1.50  tff(f_35, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_enumset1)).
% 3.25/1.50  tff(f_37, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t74_enumset1)).
% 3.25/1.50  tff(f_39, axiom, (![A, B, C, D, E, F, G]: (k6_enumset1(A, A, B, C, D, E, F, G) = k5_enumset1(A, B, C, D, E, F, G))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_enumset1)).
% 3.25/1.50  tff(f_69, axiom, (![A, B, C, D, E, F, G, H, I]: ((I = k6_enumset1(A, B, C, D, E, F, G, H)) <=> (![J]: (r2_hidden(J, I) <=> ~(((((((~(J = A) & ~(J = B)) & ~(J = C)) & ~(J = D)) & ~(J = E)) & ~(J = F)) & ~(J = G)) & ~(J = H)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d6_enumset1)).
% 3.25/1.50  tff(f_81, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 3.25/1.50  tff(c_74, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.50  tff(c_72, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.50  tff(c_80, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.50  tff(c_78, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.50  tff(c_76, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.25/1.50  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.25/1.50  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.25/1.50  tff(c_6, plain, (![A_4, B_5, C_6]: (k2_enumset1(A_4, A_4, B_5, C_6)=k1_enumset1(A_4, B_5, C_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.25/1.50  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (k3_enumset1(A_7, A_7, B_8, C_9, D_10)=k2_enumset1(A_7, B_8, C_9, D_10))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.25/1.50  tff(c_10, plain, (![D_14, E_15, B_12, A_11, C_13]: (k4_enumset1(A_11, A_11, B_12, C_13, D_14, E_15)=k3_enumset1(A_11, B_12, C_13, D_14, E_15))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.25/1.50  tff(c_12, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (k5_enumset1(A_16, A_16, B_17, C_18, D_19, E_20, F_21)=k4_enumset1(A_16, B_17, C_18, D_19, E_20, F_21))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.25/1.50  tff(c_143, plain, (![E_132, A_130, B_136, G_134, D_135, F_133, C_131]: (k6_enumset1(A_130, A_130, B_136, C_131, D_135, E_132, F_133, G_134)=k5_enumset1(A_130, B_136, C_131, D_135, E_132, F_133, G_134))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.25/1.50  tff(c_24, plain, (![G_35, H_36, J_40, A_29, F_34, D_32, C_31, B_30]: (r2_hidden(J_40, k6_enumset1(A_29, B_30, C_31, D_32, J_40, F_34, G_35, H_36)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.25/1.50  tff(c_176, plain, (![B_140, F_138, D_142, G_143, C_141, A_137, E_139]: (r2_hidden(D_142, k5_enumset1(A_137, B_140, C_141, D_142, E_139, F_138, G_143)))), inference(superposition, [status(thm), theory('equality')], [c_143, c_24])).
% 3.25/1.50  tff(c_180, plain, (![D_148, E_146, F_144, C_149, B_145, A_147]: (r2_hidden(C_149, k4_enumset1(A_147, B_145, C_149, D_148, E_146, F_144)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_176])).
% 3.25/1.50  tff(c_184, plain, (![B_152, D_153, C_150, E_154, A_151]: (r2_hidden(B_152, k3_enumset1(A_151, B_152, C_150, D_153, E_154)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_180])).
% 3.25/1.50  tff(c_188, plain, (![A_155, B_156, C_157, D_158]: (r2_hidden(A_155, k2_enumset1(A_155, B_156, C_157, D_158)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_184])).
% 3.25/1.50  tff(c_192, plain, (![A_159, B_160, C_161]: (r2_hidden(A_159, k1_enumset1(A_159, B_160, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_188])).
% 3.25/1.50  tff(c_236, plain, (![A_166, B_167]: (r2_hidden(A_166, k2_tarski(A_166, B_167)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_192])).
% 3.25/1.50  tff(c_243, plain, (![A_168]: (r2_hidden(A_168, k1_tarski(A_168)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_236])).
% 3.25/1.50  tff(c_70, plain, (![D_44, C_43, B_42, A_41]: (r2_hidden(k1_funct_1(D_44, C_43), B_42) | k1_xboole_0=B_42 | ~r2_hidden(C_43, A_41) | ~m1_subset_1(D_44, k1_zfmisc_1(k2_zfmisc_1(A_41, B_42))) | ~v1_funct_2(D_44, A_41, B_42) | ~v1_funct_1(D_44))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.25/1.50  tff(c_450, plain, (![D_335, A_336, B_337]: (r2_hidden(k1_funct_1(D_335, A_336), B_337) | k1_xboole_0=B_337 | ~m1_subset_1(D_335, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A_336), B_337))) | ~v1_funct_2(D_335, k1_tarski(A_336), B_337) | ~v1_funct_1(D_335))), inference(resolution, [status(thm)], [c_243, c_70])).
% 3.25/1.50  tff(c_453, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4' | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4') | ~v1_funct_1('#skF_5')), inference(resolution, [status(thm)], [c_76, c_450])).
% 3.25/1.50  tff(c_456, plain, (r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80, c_78, c_453])).
% 3.25/1.50  tff(c_458, plain, $false, inference(negUnitSimplification, [status(thm)], [c_74, c_72, c_456])).
% 3.25/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.25/1.50  
% 3.25/1.50  Inference rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Ref     : 0
% 3.25/1.50  #Sup     : 95
% 3.25/1.50  #Fact    : 0
% 3.25/1.50  #Define  : 0
% 3.25/1.50  #Split   : 0
% 3.25/1.50  #Chain   : 0
% 3.25/1.50  #Close   : 0
% 3.25/1.50  
% 3.25/1.50  Ordering : KBO
% 3.25/1.50  
% 3.25/1.50  Simplification rules
% 3.25/1.50  ----------------------
% 3.25/1.50  #Subsume      : 0
% 3.25/1.50  #Demod        : 9
% 3.25/1.50  #Tautology    : 29
% 3.25/1.50  #SimpNegUnit  : 1
% 3.25/1.50  #BackRed      : 0
% 3.25/1.50  
% 3.25/1.50  #Partial instantiations: 0
% 3.25/1.50  #Strategies tried      : 1
% 3.25/1.50  
% 3.25/1.50  Timing (in seconds)
% 3.25/1.50  ----------------------
% 3.25/1.50  Preprocessing        : 0.36
% 3.25/1.50  Parsing              : 0.17
% 3.25/1.50  CNF conversion       : 0.03
% 3.25/1.50  Main loop            : 0.33
% 3.25/1.50  Inferencing          : 0.10
% 3.25/1.50  Reduction            : 0.09
% 3.25/1.50  Demodulation         : 0.07
% 3.25/1.50  BG Simplification    : 0.02
% 3.25/1.50  Subsumption          : 0.09
% 3.25/1.50  Abstraction          : 0.02
% 3.25/1.50  MUC search           : 0.00
% 3.25/1.50  Cooper               : 0.00
% 3.25/1.50  Total                : 0.72
% 3.25/1.50  Index Insertion      : 0.00
% 3.25/1.50  Index Deletion       : 0.00
% 3.25/1.50  Index Matching       : 0.00
% 3.25/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
