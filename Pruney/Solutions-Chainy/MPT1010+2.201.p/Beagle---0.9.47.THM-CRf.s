%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:15:32 EST 2020

% Result     : Theorem 2.65s
% Output     : CNFRefutation 2.85s
% Verified   : 
% Statistics : Number of formulae       :   72 (  86 expanded)
%              Number of leaves         :   41 (  50 expanded)
%              Depth                    :    9
%              Number of atoms          :   97 ( 143 expanded)
%              Number of equality atoms :   63 (  77 expanded)
%              Maximal formula depth    :   16 (   4 average)
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

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_71,axiom,(
    ! [A] : k1_setfam_1(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_setfam_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_73,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_48,axiom,(
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
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_37,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_69,axiom,(
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

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_60,plain,(
    ! [A_43] : k1_setfam_1(k1_tarski(A_43)) = A_43 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_110,plain,(
    ! [A_56,B_57] : k1_setfam_1(k2_tarski(A_56,B_57)) = k3_xboole_0(A_56,B_57) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_119,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = k1_setfam_1(k1_tarski(A_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_110])).

tff(c_122,plain,(
    ! [A_4] : k3_xboole_0(A_4,A_4) = A_4 ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_119])).

tff(c_133,plain,(
    ! [A_64,B_65] : k5_xboole_0(A_64,k3_xboole_0(A_64,B_65)) = k4_xboole_0(A_64,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_142,plain,(
    ! [A_4] : k5_xboole_0(A_4,A_4) = k4_xboole_0(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_133])).

tff(c_145,plain,(
    ! [A_4] : k4_xboole_0(A_4,A_4) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_142])).

tff(c_20,plain,(
    ! [B_33] : k4_xboole_0(k1_tarski(B_33),k1_tarski(B_33)) != k1_tarski(B_33) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_146,plain,(
    ! [B_33] : k1_tarski(B_33) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_20])).

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
    ! [D_156,C_157,B_158,A_159] :
      ( r2_hidden(k1_funct_1(D_156,C_157),B_158)
      | k1_xboole_0 = B_158
      | ~ r2_hidden(C_157,A_159)
      | ~ m1_subset_1(D_156,k1_zfmisc_1(k2_zfmisc_1(A_159,B_158)))
      | ~ v1_funct_2(D_156,A_159,B_158)
      | ~ v1_funct_1(D_156) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_423,plain,(
    ! [D_169,B_170] :
      ( r2_hidden(k1_funct_1(D_169,'#skF_5'),B_170)
      | k1_xboole_0 = B_170
      | ~ m1_subset_1(D_169,k1_zfmisc_1(k2_zfmisc_1('#skF_3',B_170)))
      | ~ v1_funct_2(D_169,'#skF_3',B_170)
      | ~ v1_funct_1(D_169) ) ),
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
    inference(negUnitSimplification,[status(thm)],[c_146,c_429])).

tff(c_8,plain,(
    ! [A_5,B_6] : k1_enumset1(A_5,A_5,B_6) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9] : k2_enumset1(A_7,A_7,B_8,C_9) = k1_enumset1(A_7,B_8,C_9) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12,D_13] : k3_enumset1(A_10,A_10,B_11,C_12,D_13) = k2_enumset1(A_10,B_11,C_12,D_13) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_282,plain,(
    ! [G_145,E_148,D_147,B_149,A_146,C_150] :
      ( G_145 = E_148
      | G_145 = D_147
      | G_145 = C_150
      | G_145 = B_149
      | G_145 = A_146
      | ~ r2_hidden(G_145,k3_enumset1(A_146,B_149,C_150,D_147,E_148)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_311,plain,(
    ! [C_155,A_153,B_151,G_152,D_154] :
      ( G_152 = D_154
      | G_152 = C_155
      | G_152 = B_151
      | G_152 = A_153
      | G_152 = A_153
      | ~ r2_hidden(G_152,k2_enumset1(A_153,B_151,C_155,D_154)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_282])).

tff(c_384,plain,(
    ! [G_160,C_161,B_162,A_163] :
      ( G_160 = C_161
      | G_160 = B_162
      | G_160 = A_163
      | G_160 = A_163
      | G_160 = A_163
      | ~ r2_hidden(G_160,k1_enumset1(A_163,B_162,C_161)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_311])).

tff(c_403,plain,(
    ! [G_164,B_165,A_166] :
      ( G_164 = B_165
      | G_164 = A_166
      | G_164 = A_166
      | G_164 = A_166
      | G_164 = A_166
      | ~ r2_hidden(G_164,k2_tarski(A_166,B_165)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_384])).

tff(c_412,plain,(
    ! [G_164,A_4] :
      ( G_164 = A_4
      | G_164 = A_4
      | G_164 = A_4
      | G_164 = A_4
      | G_164 = A_4
      | ~ r2_hidden(G_164,k1_tarski(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_403])).

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
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:50:46 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.65/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.37  
% 2.85/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.37  %$ v1_funct_2 > r2_hidden > m1_subset_1 > v1_funct_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_4
% 2.85/1.37  
% 2.85/1.37  %Foreground sorts:
% 2.85/1.37  
% 2.85/1.37  
% 2.85/1.37  %Background operators:
% 2.85/1.37  
% 2.85/1.37  
% 2.85/1.37  %Foreground operators:
% 2.85/1.37  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.85/1.37  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.85/1.37  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.37  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.37  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.85/1.37  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.85/1.37  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.85/1.37  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.85/1.37  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.85/1.37  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.85/1.37  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.85/1.37  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.85/1.37  tff('#skF_5', type, '#skF_5': $i).
% 2.85/1.37  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.85/1.37  tff('#skF_6', type, '#skF_6': $i).
% 2.85/1.37  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.85/1.37  tff('#skF_3', type, '#skF_3': $i).
% 2.85/1.37  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.37  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.85/1.37  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.85/1.37  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.37  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.85/1.37  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.85/1.37  tff('#skF_4', type, '#skF_4': $i).
% 2.85/1.37  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.85/1.37  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.85/1.37  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.85/1.37  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.85/1.37  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.85/1.37  
% 2.85/1.38  tff(f_96, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, k1_tarski(B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, k1_tarski(B))))) => (r2_hidden(C, A) => (k1_funct_1(D, C) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_funct_2)).
% 2.85/1.38  tff(f_29, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.85/1.38  tff(f_71, axiom, (![A]: (k1_setfam_1(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_setfam_1)).
% 2.85/1.38  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.85/1.38  tff(f_73, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.85/1.38  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.85/1.38  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.85/1.38  tff(f_85, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_funct_2)).
% 2.85/1.38  tff(f_33, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.85/1.38  tff(f_35, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.85/1.38  tff(f_37, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.85/1.38  tff(f_69, axiom, (![A, B, C, D, E, F]: ((F = k3_enumset1(A, B, C, D, E)) <=> (![G]: (r2_hidden(G, F) <=> ~((((~(G = A) & ~(G = B)) & ~(G = C)) & ~(G = D)) & ~(G = E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_enumset1)).
% 2.85/1.38  tff(c_66, plain, (k1_funct_1('#skF_6', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.85/1.38  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.85/1.38  tff(c_60, plain, (![A_43]: (k1_setfam_1(k1_tarski(A_43))=A_43)), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.85/1.38  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.85/1.38  tff(c_110, plain, (![A_56, B_57]: (k1_setfam_1(k2_tarski(A_56, B_57))=k3_xboole_0(A_56, B_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.85/1.38  tff(c_119, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=k1_setfam_1(k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_110])).
% 2.85/1.38  tff(c_122, plain, (![A_4]: (k3_xboole_0(A_4, A_4)=A_4)), inference(demodulation, [status(thm), theory('equality')], [c_60, c_119])).
% 2.85/1.38  tff(c_133, plain, (![A_64, B_65]: (k5_xboole_0(A_64, k3_xboole_0(A_64, B_65))=k4_xboole_0(A_64, B_65))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.85/1.38  tff(c_142, plain, (![A_4]: (k5_xboole_0(A_4, A_4)=k4_xboole_0(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_122, c_133])).
% 2.85/1.38  tff(c_145, plain, (![A_4]: (k4_xboole_0(A_4, A_4)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_142])).
% 2.85/1.38  tff(c_20, plain, (![B_33]: (k4_xboole_0(k1_tarski(B_33), k1_tarski(B_33))!=k1_tarski(B_33))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.85/1.38  tff(c_146, plain, (![B_33]: (k1_tarski(B_33)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_145, c_20])).
% 2.85/1.38  tff(c_74, plain, (v1_funct_1('#skF_6')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.85/1.38  tff(c_72, plain, (v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.85/1.38  tff(c_70, plain, (m1_subset_1('#skF_6', k1_zfmisc_1(k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))))), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.85/1.38  tff(c_68, plain, (r2_hidden('#skF_5', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.85/1.38  tff(c_335, plain, (![D_156, C_157, B_158, A_159]: (r2_hidden(k1_funct_1(D_156, C_157), B_158) | k1_xboole_0=B_158 | ~r2_hidden(C_157, A_159) | ~m1_subset_1(D_156, k1_zfmisc_1(k2_zfmisc_1(A_159, B_158))) | ~v1_funct_2(D_156, A_159, B_158) | ~v1_funct_1(D_156))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.85/1.38  tff(c_423, plain, (![D_169, B_170]: (r2_hidden(k1_funct_1(D_169, '#skF_5'), B_170) | k1_xboole_0=B_170 | ~m1_subset_1(D_169, k1_zfmisc_1(k2_zfmisc_1('#skF_3', B_170))) | ~v1_funct_2(D_169, '#skF_3', B_170) | ~v1_funct_1(D_169))), inference(resolution, [status(thm)], [c_68, c_335])).
% 2.85/1.38  tff(c_426, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0 | ~v1_funct_2('#skF_6', '#skF_3', k1_tarski('#skF_4')) | ~v1_funct_1('#skF_6')), inference(resolution, [status(thm)], [c_70, c_423])).
% 2.85/1.38  tff(c_429, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4')) | k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_74, c_72, c_426])).
% 2.85/1.38  tff(c_430, plain, (r2_hidden(k1_funct_1('#skF_6', '#skF_5'), k1_tarski('#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_146, c_429])).
% 2.85/1.38  tff(c_8, plain, (![A_5, B_6]: (k1_enumset1(A_5, A_5, B_6)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.85/1.38  tff(c_10, plain, (![A_7, B_8, C_9]: (k2_enumset1(A_7, A_7, B_8, C_9)=k1_enumset1(A_7, B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.85/1.38  tff(c_12, plain, (![A_10, B_11, C_12, D_13]: (k3_enumset1(A_10, A_10, B_11, C_12, D_13)=k2_enumset1(A_10, B_11, C_12, D_13))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.85/1.38  tff(c_282, plain, (![G_145, E_148, D_147, B_149, A_146, C_150]: (G_145=E_148 | G_145=D_147 | G_145=C_150 | G_145=B_149 | G_145=A_146 | ~r2_hidden(G_145, k3_enumset1(A_146, B_149, C_150, D_147, E_148)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.85/1.38  tff(c_311, plain, (![C_155, A_153, B_151, G_152, D_154]: (G_152=D_154 | G_152=C_155 | G_152=B_151 | G_152=A_153 | G_152=A_153 | ~r2_hidden(G_152, k2_enumset1(A_153, B_151, C_155, D_154)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_282])).
% 2.85/1.38  tff(c_384, plain, (![G_160, C_161, B_162, A_163]: (G_160=C_161 | G_160=B_162 | G_160=A_163 | G_160=A_163 | G_160=A_163 | ~r2_hidden(G_160, k1_enumset1(A_163, B_162, C_161)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_311])).
% 2.85/1.38  tff(c_403, plain, (![G_164, B_165, A_166]: (G_164=B_165 | G_164=A_166 | G_164=A_166 | G_164=A_166 | G_164=A_166 | ~r2_hidden(G_164, k2_tarski(A_166, B_165)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_384])).
% 2.85/1.38  tff(c_412, plain, (![G_164, A_4]: (G_164=A_4 | G_164=A_4 | G_164=A_4 | G_164=A_4 | G_164=A_4 | ~r2_hidden(G_164, k1_tarski(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_403])).
% 2.85/1.38  tff(c_433, plain, (k1_funct_1('#skF_6', '#skF_5')='#skF_4'), inference(resolution, [status(thm)], [c_430, c_412])).
% 2.85/1.38  tff(c_439, plain, $false, inference(negUnitSimplification, [status(thm)], [c_66, c_66, c_66, c_66, c_66, c_433])).
% 2.85/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.85/1.38  
% 2.85/1.38  Inference rules
% 2.85/1.38  ----------------------
% 2.85/1.38  #Ref     : 0
% 2.85/1.38  #Sup     : 84
% 2.85/1.38  #Fact    : 0
% 2.85/1.38  #Define  : 0
% 2.85/1.38  #Split   : 0
% 2.85/1.38  #Chain   : 0
% 2.85/1.38  #Close   : 0
% 2.85/1.38  
% 2.85/1.38  Ordering : KBO
% 2.85/1.38  
% 2.85/1.38  Simplification rules
% 2.85/1.38  ----------------------
% 2.85/1.38  #Subsume      : 0
% 2.85/1.38  #Demod        : 9
% 2.85/1.38  #Tautology    : 49
% 2.85/1.38  #SimpNegUnit  : 4
% 2.85/1.38  #BackRed      : 1
% 2.85/1.38  
% 2.85/1.38  #Partial instantiations: 0
% 2.85/1.38  #Strategies tried      : 1
% 2.85/1.38  
% 2.85/1.38  Timing (in seconds)
% 2.85/1.38  ----------------------
% 2.85/1.39  Preprocessing        : 0.35
% 2.85/1.39  Parsing              : 0.18
% 2.85/1.39  CNF conversion       : 0.03
% 2.85/1.39  Main loop            : 0.26
% 2.85/1.39  Inferencing          : 0.09
% 2.85/1.39  Reduction            : 0.08
% 2.85/1.39  Demodulation         : 0.06
% 2.85/1.39  BG Simplification    : 0.02
% 2.85/1.39  Subsumption          : 0.06
% 2.85/1.39  Abstraction          : 0.02
% 2.85/1.39  MUC search           : 0.00
% 2.85/1.39  Cooper               : 0.00
% 2.85/1.39  Total                : 0.65
% 2.85/1.39  Index Insertion      : 0.00
% 2.85/1.39  Index Deletion       : 0.00
% 2.85/1.39  Index Matching       : 0.00
% 2.85/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------
