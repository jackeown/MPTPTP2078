%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0927+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:05 EST 2020

% Result     : Theorem 7.12s
% Output     : CNFRefutation 7.92s
% Verified   : 
% Statistics : Number of formulae       :  451 (8051 expanded)
%              Number of leaves         :   39 (2422 expanded)
%              Depth                    :   20
%              Number of atoms          : 1030 (54190 expanded)
%              Number of equality atoms :  655 (34649 expanded)
%              Maximal formula depth    :   27 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_9 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k11_mcart_1,type,(
    k11_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_153,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k1_zfmisc_1(A))
       => ! [F] :
            ( m1_subset_1(F,k1_zfmisc_1(B))
           => ! [G] :
                ( m1_subset_1(G,k1_zfmisc_1(C))
               => ! [H] :
                    ( m1_subset_1(H,k1_zfmisc_1(D))
                   => ! [I] :
                        ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
                       => ( r2_hidden(I,k4_zfmisc_1(E,F,G,H))
                         => ( r2_hidden(k8_mcart_1(A,B,C,D,I),E)
                            & r2_hidden(k9_mcart_1(A,B,C,D,I),F)
                            & r2_hidden(k10_mcart_1(A,B,C,D,I),G)
                            & r2_hidden(k11_mcart_1(A,B,C,D,I),H) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_mcart_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

tff(f_128,axiom,(
    ! [A,B,C,D,E,F,G,H] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & E != k1_xboole_0
        & F != k1_xboole_0
        & G != k1_xboole_0
        & H != k1_xboole_0
        & ? [I] :
            ( m1_subset_1(I,k4_zfmisc_1(A,B,C,D))
            & ? [J] :
                ( m1_subset_1(J,k4_zfmisc_1(E,F,G,H))
                & I = J
                & ~ ( k8_mcart_1(A,B,C,D,I) = k8_mcart_1(E,F,G,H,J)
                    & k9_mcart_1(A,B,C,D,I) = k9_mcart_1(E,F,G,H,J)
                    & k10_mcart_1(A,B,C,D,I) = k10_mcart_1(E,F,G,H,J)
                    & k11_mcart_1(A,B,C,D,I) = k11_mcart_1(E,F,G,H,J) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_mcart_1)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_42,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_boole)).

tff(f_37,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k8_mcart_1(A,B,C,D,E),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_mcart_1)).

tff(f_81,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_boole)).

tff(f_33,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k11_mcart_1(A,B,C,D,E),D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k11_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k9_mcart_1(A,B,C,D,E),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_mcart_1)).

tff(f_29,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => m1_subset_1(k10_mcart_1(A,B,C,D,E),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k10_mcart_1)).

tff(c_14,plain,(
    ! [A_21] : m1_subset_1('#skF_1'(A_21),A_21) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_18,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_46,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_74,plain,(
    ! [A_81,B_82] :
      ( m1_subset_1(A_81,B_82)
      | ~ r2_hidden(A_81,B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_46,c_74])).

tff(c_50,plain,(
    m1_subset_1('#skF_9',k1_zfmisc_1('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_169,plain,(
    ! [C_97,B_98,A_99] :
      ( ~ v1_xboole_0(C_97)
      | ~ m1_subset_1(B_98,k1_zfmisc_1(C_97))
      | ~ r2_hidden(A_99,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_181,plain,(
    ! [A_99] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_99,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_169])).

tff(c_186,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_181])).

tff(c_52,plain,(
    m1_subset_1('#skF_8',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_185,plain,(
    ! [A_99] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_99,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_169])).

tff(c_210,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_185])).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_182,plain,(
    ! [A_99] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_99,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_169])).

tff(c_209,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_182])).

tff(c_48,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_412,plain,(
    ! [J_180,A_181,D_184,H_187,E_185,G_188,F_183,B_182,C_186] :
      ( k8_mcart_1(E_185,F_183,G_188,H_187,J_180) = k8_mcart_1(A_181,B_182,C_186,D_184,J_180)
      | ~ m1_subset_1(J_180,k4_zfmisc_1(E_185,F_183,G_188,H_187))
      | ~ m1_subset_1(J_180,k4_zfmisc_1(A_181,B_182,C_186,D_184))
      | k1_xboole_0 = H_187
      | k1_xboole_0 = G_188
      | k1_xboole_0 = F_183
      | k1_xboole_0 = E_185
      | k1_xboole_0 = D_184
      | k1_xboole_0 = C_186
      | k1_xboole_0 = B_182
      | k1_xboole_0 = A_181 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_445,plain,(
    ! [A_181,B_182,C_186,D_184] :
      ( k8_mcart_1(A_181,B_182,C_186,D_184,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_181,B_182,C_186,D_184))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_184
      | k1_xboole_0 = C_186
      | k1_xboole_0 = B_182
      | k1_xboole_0 = A_181 ) ),
    inference(resolution,[status(thm)],[c_48,c_412])).

tff(c_511,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_445])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_12,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_57,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_526,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_57])).

tff(c_529,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_209,c_526])).

tff(c_531,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_54,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_184,plain,(
    ! [A_99] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_99,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_169])).

tff(c_187,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_184])).

tff(c_301,plain,(
    ! [E_149,A_145,D_148,J_144,B_146,C_150,G_152,H_151,F_147] :
      ( k10_mcart_1(E_149,F_147,G_152,H_151,J_144) = k10_mcart_1(A_145,B_146,C_150,D_148,J_144)
      | ~ m1_subset_1(J_144,k4_zfmisc_1(E_149,F_147,G_152,H_151))
      | ~ m1_subset_1(J_144,k4_zfmisc_1(A_145,B_146,C_150,D_148))
      | k1_xboole_0 = H_151
      | k1_xboole_0 = G_152
      | k1_xboole_0 = F_147
      | k1_xboole_0 = E_149
      | k1_xboole_0 = D_148
      | k1_xboole_0 = C_150
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_334,plain,(
    ! [A_145,B_146,C_150,D_148] :
      ( k10_mcart_1(A_145,B_146,C_150,D_148,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_145,B_146,C_150,D_148))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_148
      | k1_xboole_0 = C_150
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(resolution,[status(thm)],[c_48,c_301])).

tff(c_708,plain,(
    ! [A_145,B_146,C_150,D_148] :
      ( k10_mcart_1(A_145,B_146,C_150,D_148,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_145,B_146,C_150,D_148))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = D_148
      | k1_xboole_0 = C_150
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(negUnitSimplification,[status(thm)],[c_531,c_334])).

tff(c_709,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_708])).

tff(c_729,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_709,c_57])).

tff(c_732,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_187,c_729])).

tff(c_734,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_708])).

tff(c_735,plain,(
    ! [F_231,A_229,G_236,C_234,E_233,D_232,J_228,H_235,B_230] :
      ( k11_mcart_1(E_233,F_231,G_236,H_235,J_228) = k11_mcart_1(A_229,B_230,C_234,D_232,J_228)
      | ~ m1_subset_1(J_228,k4_zfmisc_1(E_233,F_231,G_236,H_235))
      | ~ m1_subset_1(J_228,k4_zfmisc_1(A_229,B_230,C_234,D_232))
      | k1_xboole_0 = H_235
      | k1_xboole_0 = G_236
      | k1_xboole_0 = F_231
      | k1_xboole_0 = E_233
      | k1_xboole_0 = D_232
      | k1_xboole_0 = C_234
      | k1_xboole_0 = B_230
      | k1_xboole_0 = A_229 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_751,plain,(
    ! [A_229,B_230,C_234,D_232] :
      ( k11_mcart_1(A_229,B_230,C_234,D_232,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_229,B_230,C_234,D_232))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_232
      | k1_xboole_0 = C_234
      | k1_xboole_0 = B_230
      | k1_xboole_0 = A_229 ) ),
    inference(resolution,[status(thm)],[c_48,c_735])).

tff(c_770,plain,(
    ! [A_229,B_230,C_234,D_232] :
      ( k11_mcart_1(A_229,B_230,C_234,D_232,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_229,B_230,C_234,D_232))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = D_232
      | k1_xboole_0 = C_234
      | k1_xboole_0 = B_230
      | k1_xboole_0 = A_229 ) ),
    inference(negUnitSimplification,[status(thm)],[c_531,c_734,c_751])).

tff(c_776,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_770])).

tff(c_798,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_776,c_57])).

tff(c_801,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_210,c_798])).

tff(c_802,plain,(
    ! [A_229,B_230,C_234,D_232] :
      ( k1_xboole_0 = '#skF_5'
      | k11_mcart_1(A_229,B_230,C_234,D_232,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_229,B_230,C_234,D_232))
      | k1_xboole_0 = D_232
      | k1_xboole_0 = C_234
      | k1_xboole_0 = B_230
      | k1_xboole_0 = A_229 ) ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_804,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_802])).

tff(c_827,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_804,c_57])).

tff(c_830,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_186,c_827])).

tff(c_832,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_803,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_770])).

tff(c_530,plain,(
    ! [A_181,B_182,C_186,D_184] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5'
      | k8_mcart_1(A_181,B_182,C_186,D_184,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_181,B_182,C_186,D_184))
      | k1_xboole_0 = D_184
      | k1_xboole_0 = C_186
      | k1_xboole_0 = B_182
      | k1_xboole_0 = A_181 ) ),
    inference(splitRight,[status(thm)],[c_445])).

tff(c_834,plain,(
    ! [A_237,B_238,C_239,D_240] :
      ( k8_mcart_1(A_237,B_238,C_239,D_240,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_237,B_238,C_239,D_240))
      | k1_xboole_0 = D_240
      | k1_xboole_0 = C_239
      | k1_xboole_0 = B_238
      | k1_xboole_0 = A_237 ) ),
    inference(negUnitSimplification,[status(thm)],[c_832,c_803,c_734,c_530])).

tff(c_853,plain,
    ( k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_834])).

tff(c_862,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_853])).

tff(c_887,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_57])).

tff(c_28,plain,(
    ! [B_28,C_29,D_30] : k4_zfmisc_1(k1_xboole_0,B_28,C_29,D_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_885,plain,(
    ! [B_28,C_29,D_30] : k4_zfmisc_1('#skF_6',B_28,C_29,D_30) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_862,c_862,c_28])).

tff(c_34,plain,(
    ! [B_36,A_35] :
      ( ~ v1_xboole_0(B_36)
      | ~ r2_hidden(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_73,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(resolution,[status(thm)],[c_46,c_34])).

tff(c_985,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_885,c_73])).

tff(c_989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_887,c_985])).

tff(c_991,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_992,plain,(
    ! [A_257,B_258,C_259,D_260] :
      ( k11_mcart_1(A_257,B_258,C_259,D_260,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_257,B_258,C_259,D_260))
      | k1_xboole_0 = D_260
      | k1_xboole_0 = C_259
      | k1_xboole_0 = B_258
      | k1_xboole_0 = A_257 ) ),
    inference(splitRight,[status(thm)],[c_802])).

tff(c_1011,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_992])).

tff(c_1033,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_991,c_1011])).

tff(c_1034,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_1033])).

tff(c_1061,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_57])).

tff(c_26,plain,(
    ! [A_27,C_29,D_30] : k4_zfmisc_1(A_27,k1_xboole_0,C_29,D_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1056,plain,(
    ! [A_27,C_29,D_30] : k4_zfmisc_1(A_27,'#skF_7',C_29,D_30) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1034,c_1034,c_26])).

tff(c_1130,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1056,c_73])).

tff(c_1134,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1130])).

tff(c_1136,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1033])).

tff(c_44,plain,
    ( ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_153])).

tff(c_164,plain,(
    ~ r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_168,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_18,c_164])).

tff(c_217,plain,(
    ~ m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_168])).

tff(c_990,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_853])).

tff(c_1020,plain,(
    k8_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_990])).

tff(c_8,plain,(
    ! [D_14,E_15,B_12,A_11,C_13] :
      ( m1_subset_1(k8_mcart_1(A_11,B_12,C_13,D_14,E_15),A_11)
      | ~ m1_subset_1(E_15,k4_zfmisc_1(A_11,B_12,C_13,D_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1024,plain,
    ( m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1020,c_8])).

tff(c_1028,plain,(
    m1_subset_1(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_1024])).

tff(c_1030,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_217,c_1028])).

tff(c_1031,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_990])).

tff(c_1168,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_1136,c_1031])).

tff(c_1169,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_1168])).

tff(c_1198,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_57])).

tff(c_24,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,k1_xboole_0,D_30) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1194,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,'#skF_8',D_30) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1169,c_1169,c_24])).

tff(c_1251,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_73])).

tff(c_1255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1198,c_1251])).

tff(c_1256,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_1168])).

tff(c_1292,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_57])).

tff(c_22,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1289,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1256,c_1256,c_22])).

tff(c_1462,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1289,c_73])).

tff(c_1466,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1292,c_1462])).

tff(c_1467,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_168])).

tff(c_32,plain,(
    ! [A_34] :
      ( k1_xboole_0 = A_34
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1472,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1467,c_32])).

tff(c_1477,plain,(
    ! [B_28,C_29,D_30] : k4_zfmisc_1('#skF_6',B_28,C_29,D_30) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1472,c_1472,c_28])).

tff(c_1547,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1477,c_73])).

tff(c_1551,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1467,c_1547])).

tff(c_1571,plain,(
    ! [A_335] : ~ r2_hidden(A_335,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1576,plain,(
    ! [A_25] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_25,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18,c_1571])).

tff(c_1588,plain,(
    ! [A_337] : ~ m1_subset_1(A_337,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1576])).

tff(c_1593,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_1588])).

tff(c_1594,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_1576])).

tff(c_1553,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1557,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1553,c_32])).

tff(c_1563,plain,(
    ! [A_34] :
      ( A_34 = '#skF_4'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_32])).

tff(c_1598,plain,(
    '#skF_8' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1594,c_1563])).

tff(c_1552,plain,(
    ! [A_99] : ~ r2_hidden(A_99,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_185])).

tff(c_1605,plain,(
    ! [A_99] : ~ r2_hidden(A_99,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_1552])).

tff(c_1560,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,'#skF_4',D_30) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1557,c_1557,c_24])).

tff(c_1608,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_4','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1598,c_46])).

tff(c_1635,plain,(
    r2_hidden('#skF_10','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1560,c_1608])).

tff(c_1638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1605,c_1635])).

tff(c_1640,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_1644,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1640,c_32])).

tff(c_1649,plain,(
    ! [B_28,C_29,D_30] : k4_zfmisc_1('#skF_2',B_28,C_29,D_30) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1644,c_1644,c_28])).

tff(c_1662,plain,(
    ! [A_344] : ~ r2_hidden(A_344,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_182])).

tff(c_1667,plain,(
    ! [A_25] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_25,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_18,c_1662])).

tff(c_1682,plain,(
    ! [A_351] : ~ m1_subset_1(A_351,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1667])).

tff(c_1692,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_1682])).

tff(c_1693,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1667])).

tff(c_1650,plain,(
    ! [A_34] :
      ( A_34 = '#skF_2'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1644,c_32])).

tff(c_1697,plain,(
    '#skF_6' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1693,c_1650])).

tff(c_1701,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_2','#skF_7','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1697,c_73])).

tff(c_1804,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1640,c_1649,c_1701])).

tff(c_1806,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_1810,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1806,c_32])).

tff(c_1811,plain,(
    ! [A_27,C_29,D_30] : k4_zfmisc_1(A_27,'#skF_3',C_29,D_30) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_1810,c_26])).

tff(c_1829,plain,(
    ! [A_374] : ~ r2_hidden(A_374,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_184])).

tff(c_1834,plain,(
    ! [A_25] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_25,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18,c_1829])).

tff(c_1844,plain,(
    ! [A_376] : ~ m1_subset_1(A_376,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1834])).

tff(c_1849,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_1844])).

tff(c_1850,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1834])).

tff(c_1815,plain,(
    ! [A_34] :
      ( A_34 = '#skF_3'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1810,c_32])).

tff(c_1859,plain,(
    '#skF_7' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1850,c_1815])).

tff(c_1863,plain,(
    ~ v1_xboole_0(k4_zfmisc_1('#skF_6','#skF_3','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1859,c_73])).

tff(c_1986,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1806,c_1811,c_1863])).

tff(c_2010,plain,(
    ! [A_400] : ~ r2_hidden(A_400,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_2015,plain,(
    ! [A_25] :
      ( v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_25,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_2010])).

tff(c_2028,plain,(
    ! [A_406] : ~ m1_subset_1(A_406,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2015])).

tff(c_2033,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_2028])).

tff(c_2034,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2015])).

tff(c_1988,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_181])).

tff(c_1992,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1988,c_32])).

tff(c_1997,plain,(
    ! [A_34] :
      ( A_34 = '#skF_5'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_32])).

tff(c_2038,plain,(
    '#skF_5' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_2034,c_1997])).

tff(c_1995,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1992,c_1992,c_22])).

tff(c_2100,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2038,c_2038,c_1995])).

tff(c_2103,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2100,c_73])).

tff(c_2107,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2034,c_2103])).

tff(c_2108,plain,
    ( ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2176,plain,(
    ~ r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2108])).

tff(c_2216,plain,
    ( v1_xboole_0('#skF_9')
    | ~ m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(resolution,[status(thm)],[c_18,c_2176])).

tff(c_2217,plain,(
    ~ m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_2216])).

tff(c_2109,plain,(
    r2_hidden(k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_2117,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(resolution,[status(thm)],[c_2109,c_34])).

tff(c_2118,plain,(
    ! [C_419,B_420,A_421] :
      ( ~ v1_xboole_0(C_419)
      | ~ m1_subset_1(B_420,k1_zfmisc_1(C_419))
      | ~ r2_hidden(A_421,B_420) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2134,plain,(
    ! [A_421] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_421,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_52,c_2118])).

tff(c_2136,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_2134])).

tff(c_2131,plain,(
    ! [A_421] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_421,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_56,c_2118])).

tff(c_2137,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_2131])).

tff(c_2250,plain,(
    ! [G_474,B_468,D_470,C_472,E_471,F_469,J_466,H_473,A_467] :
      ( k8_mcart_1(E_471,F_469,G_474,H_473,J_466) = k8_mcart_1(A_467,B_468,C_472,D_470,J_466)
      | ~ m1_subset_1(J_466,k4_zfmisc_1(E_471,F_469,G_474,H_473))
      | ~ m1_subset_1(J_466,k4_zfmisc_1(A_467,B_468,C_472,D_470))
      | k1_xboole_0 = H_473
      | k1_xboole_0 = G_474
      | k1_xboole_0 = F_469
      | k1_xboole_0 = E_471
      | k1_xboole_0 = D_470
      | k1_xboole_0 = C_472
      | k1_xboole_0 = B_468
      | k1_xboole_0 = A_467 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2283,plain,(
    ! [A_467,B_468,C_472,D_470] :
      ( k8_mcart_1(A_467,B_468,C_472,D_470,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_467,B_468,C_472,D_470))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_470
      | k1_xboole_0 = C_472
      | k1_xboole_0 = B_468
      | k1_xboole_0 = A_467 ) ),
    inference(resolution,[status(thm)],[c_48,c_2250])).

tff(c_2331,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2283])).

tff(c_2342,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2331,c_57])).

tff(c_2345,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2137,c_2342])).

tff(c_2347,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2283])).

tff(c_2133,plain,(
    ! [A_421] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_421,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_54,c_2118])).

tff(c_2138,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_2133])).

tff(c_2130,plain,(
    ! [A_421] :
      ( ~ v1_xboole_0('#skF_5')
      | ~ r2_hidden(A_421,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_50,c_2118])).

tff(c_2135,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_2130])).

tff(c_2346,plain,(
    ! [A_467,B_468,C_472,D_470] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5'
      | k8_mcart_1(A_467,B_468,C_472,D_470,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_467,B_468,C_472,D_470))
      | k1_xboole_0 = D_470
      | k1_xboole_0 = C_472
      | k1_xboole_0 = B_468
      | k1_xboole_0 = A_467 ) ),
    inference(splitRight,[status(thm)],[c_2283])).

tff(c_2515,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2346])).

tff(c_2532,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2515,c_57])).

tff(c_2535,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2135,c_2532])).

tff(c_2537,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2346])).

tff(c_2637,plain,(
    ! [B_543,H_548,J_541,C_547,G_549,F_544,D_545,E_546,A_542] :
      ( k10_mcart_1(E_546,F_544,G_549,H_548,J_541) = k10_mcart_1(A_542,B_543,C_547,D_545,J_541)
      | ~ m1_subset_1(J_541,k4_zfmisc_1(E_546,F_544,G_549,H_548))
      | ~ m1_subset_1(J_541,k4_zfmisc_1(A_542,B_543,C_547,D_545))
      | k1_xboole_0 = H_548
      | k1_xboole_0 = G_549
      | k1_xboole_0 = F_544
      | k1_xboole_0 = E_546
      | k1_xboole_0 = D_545
      | k1_xboole_0 = C_547
      | k1_xboole_0 = B_543
      | k1_xboole_0 = A_542 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2653,plain,(
    ! [A_542,B_543,C_547,D_545] :
      ( k10_mcart_1(A_542,B_543,C_547,D_545,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_542,B_543,C_547,D_545))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_545
      | k1_xboole_0 = C_547
      | k1_xboole_0 = B_543
      | k1_xboole_0 = A_542 ) ),
    inference(resolution,[status(thm)],[c_48,c_2637])).

tff(c_2672,plain,(
    ! [A_542,B_543,C_547,D_545] :
      ( k10_mcart_1(A_542,B_543,C_547,D_545,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_542,B_543,C_547,D_545))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = D_545
      | k1_xboole_0 = C_547
      | k1_xboole_0 = B_543
      | k1_xboole_0 = A_542 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2347,c_2537,c_2653])).

tff(c_2678,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2672])).

tff(c_2699,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2678,c_57])).

tff(c_2702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2138,c_2699])).

tff(c_2704,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2672])).

tff(c_2705,plain,(
    ! [B_552,F_553,J_550,D_554,H_557,E_555,A_551,G_558,C_556] :
      ( k9_mcart_1(E_555,F_553,G_558,H_557,J_550) = k9_mcart_1(A_551,B_552,C_556,D_554,J_550)
      | ~ m1_subset_1(J_550,k4_zfmisc_1(E_555,F_553,G_558,H_557))
      | ~ m1_subset_1(J_550,k4_zfmisc_1(A_551,B_552,C_556,D_554))
      | k1_xboole_0 = H_557
      | k1_xboole_0 = G_558
      | k1_xboole_0 = F_553
      | k1_xboole_0 = E_555
      | k1_xboole_0 = D_554
      | k1_xboole_0 = C_556
      | k1_xboole_0 = B_552
      | k1_xboole_0 = A_551 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2721,plain,(
    ! [A_551,B_552,C_556,D_554] :
      ( k9_mcart_1(A_551,B_552,C_556,D_554,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_551,B_552,C_556,D_554))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_554
      | k1_xboole_0 = C_556
      | k1_xboole_0 = B_552
      | k1_xboole_0 = A_551 ) ),
    inference(resolution,[status(thm)],[c_48,c_2705])).

tff(c_2740,plain,(
    ! [A_551,B_552,C_556,D_554] :
      ( k9_mcart_1(A_551,B_552,C_556,D_554,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_551,B_552,C_556,D_554))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = D_554
      | k1_xboole_0 = C_556
      | k1_xboole_0 = B_552
      | k1_xboole_0 = A_551 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2347,c_2704,c_2537,c_2721])).

tff(c_2746,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2740])).

tff(c_2769,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2746,c_57])).

tff(c_2772,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2136,c_2769])).

tff(c_2775,plain,(
    ! [A_559,B_560,C_561,D_562] :
      ( k9_mcart_1(A_559,B_560,C_561,D_562,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_559,B_560,C_561,D_562))
      | k1_xboole_0 = D_562
      | k1_xboole_0 = C_561
      | k1_xboole_0 = B_560
      | k1_xboole_0 = A_559 ) ),
    inference(splitRight,[status(thm)],[c_2740])).

tff(c_2794,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_2775])).

tff(c_2803,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2794])).

tff(c_2828,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2803,c_57])).

tff(c_2831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2117,c_2828])).

tff(c_2833,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_2794])).

tff(c_2774,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2740])).

tff(c_2399,plain,(
    ! [A_507,J_506,B_508,H_513,D_510,E_511,F_509,G_514,C_512] :
      ( k11_mcart_1(E_511,F_509,G_514,H_513,J_506) = k11_mcart_1(A_507,B_508,C_512,D_510,J_506)
      | ~ m1_subset_1(J_506,k4_zfmisc_1(E_511,F_509,G_514,H_513))
      | ~ m1_subset_1(J_506,k4_zfmisc_1(A_507,B_508,C_512,D_510))
      | k1_xboole_0 = H_513
      | k1_xboole_0 = G_514
      | k1_xboole_0 = F_509
      | k1_xboole_0 = E_511
      | k1_xboole_0 = D_510
      | k1_xboole_0 = C_512
      | k1_xboole_0 = B_508
      | k1_xboole_0 = A_507 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_2415,plain,(
    ! [A_507,B_508,C_512,D_510] :
      ( k11_mcart_1(A_507,B_508,C_512,D_510,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_507,B_508,C_512,D_510))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_510
      | k1_xboole_0 = C_512
      | k1_xboole_0 = B_508
      | k1_xboole_0 = A_507 ) ),
    inference(resolution,[status(thm)],[c_48,c_2399])).

tff(c_2434,plain,(
    ! [A_507,B_508,C_512,D_510] :
      ( k11_mcart_1(A_507,B_508,C_512,D_510,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_507,B_508,C_512,D_510))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = D_510
      | k1_xboole_0 = C_512
      | k1_xboole_0 = B_508
      | k1_xboole_0 = A_507 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2347,c_2415])).

tff(c_2835,plain,(
    ! [A_563,B_564,C_565,D_566] :
      ( k11_mcart_1(A_563,B_564,C_565,D_566,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_563,B_564,C_565,D_566))
      | k1_xboole_0 = D_566
      | k1_xboole_0 = C_565
      | k1_xboole_0 = B_564
      | k1_xboole_0 = A_563 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2704,c_2774,c_2537,c_2434])).

tff(c_2838,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_2835])).

tff(c_2856,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_2833,c_2838])).

tff(c_2875,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_2856])).

tff(c_2902,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_57])).

tff(c_2897,plain,(
    ! [A_27,C_29,D_30] : k4_zfmisc_1(A_27,'#skF_7',C_29,D_30) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2875,c_2875,c_26])).

tff(c_3021,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2897,c_73])).

tff(c_3025,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2902,c_3021])).

tff(c_3026,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_2856])).

tff(c_3033,plain,(
    k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_3026])).

tff(c_6,plain,(
    ! [B_7,D_9,C_8,E_10,A_6] :
      ( m1_subset_1(k11_mcart_1(A_6,B_7,C_8,D_9,E_10),D_9)
      | ~ m1_subset_1(E_10,k4_zfmisc_1(A_6,B_7,C_8,D_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_3068,plain,
    ( m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3033,c_6])).

tff(c_3072,plain,(
    m1_subset_1(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_3068])).

tff(c_3074,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2217,c_3072])).

tff(c_3075,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_3026])).

tff(c_3077,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_3075])).

tff(c_3105,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_57])).

tff(c_3101,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,'#skF_8',D_30) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3077,c_3077,c_24])).

tff(c_3153,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3101,c_73])).

tff(c_3157,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3105,c_3153])).

tff(c_3158,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_3075])).

tff(c_3220,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3158,c_57])).

tff(c_3217,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3158,c_3158,c_22])).

tff(c_3268,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3217,c_73])).

tff(c_3272,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3220,c_3268])).

tff(c_3273,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_2216])).

tff(c_3283,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(resolution,[status(thm)],[c_3273,c_32])).

tff(c_3290,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3283,c_3283,c_22])).

tff(c_3372,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3290,c_73])).

tff(c_3376,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3273,c_3372])).

tff(c_3378,plain,(
    r2_hidden(k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_2108])).

tff(c_3409,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(resolution,[status(thm)],[c_3378,c_34])).

tff(c_3377,plain,
    ( ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2108])).

tff(c_3438,plain,(
    ~ r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3377])).

tff(c_3442,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_18,c_3438])).

tff(c_3443,plain,(
    ~ m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_3442])).

tff(c_3455,plain,(
    ! [C_651,F_648,J_645,D_649,G_653,E_650,B_647,A_646,H_652] :
      ( k9_mcart_1(E_650,F_648,G_653,H_652,J_645) = k9_mcart_1(A_646,B_647,C_651,D_649,J_645)
      | ~ m1_subset_1(J_645,k4_zfmisc_1(E_650,F_648,G_653,H_652))
      | ~ m1_subset_1(J_645,k4_zfmisc_1(A_646,B_647,C_651,D_649))
      | k1_xboole_0 = H_652
      | k1_xboole_0 = G_653
      | k1_xboole_0 = F_648
      | k1_xboole_0 = E_650
      | k1_xboole_0 = D_649
      | k1_xboole_0 = C_651
      | k1_xboole_0 = B_647
      | k1_xboole_0 = A_646 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3488,plain,(
    ! [A_646,B_647,C_651,D_649] :
      ( k9_mcart_1(A_646,B_647,C_651,D_649,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_646,B_647,C_651,D_649))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_649
      | k1_xboole_0 = C_651
      | k1_xboole_0 = B_647
      | k1_xboole_0 = A_646 ) ),
    inference(resolution,[status(thm)],[c_48,c_3455])).

tff(c_3512,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_3488])).

tff(c_3523,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3512,c_57])).

tff(c_3526,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2137,c_3523])).

tff(c_3528,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_3488])).

tff(c_3589,plain,(
    ! [D_691,F_690,H_694,B_689,J_687,G_695,A_688,C_693,E_692] :
      ( k8_mcart_1(E_692,F_690,G_695,H_694,J_687) = k8_mcart_1(A_688,B_689,C_693,D_691,J_687)
      | ~ m1_subset_1(J_687,k4_zfmisc_1(E_692,F_690,G_695,H_694))
      | ~ m1_subset_1(J_687,k4_zfmisc_1(A_688,B_689,C_693,D_691))
      | k1_xboole_0 = H_694
      | k1_xboole_0 = G_695
      | k1_xboole_0 = F_690
      | k1_xboole_0 = E_692
      | k1_xboole_0 = D_691
      | k1_xboole_0 = C_693
      | k1_xboole_0 = B_689
      | k1_xboole_0 = A_688 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3605,plain,(
    ! [A_688,B_689,C_693,D_691] :
      ( k8_mcart_1(A_688,B_689,C_693,D_691,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_688,B_689,C_693,D_691))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_691
      | k1_xboole_0 = C_693
      | k1_xboole_0 = B_689
      | k1_xboole_0 = A_688 ) ),
    inference(resolution,[status(thm)],[c_48,c_3589])).

tff(c_3624,plain,(
    ! [A_688,B_689,C_693,D_691] :
      ( k8_mcart_1(A_688,B_689,C_693,D_691,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_688,B_689,C_693,D_691))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = D_691
      | k1_xboole_0 = C_693
      | k1_xboole_0 = B_689
      | k1_xboole_0 = A_688 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3528,c_3605])).

tff(c_3690,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_3624])).

tff(c_3706,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3690,c_57])).

tff(c_3709,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2138,c_3706])).

tff(c_3711,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_3624])).

tff(c_3796,plain,(
    ! [B_724,F_725,C_728,H_729,A_723,G_730,D_726,J_722,E_727] :
      ( k10_mcart_1(E_727,F_725,G_730,H_729,J_722) = k10_mcart_1(A_723,B_724,C_728,D_726,J_722)
      | ~ m1_subset_1(J_722,k4_zfmisc_1(E_727,F_725,G_730,H_729))
      | ~ m1_subset_1(J_722,k4_zfmisc_1(A_723,B_724,C_728,D_726))
      | k1_xboole_0 = H_729
      | k1_xboole_0 = G_730
      | k1_xboole_0 = F_725
      | k1_xboole_0 = E_727
      | k1_xboole_0 = D_726
      | k1_xboole_0 = C_728
      | k1_xboole_0 = B_724
      | k1_xboole_0 = A_723 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3812,plain,(
    ! [A_723,B_724,C_728,D_726] :
      ( k10_mcart_1(A_723,B_724,C_728,D_726,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_723,B_724,C_728,D_726))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_726
      | k1_xboole_0 = C_728
      | k1_xboole_0 = B_724
      | k1_xboole_0 = A_723 ) ),
    inference(resolution,[status(thm)],[c_48,c_3796])).

tff(c_3831,plain,(
    ! [A_723,B_724,C_728,D_726] :
      ( k10_mcart_1(A_723,B_724,C_728,D_726,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_723,B_724,C_728,D_726))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = D_726
      | k1_xboole_0 = C_728
      | k1_xboole_0 = B_724
      | k1_xboole_0 = A_723 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3528,c_3711,c_3812])).

tff(c_3888,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_3831])).

tff(c_3909,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3888,c_57])).

tff(c_3912,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2136,c_3909])).

tff(c_3914,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_3831])).

tff(c_3915,plain,(
    ! [C_741,J_735,E_740,F_738,D_739,B_737,G_743,H_742,A_736] :
      ( k11_mcart_1(E_740,F_738,G_743,H_742,J_735) = k11_mcart_1(A_736,B_737,C_741,D_739,J_735)
      | ~ m1_subset_1(J_735,k4_zfmisc_1(E_740,F_738,G_743,H_742))
      | ~ m1_subset_1(J_735,k4_zfmisc_1(A_736,B_737,C_741,D_739))
      | k1_xboole_0 = H_742
      | k1_xboole_0 = G_743
      | k1_xboole_0 = F_738
      | k1_xboole_0 = E_740
      | k1_xboole_0 = D_739
      | k1_xboole_0 = C_741
      | k1_xboole_0 = B_737
      | k1_xboole_0 = A_736 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_3931,plain,(
    ! [A_736,B_737,C_741,D_739] :
      ( k11_mcart_1(A_736,B_737,C_741,D_739,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_736,B_737,C_741,D_739))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_739
      | k1_xboole_0 = C_741
      | k1_xboole_0 = B_737
      | k1_xboole_0 = A_736 ) ),
    inference(resolution,[status(thm)],[c_48,c_3915])).

tff(c_3950,plain,(
    ! [A_736,B_737,C_741,D_739] :
      ( k11_mcart_1(A_736,B_737,C_741,D_739,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_736,B_737,C_741,D_739))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = D_739
      | k1_xboole_0 = C_741
      | k1_xboole_0 = B_737
      | k1_xboole_0 = A_736 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3528,c_3711,c_3914,c_3931])).

tff(c_3956,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_3950])).

tff(c_3979,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3956,c_57])).

tff(c_3982,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2135,c_3979])).

tff(c_3985,plain,(
    ! [A_744,B_745,C_746,D_747] :
      ( k11_mcart_1(A_744,B_745,C_746,D_747,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_744,B_745,C_746,D_747))
      | k1_xboole_0 = D_747
      | k1_xboole_0 = C_746
      | k1_xboole_0 = B_745
      | k1_xboole_0 = A_744 ) ),
    inference(splitRight,[status(thm)],[c_3950])).

tff(c_4004,plain,
    ( k11_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_3985])).

tff(c_4013,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_4004])).

tff(c_4038,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4013,c_57])).

tff(c_4041,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2117,c_4038])).

tff(c_4043,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_4004])).

tff(c_3984,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_3950])).

tff(c_3527,plain,(
    ! [A_646,B_647,C_651,D_649] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5'
      | k9_mcart_1(A_646,B_647,C_651,D_649,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_646,B_647,C_651,D_649))
      | k1_xboole_0 = D_649
      | k1_xboole_0 = C_651
      | k1_xboole_0 = B_647
      | k1_xboole_0 = A_646 ) ),
    inference(splitRight,[status(thm)],[c_3488])).

tff(c_4045,plain,(
    ! [A_748,B_749,C_750,D_751] :
      ( k9_mcart_1(A_748,B_749,C_750,D_751,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_748,B_749,C_750,D_751))
      | k1_xboole_0 = D_751
      | k1_xboole_0 = C_750
      | k1_xboole_0 = B_749
      | k1_xboole_0 = A_748 ) ),
    inference(negUnitSimplification,[status(thm)],[c_3984,c_3914,c_3711,c_3527])).

tff(c_4048,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_4045])).

tff(c_4066,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_4043,c_4048])).

tff(c_4085,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_4066])).

tff(c_4112,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4085,c_57])).

tff(c_4107,plain,(
    ! [A_27,C_29,D_30] : k4_zfmisc_1(A_27,'#skF_7',C_29,D_30) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4085,c_4085,c_26])).

tff(c_4265,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4107,c_73])).

tff(c_4269,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4112,c_4265])).

tff(c_4271,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_4066])).

tff(c_3828,plain,(
    ! [A_723,B_724,C_728,D_726] :
      ( k10_mcart_1(A_723,B_724,C_728,D_726,'#skF_10') = k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_723,B_724,C_728,D_726))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = D_726
      | k1_xboole_0 = C_728
      | k1_xboole_0 = B_724
      | k1_xboole_0 = A_723 ) ),
    inference(resolution,[status(thm)],[c_78,c_3796])).

tff(c_4272,plain,(
    ! [A_723,B_724,C_728,D_726] :
      ( k10_mcart_1(A_723,B_724,C_728,D_726,'#skF_10') = k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_723,B_724,C_728,D_726))
      | k1_xboole_0 = '#skF_9'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = D_726
      | k1_xboole_0 = C_728
      | k1_xboole_0 = B_724
      | k1_xboole_0 = A_723 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4043,c_4271,c_3828])).

tff(c_4273,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_4272])).

tff(c_4301,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4273,c_57])).

tff(c_4297,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,'#skF_8',D_30) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4273,c_4273,c_24])).

tff(c_4401,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4297,c_73])).

tff(c_4405,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4301,c_4401])).

tff(c_4407,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_4272])).

tff(c_4270,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_4066])).

tff(c_4413,plain,
    ( k1_xboole_0 = '#skF_9'
    | k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_4407,c_4270])).

tff(c_4414,plain,(
    k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_4413])).

tff(c_10,plain,(
    ! [C_18,B_17,A_16,D_19,E_20] :
      ( m1_subset_1(k9_mcart_1(A_16,B_17,C_18,D_19,E_20),B_17)
      | ~ m1_subset_1(E_20,k4_zfmisc_1(A_16,B_17,C_18,D_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4449,plain,
    ( m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4414,c_10])).

tff(c_4453,plain,(
    m1_subset_1(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_4449])).

tff(c_4455,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3443,c_4453])).

tff(c_4456,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_4413])).

tff(c_4486,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4456,c_57])).

tff(c_4489,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3409,c_4486])).

tff(c_4490,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_3442])).

tff(c_4495,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_4490,c_32])).

tff(c_4500,plain,(
    ! [A_27,C_29,D_30] : k4_zfmisc_1(A_27,'#skF_7',C_29,D_30) = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4495,c_4495,c_26])).

tff(c_4546,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4500,c_73])).

tff(c_4550,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4490,c_4546])).

tff(c_4551,plain,(
    ~ r2_hidden(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_3377])).

tff(c_4556,plain,
    ( v1_xboole_0('#skF_8')
    | ~ m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_18,c_4551])).

tff(c_4565,plain,(
    ~ m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_4556])).

tff(c_4552,plain,(
    r2_hidden(k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_3377])).

tff(c_4564,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_4552,c_34])).

tff(c_4577,plain,(
    ! [A_809,E_813,B_810,D_812,F_811,J_808,G_816,H_815,C_814] :
      ( k10_mcart_1(E_813,F_811,G_816,H_815,J_808) = k10_mcart_1(A_809,B_810,C_814,D_812,J_808)
      | ~ m1_subset_1(J_808,k4_zfmisc_1(E_813,F_811,G_816,H_815))
      | ~ m1_subset_1(J_808,k4_zfmisc_1(A_809,B_810,C_814,D_812))
      | k1_xboole_0 = H_815
      | k1_xboole_0 = G_816
      | k1_xboole_0 = F_811
      | k1_xboole_0 = E_813
      | k1_xboole_0 = D_812
      | k1_xboole_0 = C_814
      | k1_xboole_0 = B_810
      | k1_xboole_0 = A_809 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4610,plain,(
    ! [A_809,B_810,C_814,D_812] :
      ( k10_mcart_1(A_809,B_810,C_814,D_812,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_809,B_810,C_814,D_812))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_812
      | k1_xboole_0 = C_814
      | k1_xboole_0 = B_810
      | k1_xboole_0 = A_809 ) ),
    inference(resolution,[status(thm)],[c_48,c_4577])).

tff(c_4634,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_4610])).

tff(c_4645,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4634,c_57])).

tff(c_4648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2137,c_4645])).

tff(c_4650,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_4610])).

tff(c_4711,plain,(
    ! [D_854,F_853,G_858,B_852,H_857,C_856,E_855,J_850,A_851] :
      ( k11_mcart_1(E_855,F_853,G_858,H_857,J_850) = k11_mcart_1(A_851,B_852,C_856,D_854,J_850)
      | ~ m1_subset_1(J_850,k4_zfmisc_1(E_855,F_853,G_858,H_857))
      | ~ m1_subset_1(J_850,k4_zfmisc_1(A_851,B_852,C_856,D_854))
      | k1_xboole_0 = H_857
      | k1_xboole_0 = G_858
      | k1_xboole_0 = F_853
      | k1_xboole_0 = E_855
      | k1_xboole_0 = D_854
      | k1_xboole_0 = C_856
      | k1_xboole_0 = B_852
      | k1_xboole_0 = A_851 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4727,plain,(
    ! [A_851,B_852,C_856,D_854] :
      ( k11_mcart_1(A_851,B_852,C_856,D_854,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_851,B_852,C_856,D_854))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_854
      | k1_xboole_0 = C_856
      | k1_xboole_0 = B_852
      | k1_xboole_0 = A_851 ) ),
    inference(resolution,[status(thm)],[c_48,c_4711])).

tff(c_4746,plain,(
    ! [A_851,B_852,C_856,D_854] :
      ( k11_mcart_1(A_851,B_852,C_856,D_854,'#skF_10') = k11_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_851,B_852,C_856,D_854))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = D_854
      | k1_xboole_0 = C_856
      | k1_xboole_0 = B_852
      | k1_xboole_0 = A_851 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4650,c_4727])).

tff(c_4812,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_4746])).

tff(c_4828,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4812,c_57])).

tff(c_4831,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2138,c_4828])).

tff(c_4833,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_4746])).

tff(c_4918,plain,(
    ! [C_891,G_893,H_892,D_889,B_887,J_885,E_890,A_886,F_888] :
      ( k8_mcart_1(E_890,F_888,G_893,H_892,J_885) = k8_mcart_1(A_886,B_887,C_891,D_889,J_885)
      | ~ m1_subset_1(J_885,k4_zfmisc_1(E_890,F_888,G_893,H_892))
      | ~ m1_subset_1(J_885,k4_zfmisc_1(A_886,B_887,C_891,D_889))
      | k1_xboole_0 = H_892
      | k1_xboole_0 = G_893
      | k1_xboole_0 = F_888
      | k1_xboole_0 = E_890
      | k1_xboole_0 = D_889
      | k1_xboole_0 = C_891
      | k1_xboole_0 = B_887
      | k1_xboole_0 = A_886 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_4934,plain,(
    ! [A_886,B_887,C_891,D_889] :
      ( k8_mcart_1(A_886,B_887,C_891,D_889,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_886,B_887,C_891,D_889))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_889
      | k1_xboole_0 = C_891
      | k1_xboole_0 = B_887
      | k1_xboole_0 = A_886 ) ),
    inference(resolution,[status(thm)],[c_48,c_4918])).

tff(c_4953,plain,(
    ! [A_886,B_887,C_891,D_889] :
      ( k8_mcart_1(A_886,B_887,C_891,D_889,'#skF_10') = k8_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_886,B_887,C_891,D_889))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = D_889
      | k1_xboole_0 = C_891
      | k1_xboole_0 = B_887
      | k1_xboole_0 = A_886 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4650,c_4833,c_4934])).

tff(c_5010,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_4953])).

tff(c_5031,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5010,c_57])).

tff(c_5034,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2136,c_5031])).

tff(c_5036,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_4953])).

tff(c_5037,plain,(
    ! [H_905,D_902,B_900,J_898,F_901,E_903,G_906,C_904,A_899] :
      ( k9_mcart_1(E_903,F_901,G_906,H_905,J_898) = k9_mcart_1(A_899,B_900,C_904,D_902,J_898)
      | ~ m1_subset_1(J_898,k4_zfmisc_1(E_903,F_901,G_906,H_905))
      | ~ m1_subset_1(J_898,k4_zfmisc_1(A_899,B_900,C_904,D_902))
      | k1_xboole_0 = H_905
      | k1_xboole_0 = G_906
      | k1_xboole_0 = F_901
      | k1_xboole_0 = E_903
      | k1_xboole_0 = D_902
      | k1_xboole_0 = C_904
      | k1_xboole_0 = B_900
      | k1_xboole_0 = A_899 ) ),
    inference(cnfTransformation,[status(thm)],[f_128])).

tff(c_5053,plain,(
    ! [A_899,B_900,C_904,D_902] :
      ( k9_mcart_1(A_899,B_900,C_904,D_902,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_899,B_900,C_904,D_902))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = D_902
      | k1_xboole_0 = C_904
      | k1_xboole_0 = B_900
      | k1_xboole_0 = A_899 ) ),
    inference(resolution,[status(thm)],[c_48,c_5037])).

tff(c_5072,plain,(
    ! [A_899,B_900,C_904,D_902] :
      ( k9_mcart_1(A_899,B_900,C_904,D_902,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_899,B_900,C_904,D_902))
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = D_902
      | k1_xboole_0 = C_904
      | k1_xboole_0 = B_900
      | k1_xboole_0 = A_899 ) ),
    inference(negUnitSimplification,[status(thm)],[c_4650,c_4833,c_5036,c_5053])).

tff(c_5078,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_5072])).

tff(c_5101,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5078,c_57])).

tff(c_5104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2135,c_5101])).

tff(c_5107,plain,(
    ! [A_907,B_908,C_909,D_910] :
      ( k9_mcart_1(A_907,B_908,C_909,D_910,'#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_907,B_908,C_909,D_910))
      | k1_xboole_0 = D_910
      | k1_xboole_0 = C_909
      | k1_xboole_0 = B_908
      | k1_xboole_0 = A_907 ) ),
    inference(splitRight,[status(thm)],[c_5072])).

tff(c_5126,plain,
    ( k9_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k9_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_5107])).

tff(c_5135,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5126])).

tff(c_5160,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5135,c_57])).

tff(c_5163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2117,c_5160])).

tff(c_5165,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5126])).

tff(c_5106,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_5072])).

tff(c_4649,plain,(
    ! [A_809,B_810,C_814,D_812] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_5'
      | k10_mcart_1(A_809,B_810,C_814,D_812,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_809,B_810,C_814,D_812))
      | k1_xboole_0 = D_812
      | k1_xboole_0 = C_814
      | k1_xboole_0 = B_810
      | k1_xboole_0 = A_809 ) ),
    inference(splitRight,[status(thm)],[c_4610])).

tff(c_5167,plain,(
    ! [A_911,B_912,C_913,D_914] :
      ( k10_mcart_1(A_911,B_912,C_913,D_914,'#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_911,B_912,C_913,D_914))
      | k1_xboole_0 = D_914
      | k1_xboole_0 = C_913
      | k1_xboole_0 = B_912
      | k1_xboole_0 = A_911 ) ),
    inference(negUnitSimplification,[status(thm)],[c_5106,c_5036,c_4833,c_4649])).

tff(c_5170,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_78,c_5167])).

tff(c_5188,plain,
    ( k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10')
    | k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(negUnitSimplification,[status(thm)],[c_5165,c_5170])).

tff(c_5207,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_5188])).

tff(c_5234,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5207,c_57])).

tff(c_5237,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4564,c_5234])).

tff(c_5238,plain,
    ( k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_9'
    | k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitRight,[status(thm)],[c_5188])).

tff(c_5271,plain,(
    k10_mcart_1('#skF_6','#skF_7','#skF_8','#skF_9','#skF_10') = k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10') ),
    inference(splitLeft,[status(thm)],[c_5238])).

tff(c_4,plain,(
    ! [B_2,C_3,A_1,E_5,D_4] :
      ( m1_subset_1(k10_mcart_1(A_1,B_2,C_3,D_4,E_5),C_3)
      | ~ m1_subset_1(E_5,k4_zfmisc_1(A_1,B_2,C_3,D_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_5275,plain,
    ( m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8')
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_8','#skF_9')) ),
    inference(superposition,[status(thm),theory(equality)],[c_5271,c_4])).

tff(c_5279,plain,(
    m1_subset_1(k10_mcart_1('#skF_2','#skF_3','#skF_4','#skF_5','#skF_10'),'#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5275])).

tff(c_5281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4565,c_5279])).

tff(c_5282,plain,
    ( k1_xboole_0 = '#skF_9'
    | k1_xboole_0 = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_5238])).

tff(c_5284,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_5282])).

tff(c_5315,plain,(
    v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5284,c_57])).

tff(c_5311,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,'#skF_8',D_30) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5284,c_5284,c_24])).

tff(c_5389,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5311,c_73])).

tff(c_5393,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5315,c_5389])).

tff(c_5394,plain,(
    k1_xboole_0 = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_5282])).

tff(c_5430,plain,(
    v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5394,c_57])).

tff(c_5433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3409,c_5430])).

tff(c_5434,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_4556])).

tff(c_5444,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_5434,c_32])).

tff(c_5450,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,'#skF_8',D_30) = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5444,c_5444,c_24])).

tff(c_5490,plain,(
    ~ v1_xboole_0('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5450,c_73])).

tff(c_5494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5434,c_5490])).

tff(c_5539,plain,(
    ! [A_946] : ~ r2_hidden(A_946,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2133])).

tff(c_5544,plain,(
    ! [A_25] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_25,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_18,c_5539])).

tff(c_5552,plain,(
    ! [A_948] : ~ m1_subset_1(A_948,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_5544])).

tff(c_5557,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_5552])).

tff(c_5558,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_5544])).

tff(c_5496,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_2133])).

tff(c_5500,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5496,c_32])).

tff(c_5527,plain,(
    ! [A_34] :
      ( A_34 = '#skF_3'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5500,c_32])).

tff(c_5562,plain,(
    '#skF_7' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_5558,c_5527])).

tff(c_5495,plain,(
    ! [A_421] : ~ r2_hidden(A_421,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_2133])).

tff(c_5564,plain,(
    ! [A_421] : ~ r2_hidden(A_421,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5562,c_5495])).

tff(c_5523,plain,(
    ! [A_27,C_29,D_30] : k4_zfmisc_1(A_27,'#skF_3',C_29,D_30) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5500,c_5500,c_26])).

tff(c_5567,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_3','#skF_8','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5562,c_46])).

tff(c_5606,plain,(
    r2_hidden('#skF_10','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5523,c_5567])).

tff(c_5609,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5564,c_5606])).

tff(c_5610,plain,(
    ! [A_421] : ~ r2_hidden(A_421,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_2131])).

tff(c_5635,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5610,c_2109])).

tff(c_5659,plain,(
    ! [A_962] : ~ r2_hidden(A_962,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_5664,plain,(
    ! [A_25] :
      ( v1_xboole_0('#skF_8')
      | ~ m1_subset_1(A_25,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_18,c_5659])).

tff(c_5675,plain,(
    ! [A_968] : ~ m1_subset_1(A_968,'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_5664])).

tff(c_5680,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_5675])).

tff(c_5681,plain,(
    v1_xboole_0('#skF_8') ),
    inference(splitRight,[status(thm)],[c_5664])).

tff(c_5637,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_5641,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5637,c_32])).

tff(c_5646,plain,(
    ! [A_34] :
      ( A_34 = '#skF_4'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5641,c_32])).

tff(c_5685,plain,(
    '#skF_8' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5681,c_5646])).

tff(c_5636,plain,(
    ! [A_421] : ~ r2_hidden(A_421,'#skF_8') ),
    inference(splitRight,[status(thm)],[c_2134])).

tff(c_5687,plain,(
    ! [A_421] : ~ r2_hidden(A_421,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_5636])).

tff(c_5643,plain,(
    ! [A_27,B_28,D_30] : k4_zfmisc_1(A_27,B_28,'#skF_4',D_30) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5641,c_5641,c_24])).

tff(c_5690,plain,(
    r2_hidden('#skF_10',k4_zfmisc_1('#skF_6','#skF_7','#skF_4','#skF_9')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5685,c_46])).

tff(c_5775,plain,(
    r2_hidden('#skF_10','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5643,c_5690])).

tff(c_5776,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5687,c_5775])).

tff(c_5799,plain,(
    ! [A_984] : ~ r2_hidden(A_984,'#skF_9') ),
    inference(splitRight,[status(thm)],[c_2130])).

tff(c_5804,plain,(
    ! [A_25] :
      ( v1_xboole_0('#skF_9')
      | ~ m1_subset_1(A_25,'#skF_9') ) ),
    inference(resolution,[status(thm)],[c_18,c_5799])).

tff(c_5817,plain,(
    ! [A_990] : ~ m1_subset_1(A_990,'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_5804])).

tff(c_5822,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_14,c_5817])).

tff(c_5823,plain,(
    v1_xboole_0('#skF_9') ),
    inference(splitRight,[status(thm)],[c_5804])).

tff(c_5778,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_2130])).

tff(c_5782,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_5778,c_32])).

tff(c_5787,plain,(
    ! [A_34] :
      ( A_34 = '#skF_5'
      | ~ v1_xboole_0(A_34) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_32])).

tff(c_5827,plain,(
    '#skF_5' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_5823,c_5787])).

tff(c_5785,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5782,c_5782,c_22])).

tff(c_5913,plain,(
    ! [A_27,B_28,C_29] : k4_zfmisc_1(A_27,B_28,C_29,'#skF_9') = '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5827,c_5827,c_5785])).

tff(c_5915,plain,(
    ~ v1_xboole_0('#skF_9') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5913,c_73])).

tff(c_5919,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5823,c_5915])).

%------------------------------------------------------------------------------
