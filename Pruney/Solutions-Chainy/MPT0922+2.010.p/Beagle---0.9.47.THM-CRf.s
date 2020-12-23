%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:20 EST 2020

% Result     : Theorem 4.20s
% Output     : CNFRefutation 4.20s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 490 expanded)
%              Number of leaves         :   27 ( 207 expanded)
%              Depth                    :   20
%              Number of atoms          :  252 (3310 expanded)
%              Number of equality atoms :  192 (2141 expanded)
%              Maximal formula depth    :   21 (   8 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_134,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
       => ( ! [G] :
              ( m1_subset_1(G,A)
             => ! [H] :
                  ( m1_subset_1(H,B)
                 => ! [I] :
                      ( m1_subset_1(I,C)
                     => ! [J] :
                          ( m1_subset_1(J,D)
                         => ( F = k4_mcart_1(G,H,I,J)
                           => E = J ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k11_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t82_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ~ ! [E] :
              ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
             => ( k8_mcart_1(A,B,C,D,E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k9_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E)))
                & k10_mcart_1(A,B,C,D,E) = k2_mcart_1(k1_mcart_1(E))
                & k11_mcart_1(A,B,C,D,E) = k2_mcart_1(E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_mcart_1)).

tff(f_105,axiom,(
    ! [A,B,C,D,E,F] :
      ( m1_subset_1(F,k4_zfmisc_1(A,B,C,D))
     => ( ! [G] :
            ( m1_subset_1(G,A)
           => ! [H] :
                ( m1_subset_1(H,B)
               => ! [I] :
                    ( m1_subset_1(I,C)
                   => ! [J] :
                        ( m1_subset_1(J,D)
                       => ( F = k4_mcart_1(G,H,I,J)
                         => E = G ) ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | E = k8_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

tff(f_77,axiom,(
    ! [A,B,C,D,E] :
      ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & D != k1_xboole_0
          & ? [F,G,H,I] :
              ( E = k4_mcart_1(F,G,H,I)
              & ~ ( k8_mcart_1(A,B,C,D,E) = F
                  & k9_mcart_1(A,B,C,D,E) = G
                  & k10_mcart_1(A,B,C,D,E) = H
                  & k11_mcart_1(A,B,C,D,E) = I ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_mcart_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_44,plain,(
    ! [B_87,D_86,E_89,C_88,A_90] :
      ( k11_mcart_1(A_90,B_87,C_88,D_86,E_89) = k2_mcart_1(E_89)
      | ~ m1_subset_1(E_89,k4_zfmisc_1(A_90,B_87,C_88,D_86))
      | k1_xboole_0 = D_86
      | k1_xboole_0 = C_88
      | k1_xboole_0 = B_87
      | k1_xboole_0 = A_90 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_47,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_44])).

tff(c_50,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_47])).

tff(c_30,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_51,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_30])).

tff(c_22,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( m1_subset_1('#skF_4'(C_22,B_21,D_23,E_24,A_20,F_25),D_23)
      | k8_mcart_1(A_20,B_21,C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(F_25,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_24,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( m1_subset_1('#skF_3'(C_22,B_21,D_23,E_24,A_20,F_25),C_22)
      | k8_mcart_1(A_20,B_21,C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(F_25,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_28,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( m1_subset_1('#skF_1'(C_22,B_21,D_23,E_24,A_20,F_25),A_20)
      | k8_mcart_1(A_20,B_21,C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(F_25,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_26,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( m1_subset_1('#skF_2'(C_22,B_21,D_23,E_24,A_20,F_25),B_21)
      | k8_mcart_1(A_20,B_21,C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(F_25,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_177,plain,(
    ! [D_170,F_173,A_172,C_168,E_171,B_169] :
      ( k4_mcart_1('#skF_1'(C_168,B_169,D_170,E_171,A_172,F_173),'#skF_2'(C_168,B_169,D_170,E_171,A_172,F_173),'#skF_3'(C_168,B_169,D_170,E_171,A_172,F_173),'#skF_4'(C_168,B_169,D_170,E_171,A_172,F_173)) = F_173
      | k8_mcart_1(A_172,B_169,C_168,D_170,F_173) = E_171
      | k1_xboole_0 = D_170
      | k1_xboole_0 = C_168
      | k1_xboole_0 = B_169
      | k1_xboole_0 = A_172
      | ~ m1_subset_1(F_173,k4_zfmisc_1(A_172,B_169,C_168,D_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_40,plain,(
    ! [J_81,G_67,H_75,I_79] :
      ( J_81 = '#skF_9'
      | k4_mcart_1(G_67,H_75,I_79,J_81) != '#skF_10'
      | ~ m1_subset_1(J_81,'#skF_8')
      | ~ m1_subset_1(I_79,'#skF_7')
      | ~ m1_subset_1(H_75,'#skF_6')
      | ~ m1_subset_1(G_67,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_201,plain,(
    ! [C_176,B_177,A_178,D_179,E_174,F_175] :
      ( '#skF_4'(C_176,B_177,D_179,E_174,A_178,F_175) = '#skF_9'
      | F_175 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_176,B_177,D_179,E_174,A_178,F_175),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_176,B_177,D_179,E_174,A_178,F_175),'#skF_7')
      | ~ m1_subset_1('#skF_2'(C_176,B_177,D_179,E_174,A_178,F_175),'#skF_6')
      | ~ m1_subset_1('#skF_1'(C_176,B_177,D_179,E_174,A_178,F_175),'#skF_5')
      | k8_mcart_1(A_178,B_177,C_176,D_179,F_175) = E_174
      | k1_xboole_0 = D_179
      | k1_xboole_0 = C_176
      | k1_xboole_0 = B_177
      | k1_xboole_0 = A_178
      | ~ m1_subset_1(F_175,k4_zfmisc_1(A_178,B_177,C_176,D_179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_40])).

tff(c_205,plain,(
    ! [C_22,D_23,A_20,F_25,E_24] :
      ( '#skF_4'(C_22,'#skF_6',D_23,E_24,A_20,F_25) = '#skF_9'
      | F_25 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_22,'#skF_6',D_23,E_24,A_20,F_25),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_22,'#skF_6',D_23,E_24,A_20,F_25),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_22,'#skF_6',D_23,E_24,A_20,F_25),'#skF_5')
      | k8_mcart_1(A_20,'#skF_6',C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(F_25,k4_zfmisc_1(A_20,'#skF_6',C_22,D_23)) ) ),
    inference(resolution,[status(thm)],[c_26,c_201])).

tff(c_210,plain,(
    ! [D_181,F_184,C_180,A_183,E_182] :
      ( '#skF_4'(C_180,'#skF_6',D_181,E_182,A_183,F_184) = '#skF_9'
      | F_184 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_180,'#skF_6',D_181,E_182,A_183,F_184),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_180,'#skF_6',D_181,E_182,A_183,F_184),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_180,'#skF_6',D_181,E_182,A_183,F_184),'#skF_5')
      | k8_mcart_1(A_183,'#skF_6',C_180,D_181,F_184) = E_182
      | k1_xboole_0 = D_181
      | k1_xboole_0 = C_180
      | k1_xboole_0 = A_183
      | ~ m1_subset_1(F_184,k4_zfmisc_1(A_183,'#skF_6',C_180,D_181)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_205])).

tff(c_214,plain,(
    ! [C_22,D_23,E_24,F_25] :
      ( '#skF_4'(C_22,'#skF_6',D_23,E_24,'#skF_5',F_25) = '#skF_9'
      | F_25 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_22,'#skF_6',D_23,E_24,'#skF_5',F_25),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_22,'#skF_6',D_23,E_24,'#skF_5',F_25),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_25,k4_zfmisc_1('#skF_5','#skF_6',C_22,D_23)) ) ),
    inference(resolution,[status(thm)],[c_28,c_210])).

tff(c_219,plain,(
    ! [C_185,D_186,E_187,F_188] :
      ( '#skF_4'(C_185,'#skF_6',D_186,E_187,'#skF_5',F_188) = '#skF_9'
      | F_188 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_185,'#skF_6',D_186,E_187,'#skF_5',F_188),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_185,'#skF_6',D_186,E_187,'#skF_5',F_188),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_185,D_186,F_188) = E_187
      | k1_xboole_0 = D_186
      | k1_xboole_0 = C_185
      | ~ m1_subset_1(F_188,k4_zfmisc_1('#skF_5','#skF_6',C_185,D_186)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_38,c_214])).

tff(c_223,plain,(
    ! [D_23,E_24,F_25] :
      ( '#skF_4'('#skF_7','#skF_6',D_23,E_24,'#skF_5',F_25) = '#skF_9'
      | F_25 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_6',D_23,E_24,'#skF_5',F_25),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_25,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_23)) ) ),
    inference(resolution,[status(thm)],[c_24,c_219])).

tff(c_228,plain,(
    ! [D_189,E_190,F_191] :
      ( '#skF_4'('#skF_7','#skF_6',D_189,E_190,'#skF_5',F_191) = '#skF_9'
      | F_191 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_6',D_189,E_190,'#skF_5',F_191),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_189,F_191) = E_190
      | k1_xboole_0 = D_189
      | ~ m1_subset_1(F_191,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_189)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_34,c_223])).

tff(c_232,plain,(
    ! [E_24,F_25] :
      ( '#skF_4'('#skF_7','#skF_6','#skF_8',E_24,'#skF_5',F_25) = '#skF_9'
      | F_25 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_25) = E_24
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_25,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_22,c_228])).

tff(c_237,plain,(
    ! [E_192,F_193] :
      ( '#skF_4'('#skF_7','#skF_6','#skF_8',E_192,'#skF_5',F_193) = '#skF_9'
      | F_193 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_193) = E_192
      | ~ m1_subset_1(F_193,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_32,c_232])).

tff(c_259,plain,(
    ! [E_194] :
      ( '#skF_4'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10') = '#skF_9'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(resolution,[status(thm)],[c_42,c_237])).

tff(c_20,plain,(
    ! [C_22,D_23,A_20,B_21,F_25,E_24] :
      ( k4_mcart_1('#skF_1'(C_22,B_21,D_23,E_24,A_20,F_25),'#skF_2'(C_22,B_21,D_23,E_24,A_20,F_25),'#skF_3'(C_22,B_21,D_23,E_24,A_20,F_25),'#skF_4'(C_22,B_21,D_23,E_24,A_20,F_25)) = F_25
      | k8_mcart_1(A_20,B_21,C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(F_25,k4_zfmisc_1(A_20,B_21,C_22,D_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_268,plain,(
    ! [E_194] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_3'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_9') = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_259,c_20])).

tff(c_631,plain,(
    ! [E_194] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_3'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_9') = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_268])).

tff(c_632,plain,(
    ! [E_194] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_3'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_9') = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_631])).

tff(c_728,plain,(
    ! [E_2213] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_2213,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_2213,'#skF_5','#skF_10'),'#skF_3'('#skF_7','#skF_6','#skF_8',E_2213,'#skF_5','#skF_10'),'#skF_9') = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_2213 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_631])).

tff(c_10,plain,(
    ! [G_17,I_19,F_16,D_10,A_7,B_8,H_18,C_9] :
      ( k11_mcart_1(A_7,B_8,C_9,D_10,k4_mcart_1(F_16,G_17,H_18,I_19)) = I_19
      | k1_xboole_0 = D_10
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | ~ m1_subset_1(k4_mcart_1(F_16,G_17,H_18,I_19),k4_zfmisc_1(A_7,B_8,C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_993,plain,(
    ! [C_2666,B_2665,A_2667,E_2668,D_2664] :
      ( k11_mcart_1(A_2667,B_2665,C_2666,D_2664,k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_2668,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_2668,'#skF_5','#skF_10'),'#skF_3'('#skF_7','#skF_6','#skF_8',E_2668,'#skF_5','#skF_10'),'#skF_9')) = '#skF_9'
      | k1_xboole_0 = D_2664
      | k1_xboole_0 = C_2666
      | k1_xboole_0 = B_2665
      | k1_xboole_0 = A_2667
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_2667,B_2665,C_2666,D_2664))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_2668 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_10])).

tff(c_1002,plain,(
    ! [C_2666,E_194,B_2665,A_2667,D_2664] :
      ( k11_mcart_1(A_2667,B_2665,C_2666,D_2664,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_2664
      | k1_xboole_0 = C_2666
      | k1_xboole_0 = B_2665
      | k1_xboole_0 = A_2667
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_2667,B_2665,C_2666,D_2664))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_632,c_993])).

tff(c_1028,plain,(
    ! [E_194] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(splitLeft,[status(thm)],[c_1002])).

tff(c_2144,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_5' ),
    inference(factorization,[status(thm),theory(equality)],[c_1028])).

tff(c_1049,plain,(
    ! [E_194] : k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ),
    inference(factorization,[status(thm),theory(equality)],[c_1028])).

tff(c_2701,plain,(
    ! [E_11321] : E_11321 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2144,c_1049])).

tff(c_2939,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2701,c_38])).

tff(c_2941,plain,(
    ! [A_12672,B_12673,C_12674,D_12675] :
      ( k11_mcart_1(A_12672,B_12673,C_12674,D_12675,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_12675
      | k1_xboole_0 = C_12674
      | k1_xboole_0 = B_12673
      | k1_xboole_0 = A_12672
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_12672,B_12673,C_12674,D_12675)) ) ),
    inference(splitRight,[status(thm)],[c_1002])).

tff(c_2945,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_2941])).

tff(c_2947,plain,
    ( k2_mcart_1('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_2945])).

tff(c_2949,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_51,c_2947])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.20/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.73  
% 4.20/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.73  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 4.20/1.73  
% 4.20/1.73  %Foreground sorts:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Background operators:
% 4.20/1.73  
% 4.20/1.73  
% 4.20/1.73  %Foreground operators:
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.20/1.73  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.20/1.73  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.20/1.73  tff('#skF_7', type, '#skF_7': $i).
% 4.20/1.73  tff('#skF_10', type, '#skF_10': $i).
% 4.20/1.73  tff('#skF_5', type, '#skF_5': $i).
% 4.20/1.73  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff('#skF_6', type, '#skF_6': $i).
% 4.20/1.73  tff('#skF_9', type, '#skF_9': $i).
% 4.20/1.73  tff('#skF_8', type, '#skF_8': $i).
% 4.20/1.73  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.20/1.73  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.20/1.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.20/1.73  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.20/1.73  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.20/1.73  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 4.20/1.73  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.20/1.73  
% 4.20/1.75  tff(f_134, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_mcart_1)).
% 4.20/1.75  tff(f_50, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 4.20/1.75  tff(f_105, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 4.20/1.75  tff(f_77, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 4.20/1.75  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.20/1.75  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.20/1.75  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.20/1.75  tff(c_32, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.20/1.75  tff(c_42, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.20/1.75  tff(c_44, plain, (![B_87, D_86, E_89, C_88, A_90]: (k11_mcart_1(A_90, B_87, C_88, D_86, E_89)=k2_mcart_1(E_89) | ~m1_subset_1(E_89, k4_zfmisc_1(A_90, B_87, C_88, D_86)) | k1_xboole_0=D_86 | k1_xboole_0=C_88 | k1_xboole_0=B_87 | k1_xboole_0=A_90)), inference(cnfTransformation, [status(thm)], [f_50])).
% 4.20/1.75  tff(c_47, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_44])).
% 4.20/1.75  tff(c_50, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_47])).
% 4.20/1.75  tff(c_30, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.20/1.75  tff(c_51, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_30])).
% 4.20/1.75  tff(c_22, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_4'(C_22, B_21, D_23, E_24, A_20, F_25), D_23) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.20/1.75  tff(c_24, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_3'(C_22, B_21, D_23, E_24, A_20, F_25), C_22) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.20/1.75  tff(c_28, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_1'(C_22, B_21, D_23, E_24, A_20, F_25), A_20) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.20/1.75  tff(c_26, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_2'(C_22, B_21, D_23, E_24, A_20, F_25), B_21) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.20/1.75  tff(c_177, plain, (![D_170, F_173, A_172, C_168, E_171, B_169]: (k4_mcart_1('#skF_1'(C_168, B_169, D_170, E_171, A_172, F_173), '#skF_2'(C_168, B_169, D_170, E_171, A_172, F_173), '#skF_3'(C_168, B_169, D_170, E_171, A_172, F_173), '#skF_4'(C_168, B_169, D_170, E_171, A_172, F_173))=F_173 | k8_mcart_1(A_172, B_169, C_168, D_170, F_173)=E_171 | k1_xboole_0=D_170 | k1_xboole_0=C_168 | k1_xboole_0=B_169 | k1_xboole_0=A_172 | ~m1_subset_1(F_173, k4_zfmisc_1(A_172, B_169, C_168, D_170)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.20/1.75  tff(c_40, plain, (![J_81, G_67, H_75, I_79]: (J_81='#skF_9' | k4_mcart_1(G_67, H_75, I_79, J_81)!='#skF_10' | ~m1_subset_1(J_81, '#skF_8') | ~m1_subset_1(I_79, '#skF_7') | ~m1_subset_1(H_75, '#skF_6') | ~m1_subset_1(G_67, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.20/1.75  tff(c_201, plain, (![C_176, B_177, A_178, D_179, E_174, F_175]: ('#skF_4'(C_176, B_177, D_179, E_174, A_178, F_175)='#skF_9' | F_175!='#skF_10' | ~m1_subset_1('#skF_4'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_8') | ~m1_subset_1('#skF_3'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_7') | ~m1_subset_1('#skF_2'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_6') | ~m1_subset_1('#skF_1'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_5') | k8_mcart_1(A_178, B_177, C_176, D_179, F_175)=E_174 | k1_xboole_0=D_179 | k1_xboole_0=C_176 | k1_xboole_0=B_177 | k1_xboole_0=A_178 | ~m1_subset_1(F_175, k4_zfmisc_1(A_178, B_177, C_176, D_179)))), inference(superposition, [status(thm), theory('equality')], [c_177, c_40])).
% 4.20/1.75  tff(c_205, plain, (![C_22, D_23, A_20, F_25, E_24]: ('#skF_4'(C_22, '#skF_6', D_23, E_24, A_20, F_25)='#skF_9' | F_25!='#skF_10' | ~m1_subset_1('#skF_4'(C_22, '#skF_6', D_23, E_24, A_20, F_25), '#skF_8') | ~m1_subset_1('#skF_3'(C_22, '#skF_6', D_23, E_24, A_20, F_25), '#skF_7') | ~m1_subset_1('#skF_1'(C_22, '#skF_6', D_23, E_24, A_20, F_25), '#skF_5') | k8_mcart_1(A_20, '#skF_6', C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0='#skF_6' | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, '#skF_6', C_22, D_23)))), inference(resolution, [status(thm)], [c_26, c_201])).
% 4.20/1.75  tff(c_210, plain, (![D_181, F_184, C_180, A_183, E_182]: ('#skF_4'(C_180, '#skF_6', D_181, E_182, A_183, F_184)='#skF_9' | F_184!='#skF_10' | ~m1_subset_1('#skF_4'(C_180, '#skF_6', D_181, E_182, A_183, F_184), '#skF_8') | ~m1_subset_1('#skF_3'(C_180, '#skF_6', D_181, E_182, A_183, F_184), '#skF_7') | ~m1_subset_1('#skF_1'(C_180, '#skF_6', D_181, E_182, A_183, F_184), '#skF_5') | k8_mcart_1(A_183, '#skF_6', C_180, D_181, F_184)=E_182 | k1_xboole_0=D_181 | k1_xboole_0=C_180 | k1_xboole_0=A_183 | ~m1_subset_1(F_184, k4_zfmisc_1(A_183, '#skF_6', C_180, D_181)))), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_205])).
% 4.20/1.75  tff(c_214, plain, (![C_22, D_23, E_24, F_25]: ('#skF_4'(C_22, '#skF_6', D_23, E_24, '#skF_5', F_25)='#skF_9' | F_25!='#skF_10' | ~m1_subset_1('#skF_4'(C_22, '#skF_6', D_23, E_24, '#skF_5', F_25), '#skF_8') | ~m1_subset_1('#skF_3'(C_22, '#skF_6', D_23, E_24, '#skF_5', F_25), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_25, k4_zfmisc_1('#skF_5', '#skF_6', C_22, D_23)))), inference(resolution, [status(thm)], [c_28, c_210])).
% 4.20/1.75  tff(c_219, plain, (![C_185, D_186, E_187, F_188]: ('#skF_4'(C_185, '#skF_6', D_186, E_187, '#skF_5', F_188)='#skF_9' | F_188!='#skF_10' | ~m1_subset_1('#skF_4'(C_185, '#skF_6', D_186, E_187, '#skF_5', F_188), '#skF_8') | ~m1_subset_1('#skF_3'(C_185, '#skF_6', D_186, E_187, '#skF_5', F_188), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_185, D_186, F_188)=E_187 | k1_xboole_0=D_186 | k1_xboole_0=C_185 | ~m1_subset_1(F_188, k4_zfmisc_1('#skF_5', '#skF_6', C_185, D_186)))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_38, c_214])).
% 4.20/1.75  tff(c_223, plain, (![D_23, E_24, F_25]: ('#skF_4'('#skF_7', '#skF_6', D_23, E_24, '#skF_5', F_25)='#skF_9' | F_25!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_7', '#skF_6', D_23, E_24, '#skF_5', F_25), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_25, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_23)))), inference(resolution, [status(thm)], [c_24, c_219])).
% 4.20/1.75  tff(c_228, plain, (![D_189, E_190, F_191]: ('#skF_4'('#skF_7', '#skF_6', D_189, E_190, '#skF_5', F_191)='#skF_9' | F_191!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_7', '#skF_6', D_189, E_190, '#skF_5', F_191), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_189, F_191)=E_190 | k1_xboole_0=D_189 | ~m1_subset_1(F_191, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_189)))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_34, c_223])).
% 4.20/1.75  tff(c_232, plain, (![E_24, F_25]: ('#skF_4'('#skF_7', '#skF_6', '#skF_8', E_24, '#skF_5', F_25)='#skF_9' | F_25!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_25)=E_24 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_25, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_22, c_228])).
% 4.20/1.75  tff(c_237, plain, (![E_192, F_193]: ('#skF_4'('#skF_7', '#skF_6', '#skF_8', E_192, '#skF_5', F_193)='#skF_9' | F_193!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_193)=E_192 | ~m1_subset_1(F_193, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_32, c_232])).
% 4.20/1.75  tff(c_259, plain, (![E_194]: ('#skF_4'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10')='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(resolution, [status(thm)], [c_42, c_237])).
% 4.20/1.75  tff(c_20, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k4_mcart_1('#skF_1'(C_22, B_21, D_23, E_24, A_20, F_25), '#skF_2'(C_22, B_21, D_23, E_24, A_20, F_25), '#skF_3'(C_22, B_21, D_23, E_24, A_20, F_25), '#skF_4'(C_22, B_21, D_23, E_24, A_20, F_25))=F_25 | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.20/1.75  tff(c_268, plain, (![E_194]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_3'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_9')='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(superposition, [status(thm), theory('equality')], [c_259, c_20])).
% 4.20/1.75  tff(c_631, plain, (![E_194]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_3'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_9')='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_268])).
% 4.20/1.75  tff(c_632, plain, (![E_194]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_3'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_9')='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_631])).
% 4.20/1.75  tff(c_728, plain, (![E_2213]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_2213, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_2213, '#skF_5', '#skF_10'), '#skF_3'('#skF_7', '#skF_6', '#skF_8', E_2213, '#skF_5', '#skF_10'), '#skF_9')='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_2213)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_631])).
% 4.20/1.75  tff(c_10, plain, (![G_17, I_19, F_16, D_10, A_7, B_8, H_18, C_9]: (k11_mcart_1(A_7, B_8, C_9, D_10, k4_mcart_1(F_16, G_17, H_18, I_19))=I_19 | k1_xboole_0=D_10 | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7 | ~m1_subset_1(k4_mcart_1(F_16, G_17, H_18, I_19), k4_zfmisc_1(A_7, B_8, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.20/1.75  tff(c_993, plain, (![C_2666, B_2665, A_2667, E_2668, D_2664]: (k11_mcart_1(A_2667, B_2665, C_2666, D_2664, k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_2668, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_2668, '#skF_5', '#skF_10'), '#skF_3'('#skF_7', '#skF_6', '#skF_8', E_2668, '#skF_5', '#skF_10'), '#skF_9'))='#skF_9' | k1_xboole_0=D_2664 | k1_xboole_0=C_2666 | k1_xboole_0=B_2665 | k1_xboole_0=A_2667 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_2667, B_2665, C_2666, D_2664)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_2668)), inference(superposition, [status(thm), theory('equality')], [c_728, c_10])).
% 4.20/1.75  tff(c_1002, plain, (![C_2666, E_194, B_2665, A_2667, D_2664]: (k11_mcart_1(A_2667, B_2665, C_2666, D_2664, '#skF_10')='#skF_9' | k1_xboole_0=D_2664 | k1_xboole_0=C_2666 | k1_xboole_0=B_2665 | k1_xboole_0=A_2667 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_2667, B_2665, C_2666, D_2664)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(superposition, [status(thm), theory('equality')], [c_632, c_993])).
% 4.20/1.75  tff(c_1028, plain, (![E_194]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(splitLeft, [status(thm)], [c_1002])).
% 4.20/1.75  tff(c_2144, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_5'), inference(factorization, [status(thm), theory('equality')], [c_1028])).
% 4.20/1.75  tff(c_1049, plain, (![E_194]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(factorization, [status(thm), theory('equality')], [c_1028])).
% 4.20/1.75  tff(c_2701, plain, (![E_11321]: (E_11321='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2144, c_1049])).
% 4.20/1.75  tff(c_2939, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2701, c_38])).
% 4.20/1.75  tff(c_2941, plain, (![A_12672, B_12673, C_12674, D_12675]: (k11_mcart_1(A_12672, B_12673, C_12674, D_12675, '#skF_10')='#skF_9' | k1_xboole_0=D_12675 | k1_xboole_0=C_12674 | k1_xboole_0=B_12673 | k1_xboole_0=A_12672 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_12672, B_12673, C_12674, D_12675)))), inference(splitRight, [status(thm)], [c_1002])).
% 4.20/1.75  tff(c_2945, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_2941])).
% 4.20/1.75  tff(c_2947, plain, (k2_mcart_1('#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_50, c_2945])).
% 4.20/1.75  tff(c_2949, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_51, c_2947])).
% 4.20/1.75  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.20/1.75  
% 4.20/1.75  Inference rules
% 4.20/1.75  ----------------------
% 4.20/1.75  #Ref     : 0
% 4.20/1.75  #Sup     : 343
% 4.20/1.75  #Fact    : 4
% 4.20/1.75  #Define  : 0
% 4.20/1.75  #Split   : 9
% 4.20/1.75  #Chain   : 0
% 4.20/1.75  #Close   : 0
% 4.20/1.75  
% 4.20/1.75  Ordering : KBO
% 4.20/1.75  
% 4.20/1.75  Simplification rules
% 4.20/1.75  ----------------------
% 4.20/1.75  #Subsume      : 61
% 4.20/1.75  #Demod        : 81
% 4.20/1.75  #Tautology    : 78
% 4.20/1.75  #SimpNegUnit  : 33
% 4.20/1.75  #BackRed      : 1
% 4.20/1.75  
% 4.20/1.75  #Partial instantiations: 3519
% 4.20/1.75  #Strategies tried      : 1
% 4.20/1.75  
% 4.20/1.75  Timing (in seconds)
% 4.20/1.75  ----------------------
% 4.20/1.75  Preprocessing        : 0.34
% 4.20/1.75  Parsing              : 0.17
% 4.20/1.75  CNF conversion       : 0.03
% 4.20/1.75  Main loop            : 0.63
% 4.20/1.75  Inferencing          : 0.32
% 4.20/1.75  Reduction            : 0.13
% 4.20/1.75  Demodulation         : 0.09
% 4.20/1.75  BG Simplification    : 0.04
% 4.20/1.75  Subsumption          : 0.10
% 4.20/1.75  Abstraction          : 0.05
% 4.20/1.75  MUC search           : 0.00
% 4.20/1.75  Cooper               : 0.00
% 4.20/1.75  Total                : 1.00
% 4.20/1.75  Index Insertion      : 0.00
% 4.20/1.75  Index Deletion       : 0.00
% 4.20/1.75  Index Matching       : 0.00
% 4.20/1.75  BG Taut test         : 0.00
%------------------------------------------------------------------------------
