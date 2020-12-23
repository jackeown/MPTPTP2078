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
% DateTime   : Thu Dec  3 10:10:20 EST 2020

% Result     : Theorem 2.86s
% Output     : CNFRefutation 2.86s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 207 expanded)
%              Number of leaves         :   29 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :  213 (1202 expanded)
%              Number of equality atoms :  155 ( 756 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k8_mcart_1,type,(
    k8_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_139,negated_conjecture,(
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

tff(f_83,axiom,(
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

tff(f_58,axiom,(
    ! [A,B,C,D] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & ? [E] :
            ( m1_subset_1(E,k4_zfmisc_1(A,B,C,D))
            & ! [F] :
                ( m1_subset_1(F,A)
               => ! [G] :
                    ( m1_subset_1(G,B)
                   => ! [H] :
                        ( m1_subset_1(H,C)
                       => ! [I] :
                            ( m1_subset_1(I,D)
                           => E != k4_mcart_1(F,G,H,I) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l68_mcart_1)).

tff(f_110,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_55,plain,(
    ! [C_137,D_138,E_136,B_134,A_135] :
      ( k11_mcart_1(A_135,B_134,C_137,D_138,E_136) = k2_mcart_1(E_136)
      | ~ m1_subset_1(E_136,k4_zfmisc_1(A_135,B_134,C_137,D_138))
      | k1_xboole_0 = D_138
      | k1_xboole_0 = C_137
      | k1_xboole_0 = B_134
      | k1_xboole_0 = A_135 ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_66,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_55])).

tff(c_71,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_66])).

tff(c_30,plain,(
    k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_72,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_30])).

tff(c_12,plain,(
    ! [B_6,C_7,D_8,E_40,A_5] :
      ( m1_subset_1('#skF_1'(D_8,B_6,C_7,A_5,E_40),A_5)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,B_6,C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = B_6
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_8,plain,(
    ! [B_6,C_7,D_8,E_40,A_5] :
      ( m1_subset_1('#skF_3'(D_8,B_6,C_7,A_5,E_40),C_7)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,B_6,C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = B_6
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_6,plain,(
    ! [B_6,C_7,D_8,E_40,A_5] :
      ( m1_subset_1('#skF_4'(D_8,B_6,C_7,A_5,E_40),D_8)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,B_6,C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = B_6
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [B_6,C_7,D_8,E_40,A_5] :
      ( m1_subset_1('#skF_2'(D_8,B_6,C_7,A_5,E_40),B_6)
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,B_6,C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = B_6
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_184,plain,(
    ! [D_196,E_200,C_198,B_197,A_199] :
      ( k4_mcart_1('#skF_1'(D_196,B_197,C_198,A_199,E_200),'#skF_2'(D_196,B_197,C_198,A_199,E_200),'#skF_3'(D_196,B_197,C_198,A_199,E_200),'#skF_4'(D_196,B_197,C_198,A_199,E_200)) = E_200
      | ~ m1_subset_1(E_200,k4_zfmisc_1(A_199,B_197,C_198,D_196))
      | k1_xboole_0 = D_196
      | k1_xboole_0 = C_198
      | k1_xboole_0 = B_197
      | k1_xboole_0 = A_199 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [J_115,G_101,H_109,I_113] :
      ( J_115 = '#skF_9'
      | k4_mcart_1(G_101,H_109,I_113,J_115) != '#skF_10'
      | ~ m1_subset_1(J_115,'#skF_8')
      | ~ m1_subset_1(I_113,'#skF_7')
      | ~ m1_subset_1(H_109,'#skF_6')
      | ~ m1_subset_1(G_101,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_208,plain,(
    ! [C_204,A_205,E_203,D_202,B_201] :
      ( '#skF_4'(D_202,B_201,C_204,A_205,E_203) = '#skF_9'
      | E_203 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_202,B_201,C_204,A_205,E_203),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_202,B_201,C_204,A_205,E_203),'#skF_7')
      | ~ m1_subset_1('#skF_2'(D_202,B_201,C_204,A_205,E_203),'#skF_6')
      | ~ m1_subset_1('#skF_1'(D_202,B_201,C_204,A_205,E_203),'#skF_5')
      | ~ m1_subset_1(E_203,k4_zfmisc_1(A_205,B_201,C_204,D_202))
      | k1_xboole_0 = D_202
      | k1_xboole_0 = C_204
      | k1_xboole_0 = B_201
      | k1_xboole_0 = A_205 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_40])).

tff(c_212,plain,(
    ! [D_8,C_7,A_5,E_40] :
      ( '#skF_4'(D_8,'#skF_6',C_7,A_5,E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_8,'#skF_6',C_7,A_5,E_40),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_8,'#skF_6',C_7,A_5,E_40),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_8,'#skF_6',C_7,A_5,E_40),'#skF_5')
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,'#skF_6',C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_10,c_208])).

tff(c_217,plain,(
    ! [D_206,C_207,A_208,E_209] :
      ( '#skF_4'(D_206,'#skF_6',C_207,A_208,E_209) = '#skF_9'
      | E_209 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_206,'#skF_6',C_207,A_208,E_209),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_206,'#skF_6',C_207,A_208,E_209),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_206,'#skF_6',C_207,A_208,E_209),'#skF_5')
      | ~ m1_subset_1(E_209,k4_zfmisc_1(A_208,'#skF_6',C_207,D_206))
      | k1_xboole_0 = D_206
      | k1_xboole_0 = C_207
      | k1_xboole_0 = A_208 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_212])).

tff(c_221,plain,(
    ! [C_7,A_5,E_40] :
      ( '#skF_4'('#skF_8','#skF_6',C_7,A_5,E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6',C_7,A_5,E_40),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6',C_7,A_5,E_40),'#skF_5')
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,'#skF_6',C_7,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_7
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_6,c_217])).

tff(c_226,plain,(
    ! [C_210,A_211,E_212] :
      ( '#skF_4'('#skF_8','#skF_6',C_210,A_211,E_212) = '#skF_9'
      | E_212 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6',C_210,A_211,E_212),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6',C_210,A_211,E_212),'#skF_5')
      | ~ m1_subset_1(E_212,k4_zfmisc_1(A_211,'#skF_6',C_210,'#skF_8'))
      | k1_xboole_0 = C_210
      | k1_xboole_0 = A_211 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32,c_32,c_221])).

tff(c_230,plain,(
    ! [A_5,E_40] :
      ( '#skF_4'('#skF_8','#skF_6','#skF_7',A_5,E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7',A_5,E_40),'#skF_5')
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_8,c_226])).

tff(c_235,plain,(
    ! [A_213,E_214] :
      ( '#skF_4'('#skF_8','#skF_6','#skF_7',A_213,E_214) = '#skF_9'
      | E_214 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7',A_213,E_214),'#skF_5')
      | ~ m1_subset_1(E_214,k4_zfmisc_1(A_213,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_213 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_34,c_230])).

tff(c_239,plain,(
    ! [E_40] :
      ( '#skF_4'('#skF_8','#skF_6','#skF_7','#skF_5',E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1(E_40,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_12,c_235])).

tff(c_244,plain,(
    ! [E_215] :
      ( '#skF_4'('#skF_8','#skF_6','#skF_7','#skF_5',E_215) = '#skF_9'
      | E_215 != '#skF_10'
      | ~ m1_subset_1(E_215,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_38,c_239])).

tff(c_268,plain,(
    '#skF_4'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_42,c_244])).

tff(c_4,plain,(
    ! [B_6,C_7,D_8,E_40,A_5] :
      ( k4_mcart_1('#skF_1'(D_8,B_6,C_7,A_5,E_40),'#skF_2'(D_8,B_6,C_7,A_5,E_40),'#skF_3'(D_8,B_6,C_7,A_5,E_40),'#skF_4'(D_8,B_6,C_7,A_5,E_40)) = E_40
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,B_6,C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = B_6
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_275,plain,
    ( k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_3'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9') = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_4])).

tff(c_286,plain,
    ( k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_3'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9') = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_275])).

tff(c_287,plain,(
    k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_3'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9') = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_286])).

tff(c_22,plain,(
    ! [G_83,C_75,B_74,H_84,I_85,F_82,A_73,D_76] :
      ( k11_mcart_1(A_73,B_74,C_75,D_76,k4_mcart_1(F_82,G_83,H_84,I_85)) = I_85
      | k1_xboole_0 = D_76
      | k1_xboole_0 = C_75
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_73
      | ~ m1_subset_1(k4_mcart_1(F_82,G_83,H_84,I_85),k4_zfmisc_1(A_73,B_74,C_75,D_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_295,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k11_mcart_1(A_73,B_74,C_75,D_76,k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_3'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9')) = '#skF_9'
      | k1_xboole_0 = D_76
      | k1_xboole_0 = C_75
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_73
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_73,B_74,C_75,D_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_22])).

tff(c_318,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k11_mcart_1(A_216,B_217,C_218,D_219,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_219
      | k1_xboole_0 = C_218
      | k1_xboole_0 = B_217
      | k1_xboole_0 = A_216
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_216,B_217,C_218,D_219)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_287,c_295])).

tff(c_321,plain,
    ( k11_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_318])).

tff(c_323,plain,
    ( k2_mcart_1('#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_71,c_321])).

tff(c_325,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_72,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 11:09:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.86/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  
% 2.86/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.40  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.86/1.40  
% 2.86/1.40  %Foreground sorts:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Background operators:
% 2.86/1.40  
% 2.86/1.40  
% 2.86/1.40  %Foreground operators:
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.86/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.86/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.86/1.40  tff('#skF_10', type, '#skF_10': $i).
% 2.86/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.86/1.40  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.86/1.40  tff('#skF_9', type, '#skF_9': $i).
% 2.86/1.40  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.86/1.40  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.86/1.40  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.86/1.40  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.86/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.86/1.40  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.86/1.40  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.86/1.40  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.86/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.86/1.40  
% 2.86/1.42  tff(f_139, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = J)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k11_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t82_mcart_1)).
% 2.86/1.42  tff(f_83, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & ~(![E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ((((k8_mcart_1(A, B, C, D, E) = k1_mcart_1(k1_mcart_1(k1_mcart_1(E)))) & (k9_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(k1_mcart_1(E))))) & (k10_mcart_1(A, B, C, D, E) = k2_mcart_1(k1_mcart_1(E)))) & (k11_mcart_1(A, B, C, D, E) = k2_mcart_1(E))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_mcart_1)).
% 2.86/1.42  tff(f_58, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 2.86/1.42  tff(f_110, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 2.86/1.42  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.42  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.42  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.42  tff(c_32, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.42  tff(c_42, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.42  tff(c_55, plain, (![C_137, D_138, E_136, B_134, A_135]: (k11_mcart_1(A_135, B_134, C_137, D_138, E_136)=k2_mcart_1(E_136) | ~m1_subset_1(E_136, k4_zfmisc_1(A_135, B_134, C_137, D_138)) | k1_xboole_0=D_138 | k1_xboole_0=C_137 | k1_xboole_0=B_134 | k1_xboole_0=A_135)), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.86/1.42  tff(c_66, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_55])).
% 2.86/1.42  tff(c_71, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_66])).
% 2.86/1.42  tff(c_30, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.42  tff(c_72, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_30])).
% 2.86/1.42  tff(c_12, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_1'(D_8, B_6, C_7, A_5, E_40), A_5) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.42  tff(c_8, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_3'(D_8, B_6, C_7, A_5, E_40), C_7) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.42  tff(c_6, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_4'(D_8, B_6, C_7, A_5, E_40), D_8) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.42  tff(c_10, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_2'(D_8, B_6, C_7, A_5, E_40), B_6) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.42  tff(c_184, plain, (![D_196, E_200, C_198, B_197, A_199]: (k4_mcart_1('#skF_1'(D_196, B_197, C_198, A_199, E_200), '#skF_2'(D_196, B_197, C_198, A_199, E_200), '#skF_3'(D_196, B_197, C_198, A_199, E_200), '#skF_4'(D_196, B_197, C_198, A_199, E_200))=E_200 | ~m1_subset_1(E_200, k4_zfmisc_1(A_199, B_197, C_198, D_196)) | k1_xboole_0=D_196 | k1_xboole_0=C_198 | k1_xboole_0=B_197 | k1_xboole_0=A_199)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.42  tff(c_40, plain, (![J_115, G_101, H_109, I_113]: (J_115='#skF_9' | k4_mcart_1(G_101, H_109, I_113, J_115)!='#skF_10' | ~m1_subset_1(J_115, '#skF_8') | ~m1_subset_1(I_113, '#skF_7') | ~m1_subset_1(H_109, '#skF_6') | ~m1_subset_1(G_101, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.86/1.42  tff(c_208, plain, (![C_204, A_205, E_203, D_202, B_201]: ('#skF_4'(D_202, B_201, C_204, A_205, E_203)='#skF_9' | E_203!='#skF_10' | ~m1_subset_1('#skF_4'(D_202, B_201, C_204, A_205, E_203), '#skF_8') | ~m1_subset_1('#skF_3'(D_202, B_201, C_204, A_205, E_203), '#skF_7') | ~m1_subset_1('#skF_2'(D_202, B_201, C_204, A_205, E_203), '#skF_6') | ~m1_subset_1('#skF_1'(D_202, B_201, C_204, A_205, E_203), '#skF_5') | ~m1_subset_1(E_203, k4_zfmisc_1(A_205, B_201, C_204, D_202)) | k1_xboole_0=D_202 | k1_xboole_0=C_204 | k1_xboole_0=B_201 | k1_xboole_0=A_205)), inference(superposition, [status(thm), theory('equality')], [c_184, c_40])).
% 2.86/1.42  tff(c_212, plain, (![D_8, C_7, A_5, E_40]: ('#skF_4'(D_8, '#skF_6', C_7, A_5, E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1('#skF_4'(D_8, '#skF_6', C_7, A_5, E_40), '#skF_8') | ~m1_subset_1('#skF_3'(D_8, '#skF_6', C_7, A_5, E_40), '#skF_7') | ~m1_subset_1('#skF_1'(D_8, '#skF_6', C_7, A_5, E_40), '#skF_5') | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, '#skF_6', C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0='#skF_6' | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_10, c_208])).
% 2.86/1.42  tff(c_217, plain, (![D_206, C_207, A_208, E_209]: ('#skF_4'(D_206, '#skF_6', C_207, A_208, E_209)='#skF_9' | E_209!='#skF_10' | ~m1_subset_1('#skF_4'(D_206, '#skF_6', C_207, A_208, E_209), '#skF_8') | ~m1_subset_1('#skF_3'(D_206, '#skF_6', C_207, A_208, E_209), '#skF_7') | ~m1_subset_1('#skF_1'(D_206, '#skF_6', C_207, A_208, E_209), '#skF_5') | ~m1_subset_1(E_209, k4_zfmisc_1(A_208, '#skF_6', C_207, D_206)) | k1_xboole_0=D_206 | k1_xboole_0=C_207 | k1_xboole_0=A_208)), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_212])).
% 2.86/1.42  tff(c_221, plain, (![C_7, A_5, E_40]: ('#skF_4'('#skF_8', '#skF_6', C_7, A_5, E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', C_7, A_5, E_40), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', C_7, A_5, E_40), '#skF_5') | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, '#skF_6', C_7, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_7 | k1_xboole_0='#skF_6' | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_6, c_217])).
% 2.86/1.42  tff(c_226, plain, (![C_210, A_211, E_212]: ('#skF_4'('#skF_8', '#skF_6', C_210, A_211, E_212)='#skF_9' | E_212!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', C_210, A_211, E_212), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', C_210, A_211, E_212), '#skF_5') | ~m1_subset_1(E_212, k4_zfmisc_1(A_211, '#skF_6', C_210, '#skF_8')) | k1_xboole_0=C_210 | k1_xboole_0=A_211)), inference(negUnitSimplification, [status(thm)], [c_36, c_32, c_32, c_221])).
% 2.86/1.42  tff(c_230, plain, (![A_5, E_40]: ('#skF_4'('#skF_8', '#skF_6', '#skF_7', A_5, E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', A_5, E_40), '#skF_5') | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_8, c_226])).
% 2.86/1.42  tff(c_235, plain, (![A_213, E_214]: ('#skF_4'('#skF_8', '#skF_6', '#skF_7', A_213, E_214)='#skF_9' | E_214!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', A_213, E_214), '#skF_5') | ~m1_subset_1(E_214, k4_zfmisc_1(A_213, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_213)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_34, c_230])).
% 2.86/1.42  tff(c_239, plain, (![E_40]: ('#skF_4'('#skF_8', '#skF_6', '#skF_7', '#skF_5', E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1(E_40, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_12, c_235])).
% 2.86/1.42  tff(c_244, plain, (![E_215]: ('#skF_4'('#skF_8', '#skF_6', '#skF_7', '#skF_5', E_215)='#skF_9' | E_215!='#skF_10' | ~m1_subset_1(E_215, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_38, c_239])).
% 2.86/1.42  tff(c_268, plain, ('#skF_4'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_42, c_244])).
% 2.86/1.42  tff(c_4, plain, (![B_6, C_7, D_8, E_40, A_5]: (k4_mcart_1('#skF_1'(D_8, B_6, C_7, A_5, E_40), '#skF_2'(D_8, B_6, C_7, A_5, E_40), '#skF_3'(D_8, B_6, C_7, A_5, E_40), '#skF_4'(D_8, B_6, C_7, A_5, E_40))=E_40 | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.86/1.42  tff(c_275, plain, (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_3'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9')='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_268, c_4])).
% 2.86/1.42  tff(c_286, plain, (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_3'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9')='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_275])).
% 2.86/1.42  tff(c_287, plain, (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_3'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9')='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_286])).
% 2.86/1.42  tff(c_22, plain, (![G_83, C_75, B_74, H_84, I_85, F_82, A_73, D_76]: (k11_mcart_1(A_73, B_74, C_75, D_76, k4_mcart_1(F_82, G_83, H_84, I_85))=I_85 | k1_xboole_0=D_76 | k1_xboole_0=C_75 | k1_xboole_0=B_74 | k1_xboole_0=A_73 | ~m1_subset_1(k4_mcart_1(F_82, G_83, H_84, I_85), k4_zfmisc_1(A_73, B_74, C_75, D_76)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.86/1.42  tff(c_295, plain, (![A_73, B_74, C_75, D_76]: (k11_mcart_1(A_73, B_74, C_75, D_76, k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_3'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9'))='#skF_9' | k1_xboole_0=D_76 | k1_xboole_0=C_75 | k1_xboole_0=B_74 | k1_xboole_0=A_73 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_73, B_74, C_75, D_76)))), inference(superposition, [status(thm), theory('equality')], [c_287, c_22])).
% 2.86/1.42  tff(c_318, plain, (![A_216, B_217, C_218, D_219]: (k11_mcart_1(A_216, B_217, C_218, D_219, '#skF_10')='#skF_9' | k1_xboole_0=D_219 | k1_xboole_0=C_218 | k1_xboole_0=B_217 | k1_xboole_0=A_216 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_216, B_217, C_218, D_219)))), inference(demodulation, [status(thm), theory('equality')], [c_287, c_295])).
% 2.86/1.42  tff(c_321, plain, (k11_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_318])).
% 2.86/1.42  tff(c_323, plain, (k2_mcart_1('#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_71, c_321])).
% 2.86/1.42  tff(c_325, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_72, c_323])).
% 2.86/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.86/1.42  
% 2.86/1.42  Inference rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Ref     : 0
% 2.86/1.42  #Sup     : 59
% 2.86/1.42  #Fact    : 0
% 2.86/1.42  #Define  : 0
% 2.86/1.42  #Split   : 0
% 2.86/1.42  #Chain   : 0
% 2.86/1.42  #Close   : 0
% 2.86/1.42  
% 2.86/1.42  Ordering : KBO
% 2.86/1.42  
% 2.86/1.42  Simplification rules
% 2.86/1.42  ----------------------
% 2.86/1.42  #Subsume      : 0
% 2.86/1.42  #Demod        : 11
% 2.86/1.42  #Tautology    : 18
% 2.86/1.42  #SimpNegUnit  : 12
% 2.86/1.42  #BackRed      : 1
% 2.86/1.42  
% 2.86/1.42  #Partial instantiations: 0
% 2.86/1.42  #Strategies tried      : 1
% 2.86/1.42  
% 2.86/1.42  Timing (in seconds)
% 2.86/1.42  ----------------------
% 2.86/1.42  Preprocessing        : 0.35
% 2.86/1.42  Parsing              : 0.17
% 2.86/1.42  CNF conversion       : 0.03
% 2.86/1.42  Main loop            : 0.29
% 2.86/1.42  Inferencing          : 0.12
% 2.86/1.42  Reduction            : 0.07
% 2.86/1.42  Demodulation         : 0.05
% 2.86/1.42  BG Simplification    : 0.03
% 2.86/1.42  Subsumption          : 0.05
% 2.86/1.42  Abstraction          : 0.03
% 2.86/1.42  MUC search           : 0.00
% 2.86/1.42  Cooper               : 0.00
% 2.86/1.42  Total                : 0.68
% 2.86/1.42  Index Insertion      : 0.00
% 2.86/1.42  Index Deletion       : 0.00
% 2.86/1.42  Index Matching       : 0.00
% 2.86/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
