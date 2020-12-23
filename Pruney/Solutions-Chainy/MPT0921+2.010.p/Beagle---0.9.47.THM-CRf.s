%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:19 EST 2020

% Result     : Theorem 2.74s
% Output     : CNFRefutation 2.74s
% Verified   : 
% Statistics : Number of formulae       :   59 ( 177 expanded)
%              Number of leaves         :   28 (  86 expanded)
%              Depth                    :   18
%              Number of atoms          :  186 (1024 expanded)
%              Number of equality atoms :  130 ( 634 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i ) > $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

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
                           => E = I ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k10_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l68_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

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

tff(c_30,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_42,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

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

tff(c_183,plain,(
    ! [D_196,E_200,C_198,B_197,A_199] :
      ( k4_mcart_1('#skF_1'(D_196,B_197,C_198,A_199,E_200),'#skF_2'(D_196,B_197,C_198,A_199,E_200),'#skF_3'(D_196,B_197,C_198,A_199,E_200),'#skF_4'(D_196,B_197,C_198,A_199,E_200)) = E_200
      | ~ m1_subset_1(E_200,k4_zfmisc_1(A_199,B_197,C_198,D_196))
      | k1_xboole_0 = D_196
      | k1_xboole_0 = C_198
      | k1_xboole_0 = B_197
      | k1_xboole_0 = A_199 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [I_113,G_101,H_109,J_115] :
      ( I_113 = '#skF_9'
      | k4_mcart_1(G_101,H_109,I_113,J_115) != '#skF_10'
      | ~ m1_subset_1(J_115,'#skF_8')
      | ~ m1_subset_1(I_113,'#skF_7')
      | ~ m1_subset_1(H_109,'#skF_6')
      | ~ m1_subset_1(G_101,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_139])).

tff(c_207,plain,(
    ! [C_204,A_205,E_203,D_202,B_201] :
      ( '#skF_3'(D_202,B_201,C_204,A_205,E_203) = '#skF_9'
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
    inference(superposition,[status(thm),theory(equality)],[c_183,c_40])).

tff(c_211,plain,(
    ! [D_8,C_7,A_5,E_40] :
      ( '#skF_3'(D_8,'#skF_6',C_7,A_5,E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_8,'#skF_6',C_7,A_5,E_40),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_8,'#skF_6',C_7,A_5,E_40),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_8,'#skF_6',C_7,A_5,E_40),'#skF_5')
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,'#skF_6',C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_10,c_207])).

tff(c_216,plain,(
    ! [D_206,C_207,A_208,E_209] :
      ( '#skF_3'(D_206,'#skF_6',C_207,A_208,E_209) = '#skF_9'
      | E_209 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(D_206,'#skF_6',C_207,A_208,E_209),'#skF_8')
      | ~ m1_subset_1('#skF_3'(D_206,'#skF_6',C_207,A_208,E_209),'#skF_7')
      | ~ m1_subset_1('#skF_1'(D_206,'#skF_6',C_207,A_208,E_209),'#skF_5')
      | ~ m1_subset_1(E_209,k4_zfmisc_1(A_208,'#skF_6',C_207,D_206))
      | k1_xboole_0 = D_206
      | k1_xboole_0 = C_207
      | k1_xboole_0 = A_208 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_211])).

tff(c_220,plain,(
    ! [C_7,A_5,E_40] :
      ( '#skF_3'('#skF_8','#skF_6',C_7,A_5,E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6',C_7,A_5,E_40),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6',C_7,A_5,E_40),'#skF_5')
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,'#skF_6',C_7,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_7
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_6,c_216])).

tff(c_225,plain,(
    ! [C_210,A_211,E_212] :
      ( '#skF_3'('#skF_8','#skF_6',C_210,A_211,E_212) = '#skF_9'
      | E_212 != '#skF_10'
      | ~ m1_subset_1('#skF_3'('#skF_8','#skF_6',C_210,A_211,E_212),'#skF_7')
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6',C_210,A_211,E_212),'#skF_5')
      | ~ m1_subset_1(E_212,k4_zfmisc_1(A_211,'#skF_6',C_210,'#skF_8'))
      | k1_xboole_0 = C_210
      | k1_xboole_0 = A_211 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_32,c_32,c_220])).

tff(c_229,plain,(
    ! [A_5,E_40] :
      ( '#skF_3'('#skF_8','#skF_6','#skF_7',A_5,E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7',A_5,E_40),'#skF_5')
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_5 ) ),
    inference(resolution,[status(thm)],[c_8,c_225])).

tff(c_234,plain,(
    ! [A_213,E_214] :
      ( '#skF_3'('#skF_8','#skF_6','#skF_7',A_213,E_214) = '#skF_9'
      | E_214 != '#skF_10'
      | ~ m1_subset_1('#skF_1'('#skF_8','#skF_6','#skF_7',A_213,E_214),'#skF_5')
      | ~ m1_subset_1(E_214,k4_zfmisc_1(A_213,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_213 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_32,c_34,c_229])).

tff(c_238,plain,(
    ! [E_40] :
      ( '#skF_3'('#skF_8','#skF_6','#skF_7','#skF_5',E_40) = '#skF_9'
      | E_40 != '#skF_10'
      | ~ m1_subset_1(E_40,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_12,c_234])).

tff(c_243,plain,(
    ! [E_215] :
      ( '#skF_3'('#skF_8','#skF_6','#skF_7','#skF_5',E_215) = '#skF_9'
      | E_215 != '#skF_10'
      | ~ m1_subset_1(E_215,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_38,c_238])).

tff(c_267,plain,(
    '#skF_3'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_42,c_243])).

tff(c_4,plain,(
    ! [B_6,C_7,D_8,E_40,A_5] :
      ( k4_mcart_1('#skF_1'(D_8,B_6,C_7,A_5,E_40),'#skF_2'(D_8,B_6,C_7,A_5,E_40),'#skF_3'(D_8,B_6,C_7,A_5,E_40),'#skF_4'(D_8,B_6,C_7,A_5,E_40)) = E_40
      | ~ m1_subset_1(E_40,k4_zfmisc_1(A_5,B_6,C_7,D_8))
      | k1_xboole_0 = D_8
      | k1_xboole_0 = C_7
      | k1_xboole_0 = B_6
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_274,plain,
    ( k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_4])).

tff(c_285,plain,
    ( k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_274])).

tff(c_286,plain,(
    k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_285])).

tff(c_24,plain,(
    ! [G_83,C_75,B_74,H_84,I_85,F_82,A_73,D_76] :
      ( k10_mcart_1(A_73,B_74,C_75,D_76,k4_mcart_1(F_82,G_83,H_84,I_85)) = H_84
      | k1_xboole_0 = D_76
      | k1_xboole_0 = C_75
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_73
      | ~ m1_subset_1(k4_mcart_1(F_82,G_83,H_84,I_85),k4_zfmisc_1(A_73,B_74,C_75,D_76)) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_303,plain,(
    ! [A_73,B_74,C_75,D_76] :
      ( k10_mcart_1(A_73,B_74,C_75,D_76,k4_mcart_1('#skF_1'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_2'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_8','#skF_6','#skF_7','#skF_5','#skF_10'))) = '#skF_9'
      | k1_xboole_0 = D_76
      | k1_xboole_0 = C_75
      | k1_xboole_0 = B_74
      | k1_xboole_0 = A_73
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_73,B_74,C_75,D_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_24])).

tff(c_317,plain,(
    ! [A_216,B_217,C_218,D_219] :
      ( k10_mcart_1(A_216,B_217,C_218,D_219,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_219
      | k1_xboole_0 = C_218
      | k1_xboole_0 = B_217
      | k1_xboole_0 = A_216
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_216,B_217,C_218,D_219)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_286,c_303])).

tff(c_320,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_317])).

tff(c_324,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_30,c_320])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.05/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.05/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n021.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 16:57:49 EST 2020
% 0.11/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.74/1.40  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.40  
% 2.74/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.41  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_mcart_1 > k4_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.74/1.41  
% 2.74/1.41  %Foreground sorts:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Background operators:
% 2.74/1.41  
% 2.74/1.41  
% 2.74/1.41  %Foreground operators:
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.74/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.74/1.41  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.74/1.41  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.74/1.41  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_7', type, '#skF_7': $i).
% 2.74/1.41  tff('#skF_10', type, '#skF_10': $i).
% 2.74/1.41  tff('#skF_5', type, '#skF_5': $i).
% 2.74/1.41  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_6', type, '#skF_6': $i).
% 2.74/1.41  tff('#skF_9', type, '#skF_9': $i).
% 2.74/1.41  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#skF_8', type, '#skF_8': $i).
% 2.74/1.41  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.74/1.41  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.74/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.74/1.41  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.74/1.41  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.74/1.41  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.74/1.41  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.74/1.41  
% 2.74/1.42  tff(f_139, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 2.74/1.42  tff(f_58, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l68_mcart_1)).
% 2.74/1.42  tff(f_110, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 2.74/1.42  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.74/1.42  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.74/1.42  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.74/1.42  tff(c_32, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.74/1.42  tff(c_30, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.74/1.42  tff(c_42, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.74/1.42  tff(c_12, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_1'(D_8, B_6, C_7, A_5, E_40), A_5) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.42  tff(c_8, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_3'(D_8, B_6, C_7, A_5, E_40), C_7) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.42  tff(c_6, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_4'(D_8, B_6, C_7, A_5, E_40), D_8) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.42  tff(c_10, plain, (![B_6, C_7, D_8, E_40, A_5]: (m1_subset_1('#skF_2'(D_8, B_6, C_7, A_5, E_40), B_6) | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.42  tff(c_183, plain, (![D_196, E_200, C_198, B_197, A_199]: (k4_mcart_1('#skF_1'(D_196, B_197, C_198, A_199, E_200), '#skF_2'(D_196, B_197, C_198, A_199, E_200), '#skF_3'(D_196, B_197, C_198, A_199, E_200), '#skF_4'(D_196, B_197, C_198, A_199, E_200))=E_200 | ~m1_subset_1(E_200, k4_zfmisc_1(A_199, B_197, C_198, D_196)) | k1_xboole_0=D_196 | k1_xboole_0=C_198 | k1_xboole_0=B_197 | k1_xboole_0=A_199)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.42  tff(c_40, plain, (![I_113, G_101, H_109, J_115]: (I_113='#skF_9' | k4_mcart_1(G_101, H_109, I_113, J_115)!='#skF_10' | ~m1_subset_1(J_115, '#skF_8') | ~m1_subset_1(I_113, '#skF_7') | ~m1_subset_1(H_109, '#skF_6') | ~m1_subset_1(G_101, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_139])).
% 2.74/1.42  tff(c_207, plain, (![C_204, A_205, E_203, D_202, B_201]: ('#skF_3'(D_202, B_201, C_204, A_205, E_203)='#skF_9' | E_203!='#skF_10' | ~m1_subset_1('#skF_4'(D_202, B_201, C_204, A_205, E_203), '#skF_8') | ~m1_subset_1('#skF_3'(D_202, B_201, C_204, A_205, E_203), '#skF_7') | ~m1_subset_1('#skF_2'(D_202, B_201, C_204, A_205, E_203), '#skF_6') | ~m1_subset_1('#skF_1'(D_202, B_201, C_204, A_205, E_203), '#skF_5') | ~m1_subset_1(E_203, k4_zfmisc_1(A_205, B_201, C_204, D_202)) | k1_xboole_0=D_202 | k1_xboole_0=C_204 | k1_xboole_0=B_201 | k1_xboole_0=A_205)), inference(superposition, [status(thm), theory('equality')], [c_183, c_40])).
% 2.74/1.42  tff(c_211, plain, (![D_8, C_7, A_5, E_40]: ('#skF_3'(D_8, '#skF_6', C_7, A_5, E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1('#skF_4'(D_8, '#skF_6', C_7, A_5, E_40), '#skF_8') | ~m1_subset_1('#skF_3'(D_8, '#skF_6', C_7, A_5, E_40), '#skF_7') | ~m1_subset_1('#skF_1'(D_8, '#skF_6', C_7, A_5, E_40), '#skF_5') | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, '#skF_6', C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0='#skF_6' | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_10, c_207])).
% 2.74/1.42  tff(c_216, plain, (![D_206, C_207, A_208, E_209]: ('#skF_3'(D_206, '#skF_6', C_207, A_208, E_209)='#skF_9' | E_209!='#skF_10' | ~m1_subset_1('#skF_4'(D_206, '#skF_6', C_207, A_208, E_209), '#skF_8') | ~m1_subset_1('#skF_3'(D_206, '#skF_6', C_207, A_208, E_209), '#skF_7') | ~m1_subset_1('#skF_1'(D_206, '#skF_6', C_207, A_208, E_209), '#skF_5') | ~m1_subset_1(E_209, k4_zfmisc_1(A_208, '#skF_6', C_207, D_206)) | k1_xboole_0=D_206 | k1_xboole_0=C_207 | k1_xboole_0=A_208)), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_211])).
% 2.74/1.42  tff(c_220, plain, (![C_7, A_5, E_40]: ('#skF_3'('#skF_8', '#skF_6', C_7, A_5, E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', C_7, A_5, E_40), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', C_7, A_5, E_40), '#skF_5') | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, '#skF_6', C_7, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_7 | k1_xboole_0='#skF_6' | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_6, c_216])).
% 2.74/1.42  tff(c_225, plain, (![C_210, A_211, E_212]: ('#skF_3'('#skF_8', '#skF_6', C_210, A_211, E_212)='#skF_9' | E_212!='#skF_10' | ~m1_subset_1('#skF_3'('#skF_8', '#skF_6', C_210, A_211, E_212), '#skF_7') | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', C_210, A_211, E_212), '#skF_5') | ~m1_subset_1(E_212, k4_zfmisc_1(A_211, '#skF_6', C_210, '#skF_8')) | k1_xboole_0=C_210 | k1_xboole_0=A_211)), inference(negUnitSimplification, [status(thm)], [c_36, c_32, c_32, c_220])).
% 2.74/1.42  tff(c_229, plain, (![A_5, E_40]: ('#skF_3'('#skF_8', '#skF_6', '#skF_7', A_5, E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', A_5, E_40), '#skF_5') | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_5)), inference(resolution, [status(thm)], [c_8, c_225])).
% 2.74/1.42  tff(c_234, plain, (![A_213, E_214]: ('#skF_3'('#skF_8', '#skF_6', '#skF_7', A_213, E_214)='#skF_9' | E_214!='#skF_10' | ~m1_subset_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', A_213, E_214), '#skF_5') | ~m1_subset_1(E_214, k4_zfmisc_1(A_213, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_213)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_32, c_34, c_229])).
% 2.74/1.42  tff(c_238, plain, (![E_40]: ('#skF_3'('#skF_8', '#skF_6', '#skF_7', '#skF_5', E_40)='#skF_9' | E_40!='#skF_10' | ~m1_subset_1(E_40, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_12, c_234])).
% 2.74/1.42  tff(c_243, plain, (![E_215]: ('#skF_3'('#skF_8', '#skF_6', '#skF_7', '#skF_5', E_215)='#skF_9' | E_215!='#skF_10' | ~m1_subset_1(E_215, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_38, c_238])).
% 2.74/1.42  tff(c_267, plain, ('#skF_3'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10')='#skF_9'), inference(resolution, [status(thm)], [c_42, c_243])).
% 2.74/1.42  tff(c_4, plain, (![B_6, C_7, D_8, E_40, A_5]: (k4_mcart_1('#skF_1'(D_8, B_6, C_7, A_5, E_40), '#skF_2'(D_8, B_6, C_7, A_5, E_40), '#skF_3'(D_8, B_6, C_7, A_5, E_40), '#skF_4'(D_8, B_6, C_7, A_5, E_40))=E_40 | ~m1_subset_1(E_40, k4_zfmisc_1(A_5, B_6, C_7, D_8)) | k1_xboole_0=D_8 | k1_xboole_0=C_7 | k1_xboole_0=B_6 | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.74/1.42  tff(c_274, plain, (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_267, c_4])).
% 2.74/1.42  tff(c_285, plain, (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_274])).
% 2.74/1.42  tff(c_286, plain, (k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_285])).
% 2.74/1.42  tff(c_24, plain, (![G_83, C_75, B_74, H_84, I_85, F_82, A_73, D_76]: (k10_mcart_1(A_73, B_74, C_75, D_76, k4_mcart_1(F_82, G_83, H_84, I_85))=H_84 | k1_xboole_0=D_76 | k1_xboole_0=C_75 | k1_xboole_0=B_74 | k1_xboole_0=A_73 | ~m1_subset_1(k4_mcart_1(F_82, G_83, H_84, I_85), k4_zfmisc_1(A_73, B_74, C_75, D_76)))), inference(cnfTransformation, [status(thm)], [f_110])).
% 2.74/1.42  tff(c_303, plain, (![A_73, B_74, C_75, D_76]: (k10_mcart_1(A_73, B_74, C_75, D_76, k4_mcart_1('#skF_1'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_2'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_8', '#skF_6', '#skF_7', '#skF_5', '#skF_10')))='#skF_9' | k1_xboole_0=D_76 | k1_xboole_0=C_75 | k1_xboole_0=B_74 | k1_xboole_0=A_73 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_73, B_74, C_75, D_76)))), inference(superposition, [status(thm), theory('equality')], [c_286, c_24])).
% 2.74/1.42  tff(c_317, plain, (![A_216, B_217, C_218, D_219]: (k10_mcart_1(A_216, B_217, C_218, D_219, '#skF_10')='#skF_9' | k1_xboole_0=D_219 | k1_xboole_0=C_218 | k1_xboole_0=B_217 | k1_xboole_0=A_216 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_216, B_217, C_218, D_219)))), inference(demodulation, [status(thm), theory('equality')], [c_286, c_303])).
% 2.74/1.42  tff(c_320, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_317])).
% 2.74/1.42  tff(c_324, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_30, c_320])).
% 2.74/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.74/1.42  
% 2.74/1.42  Inference rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Ref     : 0
% 2.74/1.42  #Sup     : 59
% 2.74/1.42  #Fact    : 0
% 2.74/1.42  #Define  : 0
% 2.74/1.42  #Split   : 0
% 2.74/1.42  #Chain   : 0
% 2.74/1.42  #Close   : 0
% 2.74/1.42  
% 2.74/1.42  Ordering : KBO
% 2.74/1.42  
% 2.74/1.42  Simplification rules
% 2.74/1.42  ----------------------
% 2.74/1.42  #Subsume      : 0
% 2.74/1.42  #Demod        : 9
% 2.74/1.42  #Tautology    : 18
% 2.74/1.42  #SimpNegUnit  : 12
% 2.74/1.42  #BackRed      : 0
% 2.74/1.42  
% 2.74/1.42  #Partial instantiations: 0
% 2.74/1.42  #Strategies tried      : 1
% 2.74/1.42  
% 2.74/1.42  Timing (in seconds)
% 2.74/1.42  ----------------------
% 2.74/1.42  Preprocessing        : 0.37
% 2.74/1.42  Parsing              : 0.19
% 2.74/1.42  CNF conversion       : 0.03
% 2.74/1.42  Main loop            : 0.26
% 2.74/1.42  Inferencing          : 0.10
% 2.74/1.42  Reduction            : 0.07
% 2.74/1.42  Demodulation         : 0.04
% 2.74/1.43  BG Simplification    : 0.03
% 2.74/1.43  Subsumption          : 0.05
% 2.74/1.43  Abstraction          : 0.03
% 2.74/1.43  MUC search           : 0.00
% 2.74/1.43  Cooper               : 0.00
% 2.74/1.43  Total                : 0.66
% 2.74/1.43  Index Insertion      : 0.00
% 2.74/1.43  Index Deletion       : 0.00
% 2.74/1.43  Index Matching       : 0.00
% 2.74/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------
