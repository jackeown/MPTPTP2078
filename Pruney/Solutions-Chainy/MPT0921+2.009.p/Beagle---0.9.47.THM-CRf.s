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
% DateTime   : Thu Dec  3 10:10:19 EST 2020

% Result     : Theorem 4.71s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 464 expanded)
%              Number of leaves         :   30 ( 199 expanded)
%              Depth                    :   20
%              Number of atoms          :  225 (3132 expanded)
%              Number of equality atoms :  167 (2019 expanded)
%              Maximal formula depth    :   21 (   7 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k10_mcart_1,type,(
    k10_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_138,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t81_mcart_1)).

tff(f_109,axiom,(
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
                         => E = H ) ) ) ) )
       => ( A = k1_xboole_0
          | B = k1_xboole_0
          | C = k1_xboole_0
          | D = k1_xboole_0
          | E = k9_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_mcart_1)).

tff(f_81,axiom,(
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

tff(c_42,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_34,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_46,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_26,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1('#skF_4'(F_33,E_32,A_28,C_30,B_29,D_31),D_31)
      | k9_mcart_1(A_28,B_29,C_30,D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = C_30
      | k1_xboole_0 = B_29
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(F_33,k4_zfmisc_1(A_28,B_29,C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_28,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1('#skF_3'(F_33,E_32,A_28,C_30,B_29,D_31),C_30)
      | k9_mcart_1(A_28,B_29,C_30,D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = C_30
      | k1_xboole_0 = B_29
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(F_33,k4_zfmisc_1(A_28,B_29,C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_32,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1('#skF_1'(F_33,E_32,A_28,C_30,B_29,D_31),A_28)
      | k9_mcart_1(A_28,B_29,C_30,D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = C_30
      | k1_xboole_0 = B_29
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(F_33,k4_zfmisc_1(A_28,B_29,C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_30,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( m1_subset_1('#skF_2'(F_33,E_32,A_28,C_30,B_29,D_31),B_29)
      | k9_mcart_1(A_28,B_29,C_30,D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = C_30
      | k1_xboole_0 = B_29
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(F_33,k4_zfmisc_1(A_28,B_29,C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_198,plain,(
    ! [C_187,B_188,F_184,E_185,D_189,A_186] :
      ( k4_mcart_1('#skF_1'(F_184,E_185,A_186,C_187,B_188,D_189),'#skF_2'(F_184,E_185,A_186,C_187,B_188,D_189),'#skF_3'(F_184,E_185,A_186,C_187,B_188,D_189),'#skF_4'(F_184,E_185,A_186,C_187,B_188,D_189)) = F_184
      | k9_mcart_1(A_186,B_188,C_187,D_189,F_184) = E_185
      | k1_xboole_0 = D_189
      | k1_xboole_0 = C_187
      | k1_xboole_0 = B_188
      | k1_xboole_0 = A_186
      | ~ m1_subset_1(F_184,k4_zfmisc_1(A_186,B_188,C_187,D_189)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_44,plain,(
    ! [I_87,G_75,H_83,J_89] :
      ( I_87 = '#skF_9'
      | k4_mcart_1(G_75,H_83,I_87,J_89) != '#skF_10'
      | ~ m1_subset_1(J_89,'#skF_8')
      | ~ m1_subset_1(I_87,'#skF_7')
      | ~ m1_subset_1(H_83,'#skF_6')
      | ~ m1_subset_1(G_75,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_222,plain,(
    ! [A_195,C_193,B_192,E_194,D_190,F_191] :
      ( '#skF_3'(F_191,E_194,A_195,C_193,B_192,D_190) = '#skF_9'
      | F_191 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_191,E_194,A_195,C_193,B_192,D_190),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_191,E_194,A_195,C_193,B_192,D_190),'#skF_7')
      | ~ m1_subset_1('#skF_2'(F_191,E_194,A_195,C_193,B_192,D_190),'#skF_6')
      | ~ m1_subset_1('#skF_1'(F_191,E_194,A_195,C_193,B_192,D_190),'#skF_5')
      | k9_mcart_1(A_195,B_192,C_193,D_190,F_191) = E_194
      | k1_xboole_0 = D_190
      | k1_xboole_0 = C_193
      | k1_xboole_0 = B_192
      | k1_xboole_0 = A_195
      | ~ m1_subset_1(F_191,k4_zfmisc_1(A_195,B_192,C_193,D_190)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_198,c_44])).

tff(c_226,plain,(
    ! [C_30,E_32,D_31,F_33,A_28] :
      ( '#skF_3'(F_33,E_32,A_28,C_30,'#skF_6',D_31) = '#skF_9'
      | F_33 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_33,E_32,A_28,C_30,'#skF_6',D_31),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_33,E_32,A_28,C_30,'#skF_6',D_31),'#skF_7')
      | ~ m1_subset_1('#skF_1'(F_33,E_32,A_28,C_30,'#skF_6',D_31),'#skF_5')
      | k9_mcart_1(A_28,'#skF_6',C_30,D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = C_30
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(F_33,k4_zfmisc_1(A_28,'#skF_6',C_30,D_31)) ) ),
    inference(resolution,[status(thm)],[c_30,c_222])).

tff(c_231,plain,(
    ! [E_197,F_196,C_199,A_198,D_200] :
      ( '#skF_3'(F_196,E_197,A_198,C_199,'#skF_6',D_200) = '#skF_9'
      | F_196 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_196,E_197,A_198,C_199,'#skF_6',D_200),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_196,E_197,A_198,C_199,'#skF_6',D_200),'#skF_7')
      | ~ m1_subset_1('#skF_1'(F_196,E_197,A_198,C_199,'#skF_6',D_200),'#skF_5')
      | k9_mcart_1(A_198,'#skF_6',C_199,D_200,F_196) = E_197
      | k1_xboole_0 = D_200
      | k1_xboole_0 = C_199
      | k1_xboole_0 = A_198
      | ~ m1_subset_1(F_196,k4_zfmisc_1(A_198,'#skF_6',C_199,D_200)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_40,c_226])).

tff(c_235,plain,(
    ! [F_33,E_32,C_30,D_31] :
      ( '#skF_3'(F_33,E_32,'#skF_5',C_30,'#skF_6',D_31) = '#skF_9'
      | F_33 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_33,E_32,'#skF_5',C_30,'#skF_6',D_31),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_33,E_32,'#skF_5',C_30,'#skF_6',D_31),'#skF_7')
      | k9_mcart_1('#skF_5','#skF_6',C_30,D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = C_30
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_33,k4_zfmisc_1('#skF_5','#skF_6',C_30,D_31)) ) ),
    inference(resolution,[status(thm)],[c_32,c_231])).

tff(c_240,plain,(
    ! [F_201,E_202,C_203,D_204] :
      ( '#skF_3'(F_201,E_202,'#skF_5',C_203,'#skF_6',D_204) = '#skF_9'
      | F_201 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_201,E_202,'#skF_5',C_203,'#skF_6',D_204),'#skF_8')
      | ~ m1_subset_1('#skF_3'(F_201,E_202,'#skF_5',C_203,'#skF_6',D_204),'#skF_7')
      | k9_mcart_1('#skF_5','#skF_6',C_203,D_204,F_201) = E_202
      | k1_xboole_0 = D_204
      | k1_xboole_0 = C_203
      | ~ m1_subset_1(F_201,k4_zfmisc_1('#skF_5','#skF_6',C_203,D_204)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_42,c_235])).

tff(c_244,plain,(
    ! [F_33,E_32,D_31] :
      ( '#skF_3'(F_33,E_32,'#skF_5','#skF_7','#skF_6',D_31) = '#skF_9'
      | F_33 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_33,E_32,'#skF_5','#skF_7','#skF_6',D_31),'#skF_8')
      | k9_mcart_1('#skF_5','#skF_6','#skF_7',D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_33,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_31)) ) ),
    inference(resolution,[status(thm)],[c_28,c_240])).

tff(c_249,plain,(
    ! [F_205,E_206,D_207] :
      ( '#skF_3'(F_205,E_206,'#skF_5','#skF_7','#skF_6',D_207) = '#skF_9'
      | F_205 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(F_205,E_206,'#skF_5','#skF_7','#skF_6',D_207),'#skF_8')
      | k9_mcart_1('#skF_5','#skF_6','#skF_7',D_207,F_205) = E_206
      | k1_xboole_0 = D_207
      | ~ m1_subset_1(F_205,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_207)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_38,c_244])).

tff(c_253,plain,(
    ! [F_33,E_32] :
      ( '#skF_3'(F_33,E_32,'#skF_5','#skF_7','#skF_6','#skF_8') = '#skF_9'
      | F_33 != '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_33) = E_32
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_33,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_26,c_249])).

tff(c_258,plain,(
    ! [F_208,E_209] :
      ( '#skF_3'(F_208,E_209,'#skF_5','#skF_7','#skF_6','#skF_8') = '#skF_9'
      | F_208 != '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_208) = E_209
      | ~ m1_subset_1(F_208,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_36,c_253])).

tff(c_280,plain,(
    ! [E_210] :
      ( '#skF_3'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8') = '#skF_9'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210 ) ),
    inference(resolution,[status(thm)],[c_46,c_258])).

tff(c_24,plain,(
    ! [C_30,E_32,D_31,B_29,F_33,A_28] :
      ( k4_mcart_1('#skF_1'(F_33,E_32,A_28,C_30,B_29,D_31),'#skF_2'(F_33,E_32,A_28,C_30,B_29,D_31),'#skF_3'(F_33,E_32,A_28,C_30,B_29,D_31),'#skF_4'(F_33,E_32,A_28,C_30,B_29,D_31)) = F_33
      | k9_mcart_1(A_28,B_29,C_30,D_31,F_33) = E_32
      | k1_xboole_0 = D_31
      | k1_xboole_0 = C_30
      | k1_xboole_0 = B_29
      | k1_xboole_0 = A_28
      | ~ m1_subset_1(F_33,k4_zfmisc_1(A_28,B_29,C_30,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_289,plain,(
    ! [E_210] :
      ( k4_mcart_1('#skF_1'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_2'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9','#skF_4'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8')) = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_24])).

tff(c_736,plain,(
    ! [E_210] :
      ( k4_mcart_1('#skF_1'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_2'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9','#skF_4'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8')) = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_289])).

tff(c_737,plain,(
    ! [E_210] :
      ( k4_mcart_1('#skF_1'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_2'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9','#skF_4'('#skF_10',E_210,'#skF_5','#skF_7','#skF_6','#skF_8')) = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_736])).

tff(c_813,plain,(
    ! [E_2663] :
      ( k4_mcart_1('#skF_1'('#skF_10',E_2663,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_2'('#skF_10',E_2663,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9','#skF_4'('#skF_10',E_2663,'#skF_5','#skF_7','#skF_6','#skF_8')) = '#skF_10'
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_2663 ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_736])).

tff(c_16,plain,(
    ! [B_16,A_15,D_18,H_26,I_27,F_24,C_17,G_25] :
      ( k10_mcart_1(A_15,B_16,C_17,D_18,k4_mcart_1(F_24,G_25,H_26,I_27)) = H_26
      | k1_xboole_0 = D_18
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15
      | ~ m1_subset_1(k4_mcart_1(F_24,G_25,H_26,I_27),k4_zfmisc_1(A_15,B_16,C_17,D_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1118,plain,(
    ! [B_3261,C_3258,E_3260,A_3262,D_3259] :
      ( k10_mcart_1(A_3262,B_3261,C_3258,D_3259,k4_mcart_1('#skF_1'('#skF_10',E_3260,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_2'('#skF_10',E_3260,'#skF_5','#skF_7','#skF_6','#skF_8'),'#skF_9','#skF_4'('#skF_10',E_3260,'#skF_5','#skF_7','#skF_6','#skF_8'))) = '#skF_9'
      | k1_xboole_0 = D_3259
      | k1_xboole_0 = C_3258
      | k1_xboole_0 = B_3261
      | k1_xboole_0 = A_3262
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_3262,B_3261,C_3258,D_3259))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_3260 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_813,c_16])).

tff(c_1127,plain,(
    ! [B_3261,C_3258,E_210,A_3262,D_3259] :
      ( k10_mcart_1(A_3262,B_3261,C_3258,D_3259,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_3259
      | k1_xboole_0 = C_3258
      | k1_xboole_0 = B_3261
      | k1_xboole_0 = A_3262
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_3262,B_3261,C_3258,D_3259))
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_737,c_1118])).

tff(c_1158,plain,(
    ! [E_210] :
      ( k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210
      | k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210 ) ),
    inference(splitLeft,[status(thm)],[c_1127])).

tff(c_2487,plain,(
    k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(factorization,[status(thm),theory(equality)],[c_1158])).

tff(c_1179,plain,(
    ! [E_210] : k9_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_210 ),
    inference(factorization,[status(thm),theory(equality)],[c_1158])).

tff(c_3111,plain,(
    ! [E_12426] : E_12426 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2487,c_1179])).

tff(c_3485,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3111,c_38])).

tff(c_3487,plain,(
    ! [A_15435,B_15436,C_15437,D_15438] :
      ( k10_mcart_1(A_15435,B_15436,C_15437,D_15438,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_15438
      | k1_xboole_0 = C_15437
      | k1_xboole_0 = B_15436
      | k1_xboole_0 = A_15435
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_15435,B_15436,C_15437,D_15438)) ) ),
    inference(splitRight,[status(thm)],[c_1127])).

tff(c_3491,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_46,c_3487])).

tff(c_3495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_36,c_34,c_3491])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n010.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:22:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.71/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.80  
% 4.71/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.71/1.80  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 4.71/1.80  
% 4.71/1.80  %Foreground sorts:
% 4.71/1.80  
% 4.71/1.80  
% 4.71/1.80  %Background operators:
% 4.71/1.80  
% 4.71/1.80  
% 4.71/1.80  %Foreground operators:
% 4.71/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.71/1.80  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.71/1.80  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.71/1.80  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.71/1.80  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.71/1.80  tff('#skF_7', type, '#skF_7': $i).
% 4.71/1.80  tff('#skF_10', type, '#skF_10': $i).
% 4.71/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.71/1.80  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.71/1.80  tff('#skF_9', type, '#skF_9': $i).
% 4.71/1.80  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.71/1.80  tff('#skF_8', type, '#skF_8': $i).
% 4.71/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.71/1.80  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.71/1.80  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.71/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.71/1.80  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.71/1.80  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.71/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 4.71/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.71/1.80  
% 4.86/1.82  tff(f_138, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t81_mcart_1)).
% 4.86/1.82  tff(f_109, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = H)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k9_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_mcart_1)).
% 4.86/1.82  tff(f_81, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 4.86/1.82  tff(c_42, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.86/1.82  tff(c_40, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.86/1.82  tff(c_38, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.86/1.82  tff(c_36, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.86/1.82  tff(c_34, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.86/1.82  tff(c_46, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.86/1.82  tff(c_26, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1('#skF_4'(F_33, E_32, A_28, C_30, B_29, D_31), D_31) | k9_mcart_1(A_28, B_29, C_30, D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0=C_30 | k1_xboole_0=B_29 | k1_xboole_0=A_28 | ~m1_subset_1(F_33, k4_zfmisc_1(A_28, B_29, C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.86/1.82  tff(c_28, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1('#skF_3'(F_33, E_32, A_28, C_30, B_29, D_31), C_30) | k9_mcart_1(A_28, B_29, C_30, D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0=C_30 | k1_xboole_0=B_29 | k1_xboole_0=A_28 | ~m1_subset_1(F_33, k4_zfmisc_1(A_28, B_29, C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.86/1.82  tff(c_32, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1('#skF_1'(F_33, E_32, A_28, C_30, B_29, D_31), A_28) | k9_mcart_1(A_28, B_29, C_30, D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0=C_30 | k1_xboole_0=B_29 | k1_xboole_0=A_28 | ~m1_subset_1(F_33, k4_zfmisc_1(A_28, B_29, C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.86/1.82  tff(c_30, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (m1_subset_1('#skF_2'(F_33, E_32, A_28, C_30, B_29, D_31), B_29) | k9_mcart_1(A_28, B_29, C_30, D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0=C_30 | k1_xboole_0=B_29 | k1_xboole_0=A_28 | ~m1_subset_1(F_33, k4_zfmisc_1(A_28, B_29, C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.86/1.82  tff(c_198, plain, (![C_187, B_188, F_184, E_185, D_189, A_186]: (k4_mcart_1('#skF_1'(F_184, E_185, A_186, C_187, B_188, D_189), '#skF_2'(F_184, E_185, A_186, C_187, B_188, D_189), '#skF_3'(F_184, E_185, A_186, C_187, B_188, D_189), '#skF_4'(F_184, E_185, A_186, C_187, B_188, D_189))=F_184 | k9_mcart_1(A_186, B_188, C_187, D_189, F_184)=E_185 | k1_xboole_0=D_189 | k1_xboole_0=C_187 | k1_xboole_0=B_188 | k1_xboole_0=A_186 | ~m1_subset_1(F_184, k4_zfmisc_1(A_186, B_188, C_187, D_189)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.86/1.82  tff(c_44, plain, (![I_87, G_75, H_83, J_89]: (I_87='#skF_9' | k4_mcart_1(G_75, H_83, I_87, J_89)!='#skF_10' | ~m1_subset_1(J_89, '#skF_8') | ~m1_subset_1(I_87, '#skF_7') | ~m1_subset_1(H_83, '#skF_6') | ~m1_subset_1(G_75, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_138])).
% 4.86/1.82  tff(c_222, plain, (![A_195, C_193, B_192, E_194, D_190, F_191]: ('#skF_3'(F_191, E_194, A_195, C_193, B_192, D_190)='#skF_9' | F_191!='#skF_10' | ~m1_subset_1('#skF_4'(F_191, E_194, A_195, C_193, B_192, D_190), '#skF_8') | ~m1_subset_1('#skF_3'(F_191, E_194, A_195, C_193, B_192, D_190), '#skF_7') | ~m1_subset_1('#skF_2'(F_191, E_194, A_195, C_193, B_192, D_190), '#skF_6') | ~m1_subset_1('#skF_1'(F_191, E_194, A_195, C_193, B_192, D_190), '#skF_5') | k9_mcart_1(A_195, B_192, C_193, D_190, F_191)=E_194 | k1_xboole_0=D_190 | k1_xboole_0=C_193 | k1_xboole_0=B_192 | k1_xboole_0=A_195 | ~m1_subset_1(F_191, k4_zfmisc_1(A_195, B_192, C_193, D_190)))), inference(superposition, [status(thm), theory('equality')], [c_198, c_44])).
% 4.86/1.82  tff(c_226, plain, (![C_30, E_32, D_31, F_33, A_28]: ('#skF_3'(F_33, E_32, A_28, C_30, '#skF_6', D_31)='#skF_9' | F_33!='#skF_10' | ~m1_subset_1('#skF_4'(F_33, E_32, A_28, C_30, '#skF_6', D_31), '#skF_8') | ~m1_subset_1('#skF_3'(F_33, E_32, A_28, C_30, '#skF_6', D_31), '#skF_7') | ~m1_subset_1('#skF_1'(F_33, E_32, A_28, C_30, '#skF_6', D_31), '#skF_5') | k9_mcart_1(A_28, '#skF_6', C_30, D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0=C_30 | k1_xboole_0='#skF_6' | k1_xboole_0=A_28 | ~m1_subset_1(F_33, k4_zfmisc_1(A_28, '#skF_6', C_30, D_31)))), inference(resolution, [status(thm)], [c_30, c_222])).
% 4.86/1.82  tff(c_231, plain, (![E_197, F_196, C_199, A_198, D_200]: ('#skF_3'(F_196, E_197, A_198, C_199, '#skF_6', D_200)='#skF_9' | F_196!='#skF_10' | ~m1_subset_1('#skF_4'(F_196, E_197, A_198, C_199, '#skF_6', D_200), '#skF_8') | ~m1_subset_1('#skF_3'(F_196, E_197, A_198, C_199, '#skF_6', D_200), '#skF_7') | ~m1_subset_1('#skF_1'(F_196, E_197, A_198, C_199, '#skF_6', D_200), '#skF_5') | k9_mcart_1(A_198, '#skF_6', C_199, D_200, F_196)=E_197 | k1_xboole_0=D_200 | k1_xboole_0=C_199 | k1_xboole_0=A_198 | ~m1_subset_1(F_196, k4_zfmisc_1(A_198, '#skF_6', C_199, D_200)))), inference(negUnitSimplification, [status(thm)], [c_40, c_40, c_226])).
% 4.86/1.82  tff(c_235, plain, (![F_33, E_32, C_30, D_31]: ('#skF_3'(F_33, E_32, '#skF_5', C_30, '#skF_6', D_31)='#skF_9' | F_33!='#skF_10' | ~m1_subset_1('#skF_4'(F_33, E_32, '#skF_5', C_30, '#skF_6', D_31), '#skF_8') | ~m1_subset_1('#skF_3'(F_33, E_32, '#skF_5', C_30, '#skF_6', D_31), '#skF_7') | k9_mcart_1('#skF_5', '#skF_6', C_30, D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0=C_30 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_33, k4_zfmisc_1('#skF_5', '#skF_6', C_30, D_31)))), inference(resolution, [status(thm)], [c_32, c_231])).
% 4.86/1.82  tff(c_240, plain, (![F_201, E_202, C_203, D_204]: ('#skF_3'(F_201, E_202, '#skF_5', C_203, '#skF_6', D_204)='#skF_9' | F_201!='#skF_10' | ~m1_subset_1('#skF_4'(F_201, E_202, '#skF_5', C_203, '#skF_6', D_204), '#skF_8') | ~m1_subset_1('#skF_3'(F_201, E_202, '#skF_5', C_203, '#skF_6', D_204), '#skF_7') | k9_mcart_1('#skF_5', '#skF_6', C_203, D_204, F_201)=E_202 | k1_xboole_0=D_204 | k1_xboole_0=C_203 | ~m1_subset_1(F_201, k4_zfmisc_1('#skF_5', '#skF_6', C_203, D_204)))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_42, c_235])).
% 4.86/1.82  tff(c_244, plain, (![F_33, E_32, D_31]: ('#skF_3'(F_33, E_32, '#skF_5', '#skF_7', '#skF_6', D_31)='#skF_9' | F_33!='#skF_10' | ~m1_subset_1('#skF_4'(F_33, E_32, '#skF_5', '#skF_7', '#skF_6', D_31), '#skF_8') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_33, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_31)))), inference(resolution, [status(thm)], [c_28, c_240])).
% 4.86/1.82  tff(c_249, plain, (![F_205, E_206, D_207]: ('#skF_3'(F_205, E_206, '#skF_5', '#skF_7', '#skF_6', D_207)='#skF_9' | F_205!='#skF_10' | ~m1_subset_1('#skF_4'(F_205, E_206, '#skF_5', '#skF_7', '#skF_6', D_207), '#skF_8') | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', D_207, F_205)=E_206 | k1_xboole_0=D_207 | ~m1_subset_1(F_205, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_207)))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_38, c_244])).
% 4.86/1.82  tff(c_253, plain, (![F_33, E_32]: ('#skF_3'(F_33, E_32, '#skF_5', '#skF_7', '#skF_6', '#skF_8')='#skF_9' | F_33!='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_33)=E_32 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_33, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_26, c_249])).
% 4.86/1.82  tff(c_258, plain, (![F_208, E_209]: ('#skF_3'(F_208, E_209, '#skF_5', '#skF_7', '#skF_6', '#skF_8')='#skF_9' | F_208!='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_208)=E_209 | ~m1_subset_1(F_208, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_36, c_253])).
% 4.86/1.82  tff(c_280, plain, (![E_210]: ('#skF_3'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8')='#skF_9' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210)), inference(resolution, [status(thm)], [c_46, c_258])).
% 4.86/1.82  tff(c_24, plain, (![C_30, E_32, D_31, B_29, F_33, A_28]: (k4_mcart_1('#skF_1'(F_33, E_32, A_28, C_30, B_29, D_31), '#skF_2'(F_33, E_32, A_28, C_30, B_29, D_31), '#skF_3'(F_33, E_32, A_28, C_30, B_29, D_31), '#skF_4'(F_33, E_32, A_28, C_30, B_29, D_31))=F_33 | k9_mcart_1(A_28, B_29, C_30, D_31, F_33)=E_32 | k1_xboole_0=D_31 | k1_xboole_0=C_30 | k1_xboole_0=B_29 | k1_xboole_0=A_28 | ~m1_subset_1(F_33, k4_zfmisc_1(A_28, B_29, C_30, D_31)))), inference(cnfTransformation, [status(thm)], [f_109])).
% 4.86/1.82  tff(c_289, plain, (![E_210]: (k4_mcart_1('#skF_1'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_2'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9', '#skF_4'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'))='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210)), inference(superposition, [status(thm), theory('equality')], [c_280, c_24])).
% 4.86/1.82  tff(c_736, plain, (![E_210]: (k4_mcart_1('#skF_1'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_2'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9', '#skF_4'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_289])).
% 4.86/1.82  tff(c_737, plain, (![E_210]: (k4_mcart_1('#skF_1'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_2'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9', '#skF_4'('#skF_10', E_210, '#skF_5', '#skF_7', '#skF_6', '#skF_8'))='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210)), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_736])).
% 4.86/1.82  tff(c_813, plain, (![E_2663]: (k4_mcart_1('#skF_1'('#skF_10', E_2663, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_2'('#skF_10', E_2663, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9', '#skF_4'('#skF_10', E_2663, '#skF_5', '#skF_7', '#skF_6', '#skF_8'))='#skF_10' | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_2663)), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_736])).
% 4.86/1.82  tff(c_16, plain, (![B_16, A_15, D_18, H_26, I_27, F_24, C_17, G_25]: (k10_mcart_1(A_15, B_16, C_17, D_18, k4_mcart_1(F_24, G_25, H_26, I_27))=H_26 | k1_xboole_0=D_18 | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15 | ~m1_subset_1(k4_mcart_1(F_24, G_25, H_26, I_27), k4_zfmisc_1(A_15, B_16, C_17, D_18)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.86/1.82  tff(c_1118, plain, (![B_3261, C_3258, E_3260, A_3262, D_3259]: (k10_mcart_1(A_3262, B_3261, C_3258, D_3259, k4_mcart_1('#skF_1'('#skF_10', E_3260, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_2'('#skF_10', E_3260, '#skF_5', '#skF_7', '#skF_6', '#skF_8'), '#skF_9', '#skF_4'('#skF_10', E_3260, '#skF_5', '#skF_7', '#skF_6', '#skF_8')))='#skF_9' | k1_xboole_0=D_3259 | k1_xboole_0=C_3258 | k1_xboole_0=B_3261 | k1_xboole_0=A_3262 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_3262, B_3261, C_3258, D_3259)) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_3260)), inference(superposition, [status(thm), theory('equality')], [c_813, c_16])).
% 4.86/1.82  tff(c_1127, plain, (![B_3261, C_3258, E_210, A_3262, D_3259]: (k10_mcart_1(A_3262, B_3261, C_3258, D_3259, '#skF_10')='#skF_9' | k1_xboole_0=D_3259 | k1_xboole_0=C_3258 | k1_xboole_0=B_3261 | k1_xboole_0=A_3262 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_3262, B_3261, C_3258, D_3259)) | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210 | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210)), inference(superposition, [status(thm), theory('equality')], [c_737, c_1118])).
% 4.86/1.82  tff(c_1158, plain, (![E_210]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210 | k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210)), inference(splitLeft, [status(thm)], [c_1127])).
% 4.86/1.82  tff(c_2487, plain, (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(factorization, [status(thm), theory('equality')], [c_1158])).
% 4.86/1.82  tff(c_1179, plain, (![E_210]: (k9_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_210)), inference(factorization, [status(thm), theory('equality')], [c_1158])).
% 4.86/1.82  tff(c_3111, plain, (![E_12426]: (E_12426='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2487, c_1179])).
% 4.86/1.82  tff(c_3485, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3111, c_38])).
% 4.86/1.82  tff(c_3487, plain, (![A_15435, B_15436, C_15437, D_15438]: (k10_mcart_1(A_15435, B_15436, C_15437, D_15438, '#skF_10')='#skF_9' | k1_xboole_0=D_15438 | k1_xboole_0=C_15437 | k1_xboole_0=B_15436 | k1_xboole_0=A_15435 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_15435, B_15436, C_15437, D_15438)))), inference(splitRight, [status(thm)], [c_1127])).
% 4.86/1.82  tff(c_3491, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_46, c_3487])).
% 4.86/1.82  tff(c_3495, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_36, c_34, c_3491])).
% 4.86/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.82  
% 4.86/1.82  Inference rules
% 4.86/1.82  ----------------------
% 4.86/1.82  #Ref     : 0
% 4.86/1.82  #Sup     : 366
% 4.86/1.82  #Fact    : 4
% 4.86/1.82  #Define  : 0
% 4.86/1.82  #Split   : 9
% 4.86/1.82  #Chain   : 0
% 4.86/1.82  #Close   : 0
% 4.86/1.82  
% 4.86/1.82  Ordering : KBO
% 4.86/1.82  
% 4.86/1.82  Simplification rules
% 4.86/1.82  ----------------------
% 4.86/1.82  #Subsume      : 32
% 4.86/1.82  #Demod        : 73
% 4.86/1.82  #Tautology    : 76
% 4.86/1.82  #SimpNegUnit  : 33
% 4.86/1.82  #BackRed      : 0
% 4.86/1.82  
% 4.86/1.82  #Partial instantiations: 4623
% 4.86/1.82  #Strategies tried      : 1
% 4.86/1.82  
% 4.86/1.82  Timing (in seconds)
% 4.86/1.82  ----------------------
% 4.86/1.83  Preprocessing        : 0.35
% 4.86/1.83  Parsing              : 0.18
% 4.86/1.83  CNF conversion       : 0.03
% 4.86/1.83  Main loop            : 0.72
% 4.86/1.83  Inferencing          : 0.38
% 4.86/1.83  Reduction            : 0.15
% 4.86/1.83  Demodulation         : 0.09
% 4.86/1.83  BG Simplification    : 0.04
% 4.90/1.83  Subsumption          : 0.10
% 4.90/1.83  Abstraction          : 0.05
% 4.90/1.83  MUC search           : 0.00
% 4.90/1.83  Cooper               : 0.00
% 4.90/1.83  Total                : 1.10
% 4.90/1.83  Index Insertion      : 0.00
% 4.90/1.83  Index Deletion       : 0.00
% 4.90/1.83  Index Matching       : 0.00
% 4.90/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
