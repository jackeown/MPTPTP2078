%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:19 EST 2020

% Result     : Theorem 4.11s
% Output     : CNFRefutation 4.11s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 460 expanded)
%              Number of leaves         :   26 ( 195 expanded)
%              Depth                    :   20
%              Number of atoms          :  225 (3132 expanded)
%              Number of equality atoms :  167 (2019 expanded)
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
                           => E = I ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k10_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_mcart_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_mcart_1)).

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

tff(c_30,plain,(
    k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_42,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

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

tff(c_176,plain,(
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
    ! [I_79,G_67,H_75,J_81] :
      ( I_79 = '#skF_9'
      | k4_mcart_1(G_67,H_75,I_79,J_81) != '#skF_10'
      | ~ m1_subset_1(J_81,'#skF_8')
      | ~ m1_subset_1(I_79,'#skF_7')
      | ~ m1_subset_1(H_75,'#skF_6')
      | ~ m1_subset_1(G_67,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_200,plain,(
    ! [C_176,B_177,A_178,D_179,E_174,F_175] :
      ( '#skF_3'(C_176,B_177,D_179,E_174,A_178,F_175) = '#skF_9'
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
    inference(superposition,[status(thm),theory(equality)],[c_176,c_40])).

tff(c_204,plain,(
    ! [C_22,D_23,A_20,F_25,E_24] :
      ( '#skF_3'(C_22,'#skF_6',D_23,E_24,A_20,F_25) = '#skF_9'
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
    inference(resolution,[status(thm)],[c_26,c_200])).

tff(c_209,plain,(
    ! [D_181,F_184,C_180,A_183,E_182] :
      ( '#skF_3'(C_180,'#skF_6',D_181,E_182,A_183,F_184) = '#skF_9'
      | F_184 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_180,'#skF_6',D_181,E_182,A_183,F_184),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_180,'#skF_6',D_181,E_182,A_183,F_184),'#skF_7')
      | ~ m1_subset_1('#skF_1'(C_180,'#skF_6',D_181,E_182,A_183,F_184),'#skF_5')
      | k8_mcart_1(A_183,'#skF_6',C_180,D_181,F_184) = E_182
      | k1_xboole_0 = D_181
      | k1_xboole_0 = C_180
      | k1_xboole_0 = A_183
      | ~ m1_subset_1(F_184,k4_zfmisc_1(A_183,'#skF_6',C_180,D_181)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_204])).

tff(c_213,plain,(
    ! [C_22,D_23,E_24,F_25] :
      ( '#skF_3'(C_22,'#skF_6',D_23,E_24,'#skF_5',F_25) = '#skF_9'
      | F_25 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_22,'#skF_6',D_23,E_24,'#skF_5',F_25),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_22,'#skF_6',D_23,E_24,'#skF_5',F_25),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_22,D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = C_22
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_25,k4_zfmisc_1('#skF_5','#skF_6',C_22,D_23)) ) ),
    inference(resolution,[status(thm)],[c_28,c_209])).

tff(c_218,plain,(
    ! [C_185,D_186,E_187,F_188] :
      ( '#skF_3'(C_185,'#skF_6',D_186,E_187,'#skF_5',F_188) = '#skF_9'
      | F_188 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(C_185,'#skF_6',D_186,E_187,'#skF_5',F_188),'#skF_8')
      | ~ m1_subset_1('#skF_3'(C_185,'#skF_6',D_186,E_187,'#skF_5',F_188),'#skF_7')
      | k8_mcart_1('#skF_5','#skF_6',C_185,D_186,F_188) = E_187
      | k1_xboole_0 = D_186
      | k1_xboole_0 = C_185
      | ~ m1_subset_1(F_188,k4_zfmisc_1('#skF_5','#skF_6',C_185,D_186)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_38,c_213])).

tff(c_222,plain,(
    ! [D_23,E_24,F_25] :
      ( '#skF_3'('#skF_7','#skF_6',D_23,E_24,'#skF_5',F_25) = '#skF_9'
      | F_25 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_6',D_23,E_24,'#skF_5',F_25),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_23,F_25) = E_24
      | k1_xboole_0 = D_23
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_25,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_23)) ) ),
    inference(resolution,[status(thm)],[c_24,c_218])).

tff(c_227,plain,(
    ! [D_189,E_190,F_191] :
      ( '#skF_3'('#skF_7','#skF_6',D_189,E_190,'#skF_5',F_191) = '#skF_9'
      | F_191 != '#skF_10'
      | ~ m1_subset_1('#skF_4'('#skF_7','#skF_6',D_189,E_190,'#skF_5',F_191),'#skF_8')
      | k8_mcart_1('#skF_5','#skF_6','#skF_7',D_189,F_191) = E_190
      | k1_xboole_0 = D_189
      | ~ m1_subset_1(F_191,k4_zfmisc_1('#skF_5','#skF_6','#skF_7',D_189)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_34,c_222])).

tff(c_231,plain,(
    ! [E_24,F_25] :
      ( '#skF_3'('#skF_7','#skF_6','#skF_8',E_24,'#skF_5',F_25) = '#skF_9'
      | F_25 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_25) = E_24
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1(F_25,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(resolution,[status(thm)],[c_22,c_227])).

tff(c_236,plain,(
    ! [E_192,F_193] :
      ( '#skF_3'('#skF_7','#skF_6','#skF_8',E_192,'#skF_5',F_193) = '#skF_9'
      | F_193 != '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8',F_193) = E_192
      | ~ m1_subset_1(F_193,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_32,c_231])).

tff(c_258,plain,(
    ! [E_194] :
      ( '#skF_3'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10') = '#skF_9'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(resolution,[status(thm)],[c_42,c_236])).

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

tff(c_267,plain,(
    ! [E_194] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10')) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_20])).

tff(c_630,plain,(
    ! [E_194] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10')) = '#skF_10'
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_267])).

tff(c_631,plain,(
    ! [E_194] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_7','#skF_6','#skF_8',E_194,'#skF_5','#skF_10')) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_630])).

tff(c_728,plain,(
    ! [E_2213] :
      ( k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_2213,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_2213,'#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_7','#skF_6','#skF_8',E_2213,'#skF_5','#skF_10')) = '#skF_10'
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_2213 ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_630])).

tff(c_12,plain,(
    ! [G_17,I_19,F_16,D_10,A_7,B_8,H_18,C_9] :
      ( k10_mcart_1(A_7,B_8,C_9,D_10,k4_mcart_1(F_16,G_17,H_18,I_19)) = H_18
      | k1_xboole_0 = D_10
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7
      | ~ m1_subset_1(k4_mcart_1(F_16,G_17,H_18,I_19),k4_zfmisc_1(A_7,B_8,C_9,D_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_992,plain,(
    ! [C_2666,B_2665,A_2667,E_2668,D_2664] :
      ( k10_mcart_1(A_2667,B_2665,C_2666,D_2664,k4_mcart_1('#skF_1'('#skF_7','#skF_6','#skF_8',E_2668,'#skF_5','#skF_10'),'#skF_2'('#skF_7','#skF_6','#skF_8',E_2668,'#skF_5','#skF_10'),'#skF_9','#skF_4'('#skF_7','#skF_6','#skF_8',E_2668,'#skF_5','#skF_10'))) = '#skF_9'
      | k1_xboole_0 = D_2664
      | k1_xboole_0 = C_2666
      | k1_xboole_0 = B_2665
      | k1_xboole_0 = A_2667
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_2667,B_2665,C_2666,D_2664))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_2668 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_12])).

tff(c_1001,plain,(
    ! [C_2666,E_194,B_2665,A_2667,D_2664] :
      ( k10_mcart_1(A_2667,B_2665,C_2666,D_2664,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_2664
      | k1_xboole_0 = C_2666
      | k1_xboole_0 = B_2665
      | k1_xboole_0 = A_2667
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_2667,B_2665,C_2666,D_2664))
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_631,c_992])).

tff(c_1027,plain,(
    ! [E_194] :
      ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194
      | k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ) ),
    inference(splitLeft,[status(thm)],[c_1001])).

tff(c_2107,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_7' ),
    inference(factorization,[status(thm),theory(equality)],[c_1027])).

tff(c_1048,plain,(
    ! [E_194] : k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = E_194 ),
    inference(factorization,[status(thm),theory(equality)],[c_1027])).

tff(c_2661,plain,(
    ! [E_11258] : E_11258 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_2107,c_1048])).

tff(c_2949,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2661,c_34])).

tff(c_2951,plain,(
    ! [A_12609,B_12610,C_12611,D_12612] :
      ( k10_mcart_1(A_12609,B_12610,C_12611,D_12612,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_12612
      | k1_xboole_0 = C_12611
      | k1_xboole_0 = B_12610
      | k1_xboole_0 = A_12609
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_12609,B_12610,C_12611,D_12612)) ) ),
    inference(splitRight,[status(thm)],[c_1001])).

tff(c_2955,plain,
    ( k10_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_42,c_2951])).

tff(c_2959,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_32,c_30,c_2955])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:36:20 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.11/1.74  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.75  
% 4.11/1.75  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.75  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_1 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_4
% 4.11/1.75  
% 4.11/1.75  %Foreground sorts:
% 4.11/1.75  
% 4.11/1.75  
% 4.11/1.75  %Background operators:
% 4.11/1.75  
% 4.11/1.75  
% 4.11/1.75  %Foreground operators:
% 4.11/1.75  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.11/1.75  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.11/1.75  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 4.11/1.75  tff('#skF_7', type, '#skF_7': $i).
% 4.11/1.75  tff('#skF_10', type, '#skF_10': $i).
% 4.11/1.75  tff('#skF_5', type, '#skF_5': $i).
% 4.11/1.75  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff('#skF_6', type, '#skF_6': $i).
% 4.11/1.75  tff('#skF_9', type, '#skF_9': $i).
% 4.11/1.75  tff('#skF_8', type, '#skF_8': $i).
% 4.11/1.75  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.11/1.75  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.11/1.75  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.11/1.75  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.11/1.75  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 4.11/1.75  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i * $i) > $i).
% 4.11/1.75  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.11/1.75  
% 4.11/1.77  tff(f_134, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = I)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k10_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_mcart_1)).
% 4.11/1.77  tff(f_105, axiom, (![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_mcart_1)).
% 4.11/1.77  tff(f_77, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t78_mcart_1)).
% 4.11/1.77  tff(c_38, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.11/1.77  tff(c_36, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.11/1.77  tff(c_34, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.11/1.77  tff(c_32, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.11/1.77  tff(c_30, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.11/1.77  tff(c_42, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.11/1.77  tff(c_22, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_4'(C_22, B_21, D_23, E_24, A_20, F_25), D_23) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.77  tff(c_24, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_3'(C_22, B_21, D_23, E_24, A_20, F_25), C_22) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.77  tff(c_28, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_1'(C_22, B_21, D_23, E_24, A_20, F_25), A_20) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.77  tff(c_26, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (m1_subset_1('#skF_2'(C_22, B_21, D_23, E_24, A_20, F_25), B_21) | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.77  tff(c_176, plain, (![D_170, F_173, A_172, C_168, E_171, B_169]: (k4_mcart_1('#skF_1'(C_168, B_169, D_170, E_171, A_172, F_173), '#skF_2'(C_168, B_169, D_170, E_171, A_172, F_173), '#skF_3'(C_168, B_169, D_170, E_171, A_172, F_173), '#skF_4'(C_168, B_169, D_170, E_171, A_172, F_173))=F_173 | k8_mcart_1(A_172, B_169, C_168, D_170, F_173)=E_171 | k1_xboole_0=D_170 | k1_xboole_0=C_168 | k1_xboole_0=B_169 | k1_xboole_0=A_172 | ~m1_subset_1(F_173, k4_zfmisc_1(A_172, B_169, C_168, D_170)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.77  tff(c_40, plain, (![I_79, G_67, H_75, J_81]: (I_79='#skF_9' | k4_mcart_1(G_67, H_75, I_79, J_81)!='#skF_10' | ~m1_subset_1(J_81, '#skF_8') | ~m1_subset_1(I_79, '#skF_7') | ~m1_subset_1(H_75, '#skF_6') | ~m1_subset_1(G_67, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_134])).
% 4.11/1.77  tff(c_200, plain, (![C_176, B_177, A_178, D_179, E_174, F_175]: ('#skF_3'(C_176, B_177, D_179, E_174, A_178, F_175)='#skF_9' | F_175!='#skF_10' | ~m1_subset_1('#skF_4'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_8') | ~m1_subset_1('#skF_3'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_7') | ~m1_subset_1('#skF_2'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_6') | ~m1_subset_1('#skF_1'(C_176, B_177, D_179, E_174, A_178, F_175), '#skF_5') | k8_mcart_1(A_178, B_177, C_176, D_179, F_175)=E_174 | k1_xboole_0=D_179 | k1_xboole_0=C_176 | k1_xboole_0=B_177 | k1_xboole_0=A_178 | ~m1_subset_1(F_175, k4_zfmisc_1(A_178, B_177, C_176, D_179)))), inference(superposition, [status(thm), theory('equality')], [c_176, c_40])).
% 4.11/1.77  tff(c_204, plain, (![C_22, D_23, A_20, F_25, E_24]: ('#skF_3'(C_22, '#skF_6', D_23, E_24, A_20, F_25)='#skF_9' | F_25!='#skF_10' | ~m1_subset_1('#skF_4'(C_22, '#skF_6', D_23, E_24, A_20, F_25), '#skF_8') | ~m1_subset_1('#skF_3'(C_22, '#skF_6', D_23, E_24, A_20, F_25), '#skF_7') | ~m1_subset_1('#skF_1'(C_22, '#skF_6', D_23, E_24, A_20, F_25), '#skF_5') | k8_mcart_1(A_20, '#skF_6', C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0='#skF_6' | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, '#skF_6', C_22, D_23)))), inference(resolution, [status(thm)], [c_26, c_200])).
% 4.11/1.77  tff(c_209, plain, (![D_181, F_184, C_180, A_183, E_182]: ('#skF_3'(C_180, '#skF_6', D_181, E_182, A_183, F_184)='#skF_9' | F_184!='#skF_10' | ~m1_subset_1('#skF_4'(C_180, '#skF_6', D_181, E_182, A_183, F_184), '#skF_8') | ~m1_subset_1('#skF_3'(C_180, '#skF_6', D_181, E_182, A_183, F_184), '#skF_7') | ~m1_subset_1('#skF_1'(C_180, '#skF_6', D_181, E_182, A_183, F_184), '#skF_5') | k8_mcart_1(A_183, '#skF_6', C_180, D_181, F_184)=E_182 | k1_xboole_0=D_181 | k1_xboole_0=C_180 | k1_xboole_0=A_183 | ~m1_subset_1(F_184, k4_zfmisc_1(A_183, '#skF_6', C_180, D_181)))), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_204])).
% 4.11/1.77  tff(c_213, plain, (![C_22, D_23, E_24, F_25]: ('#skF_3'(C_22, '#skF_6', D_23, E_24, '#skF_5', F_25)='#skF_9' | F_25!='#skF_10' | ~m1_subset_1('#skF_4'(C_22, '#skF_6', D_23, E_24, '#skF_5', F_25), '#skF_8') | ~m1_subset_1('#skF_3'(C_22, '#skF_6', D_23, E_24, '#skF_5', F_25), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_25, k4_zfmisc_1('#skF_5', '#skF_6', C_22, D_23)))), inference(resolution, [status(thm)], [c_28, c_209])).
% 4.11/1.77  tff(c_218, plain, (![C_185, D_186, E_187, F_188]: ('#skF_3'(C_185, '#skF_6', D_186, E_187, '#skF_5', F_188)='#skF_9' | F_188!='#skF_10' | ~m1_subset_1('#skF_4'(C_185, '#skF_6', D_186, E_187, '#skF_5', F_188), '#skF_8') | ~m1_subset_1('#skF_3'(C_185, '#skF_6', D_186, E_187, '#skF_5', F_188), '#skF_7') | k8_mcart_1('#skF_5', '#skF_6', C_185, D_186, F_188)=E_187 | k1_xboole_0=D_186 | k1_xboole_0=C_185 | ~m1_subset_1(F_188, k4_zfmisc_1('#skF_5', '#skF_6', C_185, D_186)))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_38, c_213])).
% 4.11/1.77  tff(c_222, plain, (![D_23, E_24, F_25]: ('#skF_3'('#skF_7', '#skF_6', D_23, E_24, '#skF_5', F_25)='#skF_9' | F_25!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_7', '#skF_6', D_23, E_24, '#skF_5', F_25), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_25, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_23)))), inference(resolution, [status(thm)], [c_24, c_218])).
% 4.11/1.77  tff(c_227, plain, (![D_189, E_190, F_191]: ('#skF_3'('#skF_7', '#skF_6', D_189, E_190, '#skF_5', F_191)='#skF_9' | F_191!='#skF_10' | ~m1_subset_1('#skF_4'('#skF_7', '#skF_6', D_189, E_190, '#skF_5', F_191), '#skF_8') | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', D_189, F_191)=E_190 | k1_xboole_0=D_189 | ~m1_subset_1(F_191, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', D_189)))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_34, c_222])).
% 4.11/1.77  tff(c_231, plain, (![E_24, F_25]: ('#skF_3'('#skF_7', '#skF_6', '#skF_8', E_24, '#skF_5', F_25)='#skF_9' | F_25!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_25)=E_24 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1(F_25, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(resolution, [status(thm)], [c_22, c_227])).
% 4.11/1.77  tff(c_236, plain, (![E_192, F_193]: ('#skF_3'('#skF_7', '#skF_6', '#skF_8', E_192, '#skF_5', F_193)='#skF_9' | F_193!='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', F_193)=E_192 | ~m1_subset_1(F_193, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_32, c_231])).
% 4.11/1.77  tff(c_258, plain, (![E_194]: ('#skF_3'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10')='#skF_9' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(resolution, [status(thm)], [c_42, c_236])).
% 4.11/1.77  tff(c_20, plain, (![C_22, D_23, A_20, B_21, F_25, E_24]: (k4_mcart_1('#skF_1'(C_22, B_21, D_23, E_24, A_20, F_25), '#skF_2'(C_22, B_21, D_23, E_24, A_20, F_25), '#skF_3'(C_22, B_21, D_23, E_24, A_20, F_25), '#skF_4'(C_22, B_21, D_23, E_24, A_20, F_25))=F_25 | k8_mcart_1(A_20, B_21, C_22, D_23, F_25)=E_24 | k1_xboole_0=D_23 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20 | ~m1_subset_1(F_25, k4_zfmisc_1(A_20, B_21, C_22, D_23)))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.11/1.77  tff(c_267, plain, (![E_194]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194 | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(superposition, [status(thm), theory('equality')], [c_258, c_20])).
% 4.11/1.77  tff(c_630, plain, (![E_194]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_267])).
% 4.11/1.77  tff(c_631, plain, (![E_194]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_7', '#skF_6', '#skF_8', E_194, '#skF_5', '#skF_10'))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_630])).
% 4.11/1.77  tff(c_728, plain, (![E_2213]: (k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_2213, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_2213, '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_7', '#skF_6', '#skF_8', E_2213, '#skF_5', '#skF_10'))='#skF_10' | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_2213)), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_630])).
% 4.11/1.77  tff(c_12, plain, (![G_17, I_19, F_16, D_10, A_7, B_8, H_18, C_9]: (k10_mcart_1(A_7, B_8, C_9, D_10, k4_mcart_1(F_16, G_17, H_18, I_19))=H_18 | k1_xboole_0=D_10 | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7 | ~m1_subset_1(k4_mcart_1(F_16, G_17, H_18, I_19), k4_zfmisc_1(A_7, B_8, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.11/1.77  tff(c_992, plain, (![C_2666, B_2665, A_2667, E_2668, D_2664]: (k10_mcart_1(A_2667, B_2665, C_2666, D_2664, k4_mcart_1('#skF_1'('#skF_7', '#skF_6', '#skF_8', E_2668, '#skF_5', '#skF_10'), '#skF_2'('#skF_7', '#skF_6', '#skF_8', E_2668, '#skF_5', '#skF_10'), '#skF_9', '#skF_4'('#skF_7', '#skF_6', '#skF_8', E_2668, '#skF_5', '#skF_10')))='#skF_9' | k1_xboole_0=D_2664 | k1_xboole_0=C_2666 | k1_xboole_0=B_2665 | k1_xboole_0=A_2667 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_2667, B_2665, C_2666, D_2664)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_2668)), inference(superposition, [status(thm), theory('equality')], [c_728, c_12])).
% 4.11/1.77  tff(c_1001, plain, (![C_2666, E_194, B_2665, A_2667, D_2664]: (k10_mcart_1(A_2667, B_2665, C_2666, D_2664, '#skF_10')='#skF_9' | k1_xboole_0=D_2664 | k1_xboole_0=C_2666 | k1_xboole_0=B_2665 | k1_xboole_0=A_2667 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_2667, B_2665, C_2666, D_2664)) | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(superposition, [status(thm), theory('equality')], [c_631, c_992])).
% 4.11/1.77  tff(c_1027, plain, (![E_194]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194 | k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(splitLeft, [status(thm)], [c_1001])).
% 4.11/1.77  tff(c_2107, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_7'), inference(factorization, [status(thm), theory('equality')], [c_1027])).
% 4.11/1.77  tff(c_1048, plain, (![E_194]: (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')=E_194)), inference(factorization, [status(thm), theory('equality')], [c_1027])).
% 4.11/1.77  tff(c_2661, plain, (![E_11258]: (E_11258='#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_2107, c_1048])).
% 4.11/1.77  tff(c_2949, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2661, c_34])).
% 4.11/1.77  tff(c_2951, plain, (![A_12609, B_12610, C_12611, D_12612]: (k10_mcart_1(A_12609, B_12610, C_12611, D_12612, '#skF_10')='#skF_9' | k1_xboole_0=D_12612 | k1_xboole_0=C_12611 | k1_xboole_0=B_12610 | k1_xboole_0=A_12609 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_12609, B_12610, C_12611, D_12612)))), inference(splitRight, [status(thm)], [c_1001])).
% 4.11/1.77  tff(c_2955, plain, (k10_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_42, c_2951])).
% 4.11/1.77  tff(c_2959, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_32, c_30, c_2955])).
% 4.11/1.77  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.11/1.77  
% 4.11/1.77  Inference rules
% 4.11/1.77  ----------------------
% 4.11/1.77  #Ref     : 0
% 4.11/1.77  #Sup     : 343
% 4.11/1.77  #Fact    : 4
% 4.11/1.77  #Define  : 0
% 4.11/1.77  #Split   : 9
% 4.11/1.77  #Chain   : 0
% 4.11/1.77  #Close   : 0
% 4.11/1.77  
% 4.11/1.77  Ordering : KBO
% 4.11/1.77  
% 4.11/1.77  Simplification rules
% 4.11/1.77  ----------------------
% 4.11/1.77  #Subsume      : 61
% 4.11/1.77  #Demod        : 79
% 4.11/1.77  #Tautology    : 78
% 4.11/1.77  #SimpNegUnit  : 33
% 4.11/1.77  #BackRed      : 0
% 4.11/1.77  
% 4.11/1.77  #Partial instantiations: 3547
% 4.11/1.77  #Strategies tried      : 1
% 4.11/1.77  
% 4.11/1.77  Timing (in seconds)
% 4.11/1.77  ----------------------
% 4.11/1.77  Preprocessing        : 0.38
% 4.11/1.77  Parsing              : 0.19
% 4.11/1.77  CNF conversion       : 0.03
% 4.11/1.77  Main loop            : 0.61
% 4.11/1.77  Inferencing          : 0.31
% 4.11/1.77  Reduction            : 0.13
% 4.11/1.77  Demodulation         : 0.08
% 4.11/1.77  BG Simplification    : 0.04
% 4.11/1.77  Subsumption          : 0.09
% 4.11/1.77  Abstraction          : 0.05
% 4.11/1.77  MUC search           : 0.00
% 4.11/1.77  Cooper               : 0.00
% 4.11/1.77  Total                : 1.03
% 4.11/1.77  Index Insertion      : 0.00
% 4.11/1.77  Index Deletion       : 0.00
% 4.11/1.77  Index Matching       : 0.00
% 4.11/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------
