%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:16 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.67s
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
%$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k9_mcart_1,type,(
    k9_mcart_1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k4_mcart_1,type,(
    k4_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
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
                           => E = G ) ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k1_xboole_0
            | E = k8_mcart_1(A,B,C,D,F) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_mcart_1)).

tff(f_60,axiom,(
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

tff(f_87,axiom,(
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

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_24,plain,(
    k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_36,plain,(
    m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_14,plain,(
    ! [E_44,C_11,B_10,D_12,A_9] :
      ( m1_subset_1('#skF_1'(E_44,B_10,C_11,D_12,A_9),A_9)
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_10,plain,(
    ! [E_44,C_11,B_10,D_12,A_9] :
      ( m1_subset_1('#skF_3'(E_44,B_10,C_11,D_12,A_9),C_11)
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_8,plain,(
    ! [E_44,C_11,B_10,D_12,A_9] :
      ( m1_subset_1('#skF_4'(E_44,B_10,C_11,D_12,A_9),D_12)
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_12,plain,(
    ! [E_44,C_11,B_10,D_12,A_9] :
      ( m1_subset_1('#skF_2'(E_44,B_10,C_11,D_12,A_9),B_10)
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_72,plain,(
    ! [D_181,E_178,A_182,C_180,B_179] :
      ( k4_mcart_1('#skF_1'(E_178,B_179,C_180,D_181,A_182),'#skF_2'(E_178,B_179,C_180,D_181,A_182),'#skF_3'(E_178,B_179,C_180,D_181,A_182),'#skF_4'(E_178,B_179,C_180,D_181,A_182)) = E_178
      | ~ m1_subset_1(E_178,k4_zfmisc_1(A_182,B_179,C_180,D_181))
      | k1_xboole_0 = D_181
      | k1_xboole_0 = C_180
      | k1_xboole_0 = B_179
      | k1_xboole_0 = A_182 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [G_99,H_107,I_111,J_113] :
      ( G_99 = '#skF_9'
      | k4_mcart_1(G_99,H_107,I_111,J_113) != '#skF_10'
      | ~ m1_subset_1(J_113,'#skF_8')
      | ~ m1_subset_1(I_111,'#skF_7')
      | ~ m1_subset_1(H_107,'#skF_6')
      | ~ m1_subset_1(G_99,'#skF_5') ) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_96,plain,(
    ! [B_183,C_187,D_184,A_185,E_186] :
      ( '#skF_1'(E_186,B_183,C_187,D_184,A_185) = '#skF_9'
      | E_186 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(E_186,B_183,C_187,D_184,A_185),'#skF_8')
      | ~ m1_subset_1('#skF_3'(E_186,B_183,C_187,D_184,A_185),'#skF_7')
      | ~ m1_subset_1('#skF_2'(E_186,B_183,C_187,D_184,A_185),'#skF_6')
      | ~ m1_subset_1('#skF_1'(E_186,B_183,C_187,D_184,A_185),'#skF_5')
      | ~ m1_subset_1(E_186,k4_zfmisc_1(A_185,B_183,C_187,D_184))
      | k1_xboole_0 = D_184
      | k1_xboole_0 = C_187
      | k1_xboole_0 = B_183
      | k1_xboole_0 = A_185 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_34])).

tff(c_100,plain,(
    ! [E_44,C_11,D_12,A_9] :
      ( '#skF_1'(E_44,'#skF_6',C_11,D_12,A_9) = '#skF_9'
      | E_44 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(E_44,'#skF_6',C_11,D_12,A_9),'#skF_8')
      | ~ m1_subset_1('#skF_3'(E_44,'#skF_6',C_11,D_12,A_9),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_44,'#skF_6',C_11,D_12,A_9),'#skF_5')
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,'#skF_6',C_11,D_12))
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_9 ) ),
    inference(resolution,[status(thm)],[c_12,c_96])).

tff(c_105,plain,(
    ! [E_188,C_189,D_190,A_191] :
      ( '#skF_1'(E_188,'#skF_6',C_189,D_190,A_191) = '#skF_9'
      | E_188 != '#skF_10'
      | ~ m1_subset_1('#skF_4'(E_188,'#skF_6',C_189,D_190,A_191),'#skF_8')
      | ~ m1_subset_1('#skF_3'(E_188,'#skF_6',C_189,D_190,A_191),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_188,'#skF_6',C_189,D_190,A_191),'#skF_5')
      | ~ m1_subset_1(E_188,k4_zfmisc_1(A_191,'#skF_6',C_189,D_190))
      | k1_xboole_0 = D_190
      | k1_xboole_0 = C_189
      | k1_xboole_0 = A_191 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_100])).

tff(c_109,plain,(
    ! [E_44,C_11,A_9] :
      ( '#skF_1'(E_44,'#skF_6',C_11,'#skF_8',A_9) = '#skF_9'
      | E_44 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(E_44,'#skF_6',C_11,'#skF_8',A_9),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_44,'#skF_6',C_11,'#skF_8',A_9),'#skF_5')
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,'#skF_6',C_11,'#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = C_11
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_9 ) ),
    inference(resolution,[status(thm)],[c_8,c_105])).

tff(c_114,plain,(
    ! [E_192,C_193,A_194] :
      ( '#skF_1'(E_192,'#skF_6',C_193,'#skF_8',A_194) = '#skF_9'
      | E_192 != '#skF_10'
      | ~ m1_subset_1('#skF_3'(E_192,'#skF_6',C_193,'#skF_8',A_194),'#skF_7')
      | ~ m1_subset_1('#skF_1'(E_192,'#skF_6',C_193,'#skF_8',A_194),'#skF_5')
      | ~ m1_subset_1(E_192,k4_zfmisc_1(A_194,'#skF_6',C_193,'#skF_8'))
      | k1_xboole_0 = C_193
      | k1_xboole_0 = A_194 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_26,c_26,c_109])).

tff(c_118,plain,(
    ! [E_44,A_9] :
      ( '#skF_1'(E_44,'#skF_6','#skF_7','#skF_8',A_9) = '#skF_9'
      | E_44 != '#skF_10'
      | ~ m1_subset_1('#skF_1'(E_44,'#skF_6','#skF_7','#skF_8',A_9),'#skF_5')
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = A_9 ) ),
    inference(resolution,[status(thm)],[c_10,c_114])).

tff(c_123,plain,(
    ! [E_195,A_196] :
      ( '#skF_1'(E_195,'#skF_6','#skF_7','#skF_8',A_196) = '#skF_9'
      | E_195 != '#skF_10'
      | ~ m1_subset_1('#skF_1'(E_195,'#skF_6','#skF_7','#skF_8',A_196),'#skF_5')
      | ~ m1_subset_1(E_195,k4_zfmisc_1(A_196,'#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = A_196 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_28,c_118])).

tff(c_127,plain,(
    ! [E_44] :
      ( '#skF_1'(E_44,'#skF_6','#skF_7','#skF_8','#skF_5') = '#skF_9'
      | E_44 != '#skF_10'
      | ~ m1_subset_1(E_44,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
      | k1_xboole_0 = '#skF_8'
      | k1_xboole_0 = '#skF_7'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5' ) ),
    inference(resolution,[status(thm)],[c_14,c_123])).

tff(c_132,plain,(
    ! [E_197] :
      ( '#skF_1'(E_197,'#skF_6','#skF_7','#skF_8','#skF_5') = '#skF_9'
      | E_197 != '#skF_10'
      | ~ m1_subset_1(E_197,k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_32,c_127])).

tff(c_156,plain,(
    '#skF_1'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5') = '#skF_9' ),
    inference(resolution,[status(thm)],[c_36,c_132])).

tff(c_6,plain,(
    ! [E_44,C_11,B_10,D_12,A_9] :
      ( k4_mcart_1('#skF_1'(E_44,B_10,C_11,D_12,A_9),'#skF_2'(E_44,B_10,C_11,D_12,A_9),'#skF_3'(E_44,B_10,C_11,D_12,A_9),'#skF_4'(E_44,B_10,C_11,D_12,A_9)) = E_44
      | ~ m1_subset_1(E_44,k4_zfmisc_1(A_9,B_10,C_11,D_12))
      | k1_xboole_0 = D_12
      | k1_xboole_0 = C_11
      | k1_xboole_0 = B_10
      | k1_xboole_0 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_163,plain,
    ( k4_mcart_1('#skF_9','#skF_2'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_3'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_4'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5')) = '#skF_10'
    | ~ m1_subset_1('#skF_10',k4_zfmisc_1('#skF_5','#skF_6','#skF_7','#skF_8'))
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_156,c_6])).

tff(c_174,plain,
    ( k4_mcart_1('#skF_9','#skF_2'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_3'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_4'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5')) = '#skF_10'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_163])).

tff(c_175,plain,(
    k4_mcart_1('#skF_9','#skF_2'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_3'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_4'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_174])).

tff(c_22,plain,(
    ! [H_82,D_74,I_83,F_80,C_73,B_72,G_81,A_71] :
      ( k8_mcart_1(A_71,B_72,C_73,D_74,k4_mcart_1(F_80,G_81,H_82,I_83)) = F_80
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_72
      | k1_xboole_0 = A_71
      | ~ m1_subset_1(k4_mcart_1(F_80,G_81,H_82,I_83),k4_zfmisc_1(A_71,B_72,C_73,D_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_205,plain,(
    ! [A_71,B_72,C_73,D_74] :
      ( k8_mcart_1(A_71,B_72,C_73,D_74,k4_mcart_1('#skF_9','#skF_2'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_3'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'),'#skF_4'('#skF_10','#skF_6','#skF_7','#skF_8','#skF_5'))) = '#skF_9'
      | k1_xboole_0 = D_74
      | k1_xboole_0 = C_73
      | k1_xboole_0 = B_72
      | k1_xboole_0 = A_71
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_71,B_72,C_73,D_74)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_22])).

tff(c_228,plain,(
    ! [A_207,B_208,C_209,D_210] :
      ( k8_mcart_1(A_207,B_208,C_209,D_210,'#skF_10') = '#skF_9'
      | k1_xboole_0 = D_210
      | k1_xboole_0 = C_209
      | k1_xboole_0 = B_208
      | k1_xboole_0 = A_207
      | ~ m1_subset_1('#skF_10',k4_zfmisc_1(A_207,B_208,C_209,D_210)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_205])).

tff(c_231,plain,
    ( k8_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8','#skF_10') = '#skF_9'
    | k1_xboole_0 = '#skF_8'
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_228])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_24,c_231])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:42:12 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.45  
% 2.31/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.31/1.46  %$ m1_subset_1 > k9_mcart_1 > k8_mcart_1 > k11_mcart_1 > k10_mcart_1 > k4_zfmisc_1 > k4_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_4 > #skF_7 > #skF_10 > #skF_5 > #skF_6 > #skF_9 > #skF_3 > #skF_1 > #skF_8
% 2.31/1.46  
% 2.31/1.46  %Foreground sorts:
% 2.31/1.46  
% 2.31/1.46  
% 2.31/1.46  %Background operators:
% 2.31/1.46  
% 2.31/1.46  
% 2.31/1.46  %Foreground operators:
% 2.31/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.31/1.46  tff(k10_mcart_1, type, k10_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.31/1.46  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 2.31/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.31/1.46  tff('#skF_10', type, '#skF_10': $i).
% 2.31/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.31/1.46  tff(k11_mcart_1, type, k11_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.31/1.46  tff('#skF_9', type, '#skF_9': $i).
% 2.31/1.46  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.31/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.31/1.46  tff(k8_mcart_1, type, k8_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.46  tff(k9_mcart_1, type, k9_mcart_1: ($i * $i * $i * $i * $i) > $i).
% 2.31/1.46  tff(k4_mcart_1, type, k4_mcart_1: ($i * $i * $i * $i) > $i).
% 2.31/1.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.46  
% 2.67/1.47  tff(f_116, negated_conjecture, ~(![A, B, C, D, E, F]: (m1_subset_1(F, k4_zfmisc_1(A, B, C, D)) => ((![G]: (m1_subset_1(G, A) => (![H]: (m1_subset_1(H, B) => (![I]: (m1_subset_1(I, C) => (![J]: (m1_subset_1(J, D) => ((F = k4_mcart_1(G, H, I, J)) => (E = G)))))))))) => (((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k1_xboole_0)) | (E = k8_mcart_1(A, B, C, D, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_mcart_1)).
% 2.67/1.47  tff(f_60, axiom, (![A, B, C, D]: ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) & (![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => (![I]: (m1_subset_1(I, D) => ~(E = k4_mcart_1(F, G, H, I)))))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l68_mcart_1)).
% 2.67/1.47  tff(f_87, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k4_zfmisc_1(A, B, C, D)) => ~((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) & (?[F, G, H, I]: ((E = k4_mcart_1(F, G, H, I)) & ~((((k8_mcart_1(A, B, C, D, E) = F) & (k9_mcart_1(A, B, C, D, E) = G)) & (k10_mcart_1(A, B, C, D, E) = H)) & (k11_mcart_1(A, B, C, D, E) = I))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_mcart_1)).
% 2.67/1.47  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.67/1.47  tff(c_30, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.67/1.47  tff(c_28, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.67/1.47  tff(c_26, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.67/1.47  tff(c_24, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.67/1.47  tff(c_36, plain, (m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.67/1.47  tff(c_14, plain, (![E_44, C_11, B_10, D_12, A_9]: (m1_subset_1('#skF_1'(E_44, B_10, C_11, D_12, A_9), A_9) | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.47  tff(c_10, plain, (![E_44, C_11, B_10, D_12, A_9]: (m1_subset_1('#skF_3'(E_44, B_10, C_11, D_12, A_9), C_11) | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.47  tff(c_8, plain, (![E_44, C_11, B_10, D_12, A_9]: (m1_subset_1('#skF_4'(E_44, B_10, C_11, D_12, A_9), D_12) | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.47  tff(c_12, plain, (![E_44, C_11, B_10, D_12, A_9]: (m1_subset_1('#skF_2'(E_44, B_10, C_11, D_12, A_9), B_10) | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.47  tff(c_72, plain, (![D_181, E_178, A_182, C_180, B_179]: (k4_mcart_1('#skF_1'(E_178, B_179, C_180, D_181, A_182), '#skF_2'(E_178, B_179, C_180, D_181, A_182), '#skF_3'(E_178, B_179, C_180, D_181, A_182), '#skF_4'(E_178, B_179, C_180, D_181, A_182))=E_178 | ~m1_subset_1(E_178, k4_zfmisc_1(A_182, B_179, C_180, D_181)) | k1_xboole_0=D_181 | k1_xboole_0=C_180 | k1_xboole_0=B_179 | k1_xboole_0=A_182)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.47  tff(c_34, plain, (![G_99, H_107, I_111, J_113]: (G_99='#skF_9' | k4_mcart_1(G_99, H_107, I_111, J_113)!='#skF_10' | ~m1_subset_1(J_113, '#skF_8') | ~m1_subset_1(I_111, '#skF_7') | ~m1_subset_1(H_107, '#skF_6') | ~m1_subset_1(G_99, '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 2.67/1.47  tff(c_96, plain, (![B_183, C_187, D_184, A_185, E_186]: ('#skF_1'(E_186, B_183, C_187, D_184, A_185)='#skF_9' | E_186!='#skF_10' | ~m1_subset_1('#skF_4'(E_186, B_183, C_187, D_184, A_185), '#skF_8') | ~m1_subset_1('#skF_3'(E_186, B_183, C_187, D_184, A_185), '#skF_7') | ~m1_subset_1('#skF_2'(E_186, B_183, C_187, D_184, A_185), '#skF_6') | ~m1_subset_1('#skF_1'(E_186, B_183, C_187, D_184, A_185), '#skF_5') | ~m1_subset_1(E_186, k4_zfmisc_1(A_185, B_183, C_187, D_184)) | k1_xboole_0=D_184 | k1_xboole_0=C_187 | k1_xboole_0=B_183 | k1_xboole_0=A_185)), inference(superposition, [status(thm), theory('equality')], [c_72, c_34])).
% 2.67/1.47  tff(c_100, plain, (![E_44, C_11, D_12, A_9]: ('#skF_1'(E_44, '#skF_6', C_11, D_12, A_9)='#skF_9' | E_44!='#skF_10' | ~m1_subset_1('#skF_4'(E_44, '#skF_6', C_11, D_12, A_9), '#skF_8') | ~m1_subset_1('#skF_3'(E_44, '#skF_6', C_11, D_12, A_9), '#skF_7') | ~m1_subset_1('#skF_1'(E_44, '#skF_6', C_11, D_12, A_9), '#skF_5') | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, '#skF_6', C_11, D_12)) | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0='#skF_6' | k1_xboole_0=A_9)), inference(resolution, [status(thm)], [c_12, c_96])).
% 2.67/1.47  tff(c_105, plain, (![E_188, C_189, D_190, A_191]: ('#skF_1'(E_188, '#skF_6', C_189, D_190, A_191)='#skF_9' | E_188!='#skF_10' | ~m1_subset_1('#skF_4'(E_188, '#skF_6', C_189, D_190, A_191), '#skF_8') | ~m1_subset_1('#skF_3'(E_188, '#skF_6', C_189, D_190, A_191), '#skF_7') | ~m1_subset_1('#skF_1'(E_188, '#skF_6', C_189, D_190, A_191), '#skF_5') | ~m1_subset_1(E_188, k4_zfmisc_1(A_191, '#skF_6', C_189, D_190)) | k1_xboole_0=D_190 | k1_xboole_0=C_189 | k1_xboole_0=A_191)), inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_100])).
% 2.67/1.47  tff(c_109, plain, (![E_44, C_11, A_9]: ('#skF_1'(E_44, '#skF_6', C_11, '#skF_8', A_9)='#skF_9' | E_44!='#skF_10' | ~m1_subset_1('#skF_3'(E_44, '#skF_6', C_11, '#skF_8', A_9), '#skF_7') | ~m1_subset_1('#skF_1'(E_44, '#skF_6', C_11, '#skF_8', A_9), '#skF_5') | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, '#skF_6', C_11, '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0=C_11 | k1_xboole_0='#skF_6' | k1_xboole_0=A_9)), inference(resolution, [status(thm)], [c_8, c_105])).
% 2.67/1.47  tff(c_114, plain, (![E_192, C_193, A_194]: ('#skF_1'(E_192, '#skF_6', C_193, '#skF_8', A_194)='#skF_9' | E_192!='#skF_10' | ~m1_subset_1('#skF_3'(E_192, '#skF_6', C_193, '#skF_8', A_194), '#skF_7') | ~m1_subset_1('#skF_1'(E_192, '#skF_6', C_193, '#skF_8', A_194), '#skF_5') | ~m1_subset_1(E_192, k4_zfmisc_1(A_194, '#skF_6', C_193, '#skF_8')) | k1_xboole_0=C_193 | k1_xboole_0=A_194)), inference(negUnitSimplification, [status(thm)], [c_30, c_26, c_26, c_109])).
% 2.67/1.47  tff(c_118, plain, (![E_44, A_9]: ('#skF_1'(E_44, '#skF_6', '#skF_7', '#skF_8', A_9)='#skF_9' | E_44!='#skF_10' | ~m1_subset_1('#skF_1'(E_44, '#skF_6', '#skF_7', '#skF_8', A_9), '#skF_5') | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0=A_9)), inference(resolution, [status(thm)], [c_10, c_114])).
% 2.67/1.47  tff(c_123, plain, (![E_195, A_196]: ('#skF_1'(E_195, '#skF_6', '#skF_7', '#skF_8', A_196)='#skF_9' | E_195!='#skF_10' | ~m1_subset_1('#skF_1'(E_195, '#skF_6', '#skF_7', '#skF_8', A_196), '#skF_5') | ~m1_subset_1(E_195, k4_zfmisc_1(A_196, '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0=A_196)), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_28, c_118])).
% 2.67/1.47  tff(c_127, plain, (![E_44]: ('#skF_1'(E_44, '#skF_6', '#skF_7', '#skF_8', '#skF_5')='#skF_9' | E_44!='#skF_10' | ~m1_subset_1(E_44, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5')), inference(resolution, [status(thm)], [c_14, c_123])).
% 2.67/1.47  tff(c_132, plain, (![E_197]: ('#skF_1'(E_197, '#skF_6', '#skF_7', '#skF_8', '#skF_5')='#skF_9' | E_197!='#skF_10' | ~m1_subset_1(E_197, k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_32, c_127])).
% 2.67/1.47  tff(c_156, plain, ('#skF_1'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5')='#skF_9'), inference(resolution, [status(thm)], [c_36, c_132])).
% 2.67/1.47  tff(c_6, plain, (![E_44, C_11, B_10, D_12, A_9]: (k4_mcart_1('#skF_1'(E_44, B_10, C_11, D_12, A_9), '#skF_2'(E_44, B_10, C_11, D_12, A_9), '#skF_3'(E_44, B_10, C_11, D_12, A_9), '#skF_4'(E_44, B_10, C_11, D_12, A_9))=E_44 | ~m1_subset_1(E_44, k4_zfmisc_1(A_9, B_10, C_11, D_12)) | k1_xboole_0=D_12 | k1_xboole_0=C_11 | k1_xboole_0=B_10 | k1_xboole_0=A_9)), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.67/1.47  tff(c_163, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_3'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_4'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'))='#skF_10' | ~m1_subset_1('#skF_10', k4_zfmisc_1('#skF_5', '#skF_6', '#skF_7', '#skF_8')) | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_156, c_6])).
% 2.67/1.47  tff(c_174, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_3'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_4'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'))='#skF_10' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_163])).
% 2.67/1.47  tff(c_175, plain, (k4_mcart_1('#skF_9', '#skF_2'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_3'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_4'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_174])).
% 2.67/1.47  tff(c_22, plain, (![H_82, D_74, I_83, F_80, C_73, B_72, G_81, A_71]: (k8_mcart_1(A_71, B_72, C_73, D_74, k4_mcart_1(F_80, G_81, H_82, I_83))=F_80 | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71 | ~m1_subset_1(k4_mcart_1(F_80, G_81, H_82, I_83), k4_zfmisc_1(A_71, B_72, C_73, D_74)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.67/1.47  tff(c_205, plain, (![A_71, B_72, C_73, D_74]: (k8_mcart_1(A_71, B_72, C_73, D_74, k4_mcart_1('#skF_9', '#skF_2'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_3'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5'), '#skF_4'('#skF_10', '#skF_6', '#skF_7', '#skF_8', '#skF_5')))='#skF_9' | k1_xboole_0=D_74 | k1_xboole_0=C_73 | k1_xboole_0=B_72 | k1_xboole_0=A_71 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_71, B_72, C_73, D_74)))), inference(superposition, [status(thm), theory('equality')], [c_175, c_22])).
% 2.67/1.47  tff(c_228, plain, (![A_207, B_208, C_209, D_210]: (k8_mcart_1(A_207, B_208, C_209, D_210, '#skF_10')='#skF_9' | k1_xboole_0=D_210 | k1_xboole_0=C_209 | k1_xboole_0=B_208 | k1_xboole_0=A_207 | ~m1_subset_1('#skF_10', k4_zfmisc_1(A_207, B_208, C_209, D_210)))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_205])).
% 2.67/1.47  tff(c_231, plain, (k8_mcart_1('#skF_5', '#skF_6', '#skF_7', '#skF_8', '#skF_10')='#skF_9' | k1_xboole_0='#skF_8' | k1_xboole_0='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_36, c_228])).
% 2.67/1.47  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_24, c_231])).
% 2.67/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.67/1.47  
% 2.67/1.47  Inference rules
% 2.67/1.47  ----------------------
% 2.67/1.47  #Ref     : 0
% 2.67/1.47  #Sup     : 37
% 2.67/1.47  #Fact    : 0
% 2.67/1.47  #Define  : 0
% 2.67/1.47  #Split   : 0
% 2.67/1.47  #Chain   : 0
% 2.67/1.47  #Close   : 0
% 2.67/1.47  
% 2.67/1.47  Ordering : KBO
% 2.67/1.47  
% 2.67/1.47  Simplification rules
% 2.67/1.47  ----------------------
% 2.67/1.47  #Subsume      : 0
% 2.67/1.47  #Demod        : 10
% 2.67/1.47  #Tautology    : 14
% 2.67/1.47  #SimpNegUnit  : 9
% 2.67/1.47  #BackRed      : 0
% 2.67/1.47  
% 2.67/1.47  #Partial instantiations: 0
% 2.67/1.47  #Strategies tried      : 1
% 2.67/1.47  
% 2.67/1.47  Timing (in seconds)
% 2.67/1.47  ----------------------
% 2.67/1.48  Preprocessing        : 0.36
% 2.67/1.48  Parsing              : 0.19
% 2.67/1.48  CNF conversion       : 0.03
% 2.67/1.48  Main loop            : 0.25
% 2.67/1.48  Inferencing          : 0.11
% 2.67/1.48  Reduction            : 0.06
% 2.67/1.48  Demodulation         : 0.04
% 2.67/1.48  BG Simplification    : 0.02
% 2.67/1.48  Subsumption          : 0.05
% 2.67/1.48  Abstraction          : 0.02
% 2.67/1.48  MUC search           : 0.00
% 2.67/1.48  Cooper               : 0.00
% 2.67/1.48  Total                : 0.64
% 2.67/1.48  Index Insertion      : 0.00
% 2.67/1.48  Index Deletion       : 0.00
% 2.67/1.48  Index Matching       : 0.00
% 2.67/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
