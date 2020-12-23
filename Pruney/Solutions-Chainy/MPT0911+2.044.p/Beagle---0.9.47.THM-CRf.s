%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 2.81s
% Output     : CNFRefutation 2.81s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 116 expanded)
%              Number of leaves         :   25 (  57 expanded)
%              Depth                    :   12
%              Number of atoms          :  153 ( 499 expanded)
%              Number of equality atoms :  111 ( 326 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ! [E] :
                ( m1_subset_1(E,A)
               => ! [F] :
                    ( m1_subset_1(F,B)
                   => ! [G] :
                        ( m1_subset_1(G,C)
                       => D != k3_mcart_1(E,F,G) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_94,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_223,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k3_mcart_1('#skF_1'(A_116,B_117,C_118,D_119),'#skF_2'(A_116,B_117,C_118,D_119),'#skF_3'(A_116,B_117,C_118,D_119)) = D_119
      | ~ m1_subset_1(D_119,k3_zfmisc_1(A_116,B_117,C_118))
      | k1_xboole_0 = C_118
      | k1_xboole_0 = B_117
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    ! [A_94,B_95,C_96,D_97] :
      ( k7_mcart_1(A_94,B_95,C_96,D_97) = k2_mcart_1(D_97)
      | ~ m1_subset_1(D_97,k3_zfmisc_1(A_94,B_95,C_96))
      | k1_xboole_0 = C_96
      | k1_xboole_0 = B_95
      | k1_xboole_0 = A_94 ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_69,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_75,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_69])).

tff(c_139,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k3_mcart_1(k5_mcart_1(A_106,B_107,C_108,D_109),k6_mcart_1(A_106,B_107,C_108,D_109),k7_mcart_1(A_106,B_107,C_108,D_109)) = D_109
      | ~ m1_subset_1(D_109,k3_zfmisc_1(A_106,B_107,C_108))
      | k1_xboole_0 = C_108
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_168,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_139])).

tff(c_172,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_168])).

tff(c_173,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_172])).

tff(c_10,plain,(
    ! [A_31,C_33,B_32,F_36,E_35,D_34] :
      ( F_36 = C_33
      | k3_mcart_1(D_34,E_35,F_36) != k3_mcart_1(A_31,B_32,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_185,plain,(
    ! [C_33,A_31,B_32] :
      ( k2_mcart_1('#skF_8') = C_33
      | k3_mcart_1(A_31,B_32,C_33) != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_173,c_10])).

tff(c_300,plain,(
    ! [A_131,B_132,C_133,D_134] :
      ( k2_mcart_1('#skF_8') = '#skF_3'(A_131,B_132,C_133,D_134)
      | D_134 != '#skF_8'
      | ~ m1_subset_1(D_134,k3_zfmisc_1(A_131,B_132,C_133))
      | k1_xboole_0 = C_133
      | k1_xboole_0 = B_132
      | k1_xboole_0 = A_131 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_185])).

tff(c_315,plain,
    ( k2_mcart_1('#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_300])).

tff(c_321,plain,(
    k2_mcart_1('#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_315])).

tff(c_24,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_76,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_24])).

tff(c_326,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_76])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3,D_19] :
      ( m1_subset_1('#skF_1'(A_1,B_2,C_3,D_19),A_1)
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_1,B_2,C_3))
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_19] :
      ( m1_subset_1('#skF_3'(A_1,B_2,C_3,D_19),C_3)
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_1,B_2,C_3))
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_1,B_2,C_3,D_19] :
      ( m1_subset_1('#skF_2'(A_1,B_2,C_3,D_19),B_2)
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_1,B_2,C_3))
      | k1_xboole_0 = C_3
      | k1_xboole_0 = B_2
      | k1_xboole_0 = A_1 ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    ! [H_60,F_54,G_58] :
      ( H_60 = '#skF_7'
      | k3_mcart_1(F_54,G_58,H_60) != '#skF_8'
      | ~ m1_subset_1(H_60,'#skF_6')
      | ~ m1_subset_1(G_58,'#skF_5')
      | ~ m1_subset_1(F_54,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_268,plain,(
    ! [A_123,B_124,C_125,D_126] :
      ( '#skF_3'(A_123,B_124,C_125,D_126) = '#skF_7'
      | D_126 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_123,B_124,C_125,D_126),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_123,B_124,C_125,D_126),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_123,B_124,C_125,D_126),'#skF_4')
      | ~ m1_subset_1(D_126,k3_zfmisc_1(A_123,B_124,C_125))
      | k1_xboole_0 = C_125
      | k1_xboole_0 = B_124
      | k1_xboole_0 = A_123 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_32])).

tff(c_272,plain,(
    ! [A_1,C_3,D_19] :
      ( '#skF_3'(A_1,'#skF_5',C_3,D_19) = '#skF_7'
      | D_19 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_1,'#skF_5',C_3,D_19),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_1,'#skF_5',C_3,D_19),'#skF_4')
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_1,'#skF_5',C_3))
      | k1_xboole_0 = C_3
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_6,c_268])).

tff(c_468,plain,(
    ! [A_180,C_181,D_182] :
      ( '#skF_3'(A_180,'#skF_5',C_181,D_182) = '#skF_7'
      | D_182 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_180,'#skF_5',C_181,D_182),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_180,'#skF_5',C_181,D_182),'#skF_4')
      | ~ m1_subset_1(D_182,k3_zfmisc_1(A_180,'#skF_5',C_181))
      | k1_xboole_0 = C_181
      | k1_xboole_0 = A_180 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_272])).

tff(c_472,plain,(
    ! [A_1,D_19] :
      ( '#skF_3'(A_1,'#skF_5','#skF_6',D_19) = '#skF_7'
      | D_19 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_1,'#skF_5','#skF_6',D_19),'#skF_4')
      | ~ m1_subset_1(D_19,k3_zfmisc_1(A_1,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_1 ) ),
    inference(resolution,[status(thm)],[c_4,c_468])).

tff(c_477,plain,(
    ! [A_183,D_184] :
      ( '#skF_3'(A_183,'#skF_5','#skF_6',D_184) = '#skF_7'
      | D_184 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_183,'#skF_5','#skF_6',D_184),'#skF_4')
      | ~ m1_subset_1(D_184,k3_zfmisc_1(A_183,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_183 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_26,c_472])).

tff(c_481,plain,(
    ! [D_19] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_19) = '#skF_7'
      | D_19 != '#skF_8'
      | ~ m1_subset_1(D_19,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_8,c_477])).

tff(c_486,plain,(
    ! [D_185] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_185) = '#skF_7'
      | D_185 != '#skF_8'
      | ~ m1_subset_1(D_185,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_30,c_481])).

tff(c_501,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34,c_486])).

tff(c_508,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_326,c_501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n024.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:17:36 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.81/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.40  
% 2.81/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.40  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.81/1.40  
% 2.81/1.40  %Foreground sorts:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Background operators:
% 2.81/1.40  
% 2.81/1.40  
% 2.81/1.40  %Foreground operators:
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.81/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.81/1.40  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.81/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.81/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.81/1.40  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.81/1.40  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.81/1.40  tff('#skF_8', type, '#skF_8': $i).
% 2.81/1.40  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.81/1.40  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.81/1.40  tff('#skF_4', type, '#skF_4': $i).
% 2.81/1.40  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.81/1.40  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.81/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.81/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.81/1.40  
% 2.81/1.41  tff(f_118, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 2.81/1.41  tff(f_50, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.81/1.41  tff(f_94, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.81/1.41  tff(f_74, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 2.81/1.41  tff(f_58, axiom, (![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 2.81/1.41  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.81/1.41  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.81/1.41  tff(c_26, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.81/1.41  tff(c_34, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.81/1.41  tff(c_223, plain, (![A_116, B_117, C_118, D_119]: (k3_mcart_1('#skF_1'(A_116, B_117, C_118, D_119), '#skF_2'(A_116, B_117, C_118, D_119), '#skF_3'(A_116, B_117, C_118, D_119))=D_119 | ~m1_subset_1(D_119, k3_zfmisc_1(A_116, B_117, C_118)) | k1_xboole_0=C_118 | k1_xboole_0=B_117 | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.41  tff(c_54, plain, (![A_94, B_95, C_96, D_97]: (k7_mcart_1(A_94, B_95, C_96, D_97)=k2_mcart_1(D_97) | ~m1_subset_1(D_97, k3_zfmisc_1(A_94, B_95, C_96)) | k1_xboole_0=C_96 | k1_xboole_0=B_95 | k1_xboole_0=A_94)), inference(cnfTransformation, [status(thm)], [f_94])).
% 2.81/1.41  tff(c_69, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.81/1.41  tff(c_75, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_69])).
% 2.81/1.41  tff(c_139, plain, (![A_106, B_107, C_108, D_109]: (k3_mcart_1(k5_mcart_1(A_106, B_107, C_108, D_109), k6_mcart_1(A_106, B_107, C_108, D_109), k7_mcart_1(A_106, B_107, C_108, D_109))=D_109 | ~m1_subset_1(D_109, k3_zfmisc_1(A_106, B_107, C_108)) | k1_xboole_0=C_108 | k1_xboole_0=B_107 | k1_xboole_0=A_106)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.81/1.41  tff(c_168, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_75, c_139])).
% 2.81/1.41  tff(c_172, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_168])).
% 2.81/1.41  tff(c_173, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_172])).
% 2.81/1.41  tff(c_10, plain, (![A_31, C_33, B_32, F_36, E_35, D_34]: (F_36=C_33 | k3_mcart_1(D_34, E_35, F_36)!=k3_mcart_1(A_31, B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.81/1.41  tff(c_185, plain, (![C_33, A_31, B_32]: (k2_mcart_1('#skF_8')=C_33 | k3_mcart_1(A_31, B_32, C_33)!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_173, c_10])).
% 2.81/1.41  tff(c_300, plain, (![A_131, B_132, C_133, D_134]: (k2_mcart_1('#skF_8')='#skF_3'(A_131, B_132, C_133, D_134) | D_134!='#skF_8' | ~m1_subset_1(D_134, k3_zfmisc_1(A_131, B_132, C_133)) | k1_xboole_0=C_133 | k1_xboole_0=B_132 | k1_xboole_0=A_131)), inference(superposition, [status(thm), theory('equality')], [c_223, c_185])).
% 2.81/1.41  tff(c_315, plain, (k2_mcart_1('#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_300])).
% 2.81/1.41  tff(c_321, plain, (k2_mcart_1('#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_315])).
% 2.81/1.41  tff(c_24, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.81/1.41  tff(c_76, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_24])).
% 2.81/1.41  tff(c_326, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_321, c_76])).
% 2.81/1.41  tff(c_8, plain, (![A_1, B_2, C_3, D_19]: (m1_subset_1('#skF_1'(A_1, B_2, C_3, D_19), A_1) | ~m1_subset_1(D_19, k3_zfmisc_1(A_1, B_2, C_3)) | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.41  tff(c_4, plain, (![A_1, B_2, C_3, D_19]: (m1_subset_1('#skF_3'(A_1, B_2, C_3, D_19), C_3) | ~m1_subset_1(D_19, k3_zfmisc_1(A_1, B_2, C_3)) | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.41  tff(c_6, plain, (![A_1, B_2, C_3, D_19]: (m1_subset_1('#skF_2'(A_1, B_2, C_3, D_19), B_2) | ~m1_subset_1(D_19, k3_zfmisc_1(A_1, B_2, C_3)) | k1_xboole_0=C_3 | k1_xboole_0=B_2 | k1_xboole_0=A_1)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.81/1.41  tff(c_32, plain, (![H_60, F_54, G_58]: (H_60='#skF_7' | k3_mcart_1(F_54, G_58, H_60)!='#skF_8' | ~m1_subset_1(H_60, '#skF_6') | ~m1_subset_1(G_58, '#skF_5') | ~m1_subset_1(F_54, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 2.81/1.41  tff(c_268, plain, (![A_123, B_124, C_125, D_126]: ('#skF_3'(A_123, B_124, C_125, D_126)='#skF_7' | D_126!='#skF_8' | ~m1_subset_1('#skF_3'(A_123, B_124, C_125, D_126), '#skF_6') | ~m1_subset_1('#skF_2'(A_123, B_124, C_125, D_126), '#skF_5') | ~m1_subset_1('#skF_1'(A_123, B_124, C_125, D_126), '#skF_4') | ~m1_subset_1(D_126, k3_zfmisc_1(A_123, B_124, C_125)) | k1_xboole_0=C_125 | k1_xboole_0=B_124 | k1_xboole_0=A_123)), inference(superposition, [status(thm), theory('equality')], [c_223, c_32])).
% 2.81/1.41  tff(c_272, plain, (![A_1, C_3, D_19]: ('#skF_3'(A_1, '#skF_5', C_3, D_19)='#skF_7' | D_19!='#skF_8' | ~m1_subset_1('#skF_3'(A_1, '#skF_5', C_3, D_19), '#skF_6') | ~m1_subset_1('#skF_1'(A_1, '#skF_5', C_3, D_19), '#skF_4') | ~m1_subset_1(D_19, k3_zfmisc_1(A_1, '#skF_5', C_3)) | k1_xboole_0=C_3 | k1_xboole_0='#skF_5' | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_6, c_268])).
% 2.81/1.41  tff(c_468, plain, (![A_180, C_181, D_182]: ('#skF_3'(A_180, '#skF_5', C_181, D_182)='#skF_7' | D_182!='#skF_8' | ~m1_subset_1('#skF_3'(A_180, '#skF_5', C_181, D_182), '#skF_6') | ~m1_subset_1('#skF_1'(A_180, '#skF_5', C_181, D_182), '#skF_4') | ~m1_subset_1(D_182, k3_zfmisc_1(A_180, '#skF_5', C_181)) | k1_xboole_0=C_181 | k1_xboole_0=A_180)), inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_272])).
% 2.81/1.41  tff(c_472, plain, (![A_1, D_19]: ('#skF_3'(A_1, '#skF_5', '#skF_6', D_19)='#skF_7' | D_19!='#skF_8' | ~m1_subset_1('#skF_1'(A_1, '#skF_5', '#skF_6', D_19), '#skF_4') | ~m1_subset_1(D_19, k3_zfmisc_1(A_1, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_1)), inference(resolution, [status(thm)], [c_4, c_468])).
% 2.81/1.41  tff(c_477, plain, (![A_183, D_184]: ('#skF_3'(A_183, '#skF_5', '#skF_6', D_184)='#skF_7' | D_184!='#skF_8' | ~m1_subset_1('#skF_1'(A_183, '#skF_5', '#skF_6', D_184), '#skF_4') | ~m1_subset_1(D_184, k3_zfmisc_1(A_183, '#skF_5', '#skF_6')) | k1_xboole_0=A_183)), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_26, c_472])).
% 2.81/1.41  tff(c_481, plain, (![D_19]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_19)='#skF_7' | D_19!='#skF_8' | ~m1_subset_1(D_19, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_8, c_477])).
% 2.81/1.41  tff(c_486, plain, (![D_185]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_185)='#skF_7' | D_185!='#skF_8' | ~m1_subset_1(D_185, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_30, c_481])).
% 2.81/1.41  tff(c_501, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_34, c_486])).
% 2.81/1.41  tff(c_508, plain, $false, inference(negUnitSimplification, [status(thm)], [c_326, c_501])).
% 2.81/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.81/1.41  
% 2.81/1.41  Inference rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Ref     : 9
% 2.81/1.41  #Sup     : 107
% 2.81/1.41  #Fact    : 0
% 2.81/1.41  #Define  : 0
% 2.81/1.41  #Split   : 1
% 2.81/1.41  #Chain   : 0
% 2.81/1.41  #Close   : 0
% 2.81/1.41  
% 2.81/1.41  Ordering : KBO
% 2.81/1.41  
% 2.81/1.41  Simplification rules
% 2.81/1.41  ----------------------
% 2.81/1.41  #Subsume      : 16
% 2.81/1.41  #Demod        : 11
% 2.81/1.41  #Tautology    : 29
% 2.81/1.41  #SimpNegUnit  : 13
% 2.81/1.41  #BackRed      : 7
% 2.81/1.41  
% 2.81/1.41  #Partial instantiations: 0
% 2.81/1.41  #Strategies tried      : 1
% 2.81/1.41  
% 2.81/1.41  Timing (in seconds)
% 2.81/1.41  ----------------------
% 2.81/1.42  Preprocessing        : 0.32
% 2.81/1.42  Parsing              : 0.17
% 2.81/1.42  CNF conversion       : 0.03
% 2.81/1.42  Main loop            : 0.32
% 2.81/1.42  Inferencing          : 0.12
% 2.81/1.42  Reduction            : 0.07
% 2.81/1.42  Demodulation         : 0.04
% 2.81/1.42  BG Simplification    : 0.02
% 2.81/1.42  Subsumption          : 0.07
% 2.81/1.42  Abstraction          : 0.02
% 2.81/1.42  MUC search           : 0.00
% 2.81/1.42  Cooper               : 0.00
% 2.81/1.42  Total                : 0.66
% 2.81/1.42  Index Insertion      : 0.00
% 2.81/1.42  Index Deletion       : 0.00
% 2.81/1.42  Index Matching       : 0.00
% 2.81/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
