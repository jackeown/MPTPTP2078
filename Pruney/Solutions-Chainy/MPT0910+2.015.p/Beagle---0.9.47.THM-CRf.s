%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:01 EST 2020

% Result     : Theorem 2.59s
% Output     : CNFRefutation 2.71s
% Verified   : 
% Statistics : Number of formulae       :   59 (  98 expanded)
%              Number of leaves         :   27 (  51 expanded)
%              Depth                    :   10
%              Number of atoms          :  139 ( 382 expanded)
%              Number of equality atoms :   99 ( 247 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = G ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k6_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_mcart_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => ( k5_mcart_1(A,B,C,D) = k1_mcart_1(k1_mcart_1(D))
                & k6_mcart_1(A,B,C,D) = k2_mcart_1(k1_mcart_1(D))
                & k7_mcart_1(A,B,C,D) = k2_mcart_1(D) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_mcart_1)).

tff(f_54,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_34,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_182,plain,(
    ! [A_105,B_106,C_107,D_108] :
      ( k6_mcart_1(A_105,B_106,C_107,D_108) = k2_mcart_1(k1_mcart_1(D_108))
      | ~ m1_subset_1(D_108,k3_zfmisc_1(A_105,B_106,C_107))
      | k1_xboole_0 = C_107
      | k1_xboole_0 = B_106
      | k1_xboole_0 = A_105 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_200,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_182])).

tff(c_206,plain,(
    k2_mcart_1(k1_mcart_1('#skF_8')) = k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_200])).

tff(c_242,plain,(
    ! [A_113,B_114,C_115,D_116] :
      ( k3_mcart_1('#skF_1'(A_113,B_114,C_115,D_116),'#skF_2'(A_113,B_114,C_115,D_116),'#skF_3'(A_113,B_114,C_115,D_116)) = D_116
      | ~ m1_subset_1(D_116,k3_zfmisc_1(A_113,B_114,C_115))
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_114
      | k1_xboole_0 = A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    ! [A_62,B_63,C_64] : k4_tarski(k4_tarski(A_62,B_63),C_64) = k3_mcart_1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_42,B_43] : k1_mcart_1(k4_tarski(A_42,B_43)) = A_42 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_65,plain,(
    ! [A_62,B_63,C_64] : k1_mcart_1(k3_mcart_1(A_62,B_63,C_64)) = k4_tarski(A_62,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_20])).

tff(c_311,plain,(
    ! [A_125,B_126,C_127,D_128] :
      ( k4_tarski('#skF_1'(A_125,B_126,C_127,D_128),'#skF_2'(A_125,B_126,C_127,D_128)) = k1_mcart_1(D_128)
      | ~ m1_subset_1(D_128,k3_zfmisc_1(A_125,B_126,C_127))
      | k1_xboole_0 = C_127
      | k1_xboole_0 = B_126
      | k1_xboole_0 = A_125 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_65])).

tff(c_22,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_332,plain,(
    ! [D_129,A_130,B_131,C_132] :
      ( k2_mcart_1(k1_mcart_1(D_129)) = '#skF_2'(A_130,B_131,C_132,D_129)
      | ~ m1_subset_1(D_129,k3_zfmisc_1(A_130,B_131,C_132))
      | k1_xboole_0 = C_132
      | k1_xboole_0 = B_131
      | k1_xboole_0 = A_130 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_22])).

tff(c_350,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_8')) = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_332])).

tff(c_355,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_206,c_350])).

tff(c_356,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_355])).

tff(c_24,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_358,plain,(
    '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_356,c_24])).

tff(c_12,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_1'(A_7,B_8,C_9,D_25),A_7)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_3'(A_7,B_8,C_9,D_25),C_9)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( m1_subset_1('#skF_2'(A_7,B_8,C_9,D_25),B_8)
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_32,plain,(
    ! [G_55,F_51,H_57] :
      ( G_55 = '#skF_7'
      | k3_mcart_1(F_51,G_55,H_57) != '#skF_8'
      | ~ m1_subset_1(H_57,'#skF_6')
      | ~ m1_subset_1(G_55,'#skF_5')
      | ~ m1_subset_1(F_51,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_296,plain,(
    ! [A_121,B_122,C_123,D_124] :
      ( '#skF_2'(A_121,B_122,C_123,D_124) = '#skF_7'
      | D_124 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_121,B_122,C_123,D_124),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_121,B_122,C_123,D_124),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_121,B_122,C_123,D_124),'#skF_4')
      | ~ m1_subset_1(D_124,k3_zfmisc_1(A_121,B_122,C_123))
      | k1_xboole_0 = C_123
      | k1_xboole_0 = B_122
      | k1_xboole_0 = A_121 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_32])).

tff(c_300,plain,(
    ! [A_7,C_9,D_25] :
      ( '#skF_2'(A_7,'#skF_5',C_9,D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_7,'#skF_5',C_9,D_25),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5',C_9,D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5',C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_10,c_296])).

tff(c_417,plain,(
    ! [A_143,C_144,D_145] :
      ( '#skF_2'(A_143,'#skF_5',C_144,D_145) = '#skF_7'
      | D_145 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_143,'#skF_5',C_144,D_145),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_143,'#skF_5',C_144,D_145),'#skF_4')
      | ~ m1_subset_1(D_145,k3_zfmisc_1(A_143,'#skF_5',C_144))
      | k1_xboole_0 = C_144
      | k1_xboole_0 = A_143 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_300])).

tff(c_421,plain,(
    ! [A_7,D_25] :
      ( '#skF_2'(A_7,'#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5','#skF_6',D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_8,c_417])).

tff(c_430,plain,(
    ! [A_146,D_147] :
      ( '#skF_2'(A_146,'#skF_5','#skF_6',D_147) = '#skF_7'
      | D_147 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_146,'#skF_5','#skF_6',D_147),'#skF_4')
      | ~ m1_subset_1(D_147,k3_zfmisc_1(A_146,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_146 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_26,c_421])).

tff(c_434,plain,(
    ! [D_25] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1(D_25,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12,c_430])).

tff(c_439,plain,(
    ! [D_148] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_148) = '#skF_7'
      | D_148 != '#skF_8'
      | ~ m1_subset_1(D_148,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_30,c_434])).

tff(c_454,plain,(
    '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34,c_439])).

tff(c_461,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_454])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:28:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.59/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  
% 2.59/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.59/1.35  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.59/1.35  
% 2.59/1.35  %Foreground sorts:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Background operators:
% 2.59/1.35  
% 2.59/1.35  
% 2.59/1.35  %Foreground operators:
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.59/1.35  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.59/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.59/1.35  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.59/1.35  tff('#skF_7', type, '#skF_7': $i).
% 2.59/1.35  tff('#skF_5', type, '#skF_5': $i).
% 2.59/1.35  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.59/1.35  tff('#skF_6', type, '#skF_6': $i).
% 2.59/1.35  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.59/1.35  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.59/1.35  tff('#skF_8', type, '#skF_8': $i).
% 2.59/1.35  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.59/1.35  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.59/1.35  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.59/1.35  tff('#skF_4', type, '#skF_4': $i).
% 2.59/1.35  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.59/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.59/1.35  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.59/1.35  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.59/1.35  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.59/1.35  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.59/1.35  
% 2.71/1.37  tff(f_102, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_mcart_1)).
% 2.71/1.37  tff(f_74, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 2.71/1.37  tff(f_54, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l44_mcart_1)).
% 2.71/1.37  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_mcart_1)).
% 2.71/1.37  tff(f_78, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.71/1.37  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.71/1.37  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.71/1.37  tff(c_26, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.71/1.37  tff(c_34, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.71/1.37  tff(c_182, plain, (![A_105, B_106, C_107, D_108]: (k6_mcart_1(A_105, B_106, C_107, D_108)=k2_mcart_1(k1_mcart_1(D_108)) | ~m1_subset_1(D_108, k3_zfmisc_1(A_105, B_106, C_107)) | k1_xboole_0=C_107 | k1_xboole_0=B_106 | k1_xboole_0=A_105)), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.71/1.37  tff(c_200, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_182])).
% 2.71/1.37  tff(c_206, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))=k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_200])).
% 2.71/1.37  tff(c_242, plain, (![A_113, B_114, C_115, D_116]: (k3_mcart_1('#skF_1'(A_113, B_114, C_115, D_116), '#skF_2'(A_113, B_114, C_115, D_116), '#skF_3'(A_113, B_114, C_115, D_116))=D_116 | ~m1_subset_1(D_116, k3_zfmisc_1(A_113, B_114, C_115)) | k1_xboole_0=C_115 | k1_xboole_0=B_114 | k1_xboole_0=A_113)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.37  tff(c_53, plain, (![A_62, B_63, C_64]: (k4_tarski(k4_tarski(A_62, B_63), C_64)=k3_mcart_1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.71/1.37  tff(c_20, plain, (![A_42, B_43]: (k1_mcart_1(k4_tarski(A_42, B_43))=A_42)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.37  tff(c_65, plain, (![A_62, B_63, C_64]: (k1_mcart_1(k3_mcart_1(A_62, B_63, C_64))=k4_tarski(A_62, B_63))), inference(superposition, [status(thm), theory('equality')], [c_53, c_20])).
% 2.71/1.37  tff(c_311, plain, (![A_125, B_126, C_127, D_128]: (k4_tarski('#skF_1'(A_125, B_126, C_127, D_128), '#skF_2'(A_125, B_126, C_127, D_128))=k1_mcart_1(D_128) | ~m1_subset_1(D_128, k3_zfmisc_1(A_125, B_126, C_127)) | k1_xboole_0=C_127 | k1_xboole_0=B_126 | k1_xboole_0=A_125)), inference(superposition, [status(thm), theory('equality')], [c_242, c_65])).
% 2.71/1.37  tff(c_22, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.71/1.37  tff(c_332, plain, (![D_129, A_130, B_131, C_132]: (k2_mcart_1(k1_mcart_1(D_129))='#skF_2'(A_130, B_131, C_132, D_129) | ~m1_subset_1(D_129, k3_zfmisc_1(A_130, B_131, C_132)) | k1_xboole_0=C_132 | k1_xboole_0=B_131 | k1_xboole_0=A_130)), inference(superposition, [status(thm), theory('equality')], [c_311, c_22])).
% 2.71/1.37  tff(c_350, plain, (k2_mcart_1(k1_mcart_1('#skF_8'))='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_332])).
% 2.71/1.37  tff(c_355, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_206, c_350])).
% 2.71/1.37  tff(c_356, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_355])).
% 2.71/1.37  tff(c_24, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.71/1.37  tff(c_358, plain, ('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_356, c_24])).
% 2.71/1.37  tff(c_12, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_1'(A_7, B_8, C_9, D_25), A_7) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.37  tff(c_8, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_3'(A_7, B_8, C_9, D_25), C_9) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.37  tff(c_10, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_2'(A_7, B_8, C_9, D_25), B_8) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.71/1.37  tff(c_32, plain, (![G_55, F_51, H_57]: (G_55='#skF_7' | k3_mcart_1(F_51, G_55, H_57)!='#skF_8' | ~m1_subset_1(H_57, '#skF_6') | ~m1_subset_1(G_55, '#skF_5') | ~m1_subset_1(F_51, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.71/1.37  tff(c_296, plain, (![A_121, B_122, C_123, D_124]: ('#skF_2'(A_121, B_122, C_123, D_124)='#skF_7' | D_124!='#skF_8' | ~m1_subset_1('#skF_3'(A_121, B_122, C_123, D_124), '#skF_6') | ~m1_subset_1('#skF_2'(A_121, B_122, C_123, D_124), '#skF_5') | ~m1_subset_1('#skF_1'(A_121, B_122, C_123, D_124), '#skF_4') | ~m1_subset_1(D_124, k3_zfmisc_1(A_121, B_122, C_123)) | k1_xboole_0=C_123 | k1_xboole_0=B_122 | k1_xboole_0=A_121)), inference(superposition, [status(thm), theory('equality')], [c_242, c_32])).
% 2.71/1.37  tff(c_300, plain, (![A_7, C_9, D_25]: ('#skF_2'(A_7, '#skF_5', C_9, D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_3'(A_7, '#skF_5', C_9, D_25), '#skF_6') | ~m1_subset_1('#skF_1'(A_7, '#skF_5', C_9, D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', C_9)) | k1_xboole_0=C_9 | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_10, c_296])).
% 2.71/1.37  tff(c_417, plain, (![A_143, C_144, D_145]: ('#skF_2'(A_143, '#skF_5', C_144, D_145)='#skF_7' | D_145!='#skF_8' | ~m1_subset_1('#skF_3'(A_143, '#skF_5', C_144, D_145), '#skF_6') | ~m1_subset_1('#skF_1'(A_143, '#skF_5', C_144, D_145), '#skF_4') | ~m1_subset_1(D_145, k3_zfmisc_1(A_143, '#skF_5', C_144)) | k1_xboole_0=C_144 | k1_xboole_0=A_143)), inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_300])).
% 2.71/1.37  tff(c_421, plain, (![A_7, D_25]: ('#skF_2'(A_7, '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_1'(A_7, '#skF_5', '#skF_6', D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_8, c_417])).
% 2.71/1.37  tff(c_430, plain, (![A_146, D_147]: ('#skF_2'(A_146, '#skF_5', '#skF_6', D_147)='#skF_7' | D_147!='#skF_8' | ~m1_subset_1('#skF_1'(A_146, '#skF_5', '#skF_6', D_147), '#skF_4') | ~m1_subset_1(D_147, k3_zfmisc_1(A_146, '#skF_5', '#skF_6')) | k1_xboole_0=A_146)), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_26, c_421])).
% 2.71/1.37  tff(c_434, plain, (![D_25]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1(D_25, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_12, c_430])).
% 2.71/1.37  tff(c_439, plain, (![D_148]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_148)='#skF_7' | D_148!='#skF_8' | ~m1_subset_1(D_148, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_30, c_434])).
% 2.71/1.37  tff(c_454, plain, ('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_34, c_439])).
% 2.71/1.37  tff(c_461, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_454])).
% 2.71/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.71/1.37  
% 2.71/1.37  Inference rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Ref     : 0
% 2.71/1.37  #Sup     : 100
% 2.71/1.37  #Fact    : 0
% 2.71/1.37  #Define  : 0
% 2.71/1.37  #Split   : 0
% 2.71/1.37  #Chain   : 0
% 2.71/1.37  #Close   : 0
% 2.71/1.37  
% 2.71/1.37  Ordering : KBO
% 2.71/1.37  
% 2.71/1.37  Simplification rules
% 2.71/1.37  ----------------------
% 2.71/1.37  #Subsume      : 1
% 2.71/1.37  #Demod        : 20
% 2.71/1.37  #Tautology    : 44
% 2.71/1.37  #SimpNegUnit  : 10
% 2.71/1.37  #BackRed      : 4
% 2.71/1.37  
% 2.71/1.37  #Partial instantiations: 0
% 2.71/1.37  #Strategies tried      : 1
% 2.71/1.37  
% 2.71/1.37  Timing (in seconds)
% 2.71/1.37  ----------------------
% 2.71/1.37  Preprocessing        : 0.31
% 2.71/1.37  Parsing              : 0.16
% 2.71/1.37  CNF conversion       : 0.02
% 2.71/1.37  Main loop            : 0.31
% 2.71/1.37  Inferencing          : 0.13
% 2.71/1.37  Reduction            : 0.08
% 2.71/1.37  Demodulation         : 0.06
% 2.71/1.37  BG Simplification    : 0.03
% 2.71/1.37  Subsumption          : 0.05
% 2.71/1.37  Abstraction          : 0.03
% 2.71/1.37  MUC search           : 0.00
% 2.71/1.37  Cooper               : 0.00
% 2.71/1.37  Total                : 0.65
% 2.71/1.37  Index Insertion      : 0.00
% 2.71/1.37  Index Deletion       : 0.00
% 2.71/1.37  Index Matching       : 0.00
% 2.71/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
