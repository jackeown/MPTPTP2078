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
% DateTime   : Thu Dec  3 10:10:06 EST 2020

% Result     : Theorem 2.96s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   57 (  95 expanded)
%              Number of leaves         :   27 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :  130 ( 371 expanded)
%              Number of equality atoms :   91 ( 237 expanded)
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
                       => D = H ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k7_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l44_mcart_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_78,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_mcart_1)).

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

tff(c_239,plain,(
    ! [A_109,B_110,C_111,D_112] :
      ( k3_mcart_1('#skF_1'(A_109,B_110,C_111,D_112),'#skF_2'(A_109,B_110,C_111,D_112),'#skF_3'(A_109,B_110,C_111,D_112)) = D_112
      | ~ m1_subset_1(D_112,k3_zfmisc_1(A_109,B_110,C_111))
      | k1_xboole_0 = C_111
      | k1_xboole_0 = B_110
      | k1_xboole_0 = A_109 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_53,plain,(
    ! [A_62,B_63,C_64] : k4_tarski(k4_tarski(A_62,B_63),C_64) = k3_mcart_1(A_62,B_63,C_64) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_42,B_43] : k2_mcart_1(k4_tarski(A_42,B_43)) = B_43 ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_62,plain,(
    ! [A_62,B_63,C_64] : k2_mcart_1(k3_mcart_1(A_62,B_63,C_64)) = C_64 ),
    inference(superposition,[status(thm),theory(equality)],[c_53,c_22])).

tff(c_260,plain,(
    ! [D_113,A_114,B_115,C_116] :
      ( k2_mcart_1(D_113) = '#skF_3'(A_114,B_115,C_116,D_113)
      | ~ m1_subset_1(D_113,k3_zfmisc_1(A_114,B_115,C_116))
      | k1_xboole_0 = C_116
      | k1_xboole_0 = B_115
      | k1_xboole_0 = A_114 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_62])).

tff(c_278,plain,
    ( k2_mcart_1('#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_260])).

tff(c_284,plain,(
    k2_mcart_1('#skF_8') = '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_278])).

tff(c_147,plain,(
    ! [A_89,B_90,C_91,D_92] :
      ( k7_mcart_1(A_89,B_90,C_91,D_92) = k2_mcart_1(D_92)
      | ~ m1_subset_1(D_92,k3_zfmisc_1(A_89,B_90,C_91))
      | k1_xboole_0 = C_91
      | k1_xboole_0 = B_90
      | k1_xboole_0 = A_89 ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_157,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_34,c_147])).

tff(c_161,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_157])).

tff(c_24,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_162,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_161,c_24])).

tff(c_285,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_162])).

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
    ! [H_57,F_51,G_55] :
      ( H_57 = '#skF_7'
      | k3_mcart_1(F_51,G_55,H_57) != '#skF_8'
      | ~ m1_subset_1(H_57,'#skF_6')
      | ~ m1_subset_1(G_55,'#skF_5')
      | ~ m1_subset_1(F_51,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_372,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( '#skF_3'(A_134,B_135,C_136,D_137) = '#skF_7'
      | D_137 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_134,B_135,C_136,D_137),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_134,B_135,C_136,D_137),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_134,B_135,C_136,D_137),'#skF_4')
      | ~ m1_subset_1(D_137,k3_zfmisc_1(A_134,B_135,C_136))
      | k1_xboole_0 = C_136
      | k1_xboole_0 = B_135
      | k1_xboole_0 = A_134 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_239,c_32])).

tff(c_376,plain,(
    ! [A_7,C_9,D_25] :
      ( '#skF_3'(A_7,'#skF_5',C_9,D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_7,'#skF_5',C_9,D_25),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5',C_9,D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5',C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_10,c_372])).

tff(c_615,plain,(
    ! [A_184,C_185,D_186] :
      ( '#skF_3'(A_184,'#skF_5',C_185,D_186) = '#skF_7'
      | D_186 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_184,'#skF_5',C_185,D_186),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_184,'#skF_5',C_185,D_186),'#skF_4')
      | ~ m1_subset_1(D_186,k3_zfmisc_1(A_184,'#skF_5',C_185))
      | k1_xboole_0 = C_185
      | k1_xboole_0 = A_184 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_28,c_376])).

tff(c_619,plain,(
    ! [A_7,D_25] :
      ( '#skF_3'(A_7,'#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5','#skF_6',D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_8,c_615])).

tff(c_624,plain,(
    ! [A_187,D_188] :
      ( '#skF_3'(A_187,'#skF_5','#skF_6',D_188) = '#skF_7'
      | D_188 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_187,'#skF_5','#skF_6',D_188),'#skF_4')
      | ~ m1_subset_1(D_188,k3_zfmisc_1(A_187,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_187 ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_26,c_26,c_619])).

tff(c_628,plain,(
    ! [D_25] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1(D_25,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12,c_624])).

tff(c_633,plain,(
    ! [D_189] :
      ( '#skF_3'('#skF_4','#skF_5','#skF_6',D_189) = '#skF_7'
      | D_189 != '#skF_8'
      | ~ m1_subset_1(D_189,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_26,c_30,c_628])).

tff(c_648,plain,(
    '#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_34,c_633])).

tff(c_655,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_285,c_648])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.96/1.54  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.54  
% 3.15/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.55  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 3.15/1.55  
% 3.15/1.55  %Foreground sorts:
% 3.15/1.55  
% 3.15/1.55  
% 3.15/1.55  %Background operators:
% 3.15/1.55  
% 3.15/1.55  
% 3.15/1.55  %Foreground operators:
% 3.15/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.55  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.15/1.55  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.55  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.15/1.55  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.55  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.15/1.55  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.55  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.15/1.55  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.15/1.55  tff('#skF_8', type, '#skF_8': $i).
% 3.15/1.55  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.15/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.55  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.15/1.55  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.15/1.55  tff('#skF_4', type, '#skF_4': $i).
% 3.15/1.55  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.15/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.55  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.15/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.15/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.15/1.55  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.15/1.55  
% 3.15/1.56  tff(f_102, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 3.15/1.56  tff(f_54, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 3.15/1.56  tff(f_27, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.15/1.56  tff(f_78, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 3.15/1.56  tff(f_74, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.15/1.56  tff(c_30, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.56  tff(c_28, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.56  tff(c_26, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.56  tff(c_34, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.56  tff(c_239, plain, (![A_109, B_110, C_111, D_112]: (k3_mcart_1('#skF_1'(A_109, B_110, C_111, D_112), '#skF_2'(A_109, B_110, C_111, D_112), '#skF_3'(A_109, B_110, C_111, D_112))=D_112 | ~m1_subset_1(D_112, k3_zfmisc_1(A_109, B_110, C_111)) | k1_xboole_0=C_111 | k1_xboole_0=B_110 | k1_xboole_0=A_109)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.56  tff(c_53, plain, (![A_62, B_63, C_64]: (k4_tarski(k4_tarski(A_62, B_63), C_64)=k3_mcart_1(A_62, B_63, C_64))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.56  tff(c_22, plain, (![A_42, B_43]: (k2_mcart_1(k4_tarski(A_42, B_43))=B_43)), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.15/1.56  tff(c_62, plain, (![A_62, B_63, C_64]: (k2_mcart_1(k3_mcart_1(A_62, B_63, C_64))=C_64)), inference(superposition, [status(thm), theory('equality')], [c_53, c_22])).
% 3.15/1.56  tff(c_260, plain, (![D_113, A_114, B_115, C_116]: (k2_mcart_1(D_113)='#skF_3'(A_114, B_115, C_116, D_113) | ~m1_subset_1(D_113, k3_zfmisc_1(A_114, B_115, C_116)) | k1_xboole_0=C_116 | k1_xboole_0=B_115 | k1_xboole_0=A_114)), inference(superposition, [status(thm), theory('equality')], [c_239, c_62])).
% 3.15/1.56  tff(c_278, plain, (k2_mcart_1('#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_260])).
% 3.15/1.56  tff(c_284, plain, (k2_mcart_1('#skF_8')='#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_278])).
% 3.15/1.56  tff(c_147, plain, (![A_89, B_90, C_91, D_92]: (k7_mcart_1(A_89, B_90, C_91, D_92)=k2_mcart_1(D_92) | ~m1_subset_1(D_92, k3_zfmisc_1(A_89, B_90, C_91)) | k1_xboole_0=C_91 | k1_xboole_0=B_90 | k1_xboole_0=A_89)), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.15/1.56  tff(c_157, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_34, c_147])).
% 3.15/1.56  tff(c_161, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_157])).
% 3.15/1.56  tff(c_24, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.56  tff(c_162, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_161, c_24])).
% 3.15/1.56  tff(c_285, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_284, c_162])).
% 3.15/1.56  tff(c_12, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_1'(A_7, B_8, C_9, D_25), A_7) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.56  tff(c_8, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_3'(A_7, B_8, C_9, D_25), C_9) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.56  tff(c_10, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_2'(A_7, B_8, C_9, D_25), B_8) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.15/1.56  tff(c_32, plain, (![H_57, F_51, G_55]: (H_57='#skF_7' | k3_mcart_1(F_51, G_55, H_57)!='#skF_8' | ~m1_subset_1(H_57, '#skF_6') | ~m1_subset_1(G_55, '#skF_5') | ~m1_subset_1(F_51, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.15/1.56  tff(c_372, plain, (![A_134, B_135, C_136, D_137]: ('#skF_3'(A_134, B_135, C_136, D_137)='#skF_7' | D_137!='#skF_8' | ~m1_subset_1('#skF_3'(A_134, B_135, C_136, D_137), '#skF_6') | ~m1_subset_1('#skF_2'(A_134, B_135, C_136, D_137), '#skF_5') | ~m1_subset_1('#skF_1'(A_134, B_135, C_136, D_137), '#skF_4') | ~m1_subset_1(D_137, k3_zfmisc_1(A_134, B_135, C_136)) | k1_xboole_0=C_136 | k1_xboole_0=B_135 | k1_xboole_0=A_134)), inference(superposition, [status(thm), theory('equality')], [c_239, c_32])).
% 3.15/1.56  tff(c_376, plain, (![A_7, C_9, D_25]: ('#skF_3'(A_7, '#skF_5', C_9, D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_3'(A_7, '#skF_5', C_9, D_25), '#skF_6') | ~m1_subset_1('#skF_1'(A_7, '#skF_5', C_9, D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', C_9)) | k1_xboole_0=C_9 | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_10, c_372])).
% 3.15/1.56  tff(c_615, plain, (![A_184, C_185, D_186]: ('#skF_3'(A_184, '#skF_5', C_185, D_186)='#skF_7' | D_186!='#skF_8' | ~m1_subset_1('#skF_3'(A_184, '#skF_5', C_185, D_186), '#skF_6') | ~m1_subset_1('#skF_1'(A_184, '#skF_5', C_185, D_186), '#skF_4') | ~m1_subset_1(D_186, k3_zfmisc_1(A_184, '#skF_5', C_185)) | k1_xboole_0=C_185 | k1_xboole_0=A_184)), inference(negUnitSimplification, [status(thm)], [c_28, c_28, c_376])).
% 3.15/1.56  tff(c_619, plain, (![A_7, D_25]: ('#skF_3'(A_7, '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_1'(A_7, '#skF_5', '#skF_6', D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_8, c_615])).
% 3.15/1.56  tff(c_624, plain, (![A_187, D_188]: ('#skF_3'(A_187, '#skF_5', '#skF_6', D_188)='#skF_7' | D_188!='#skF_8' | ~m1_subset_1('#skF_1'(A_187, '#skF_5', '#skF_6', D_188), '#skF_4') | ~m1_subset_1(D_188, k3_zfmisc_1(A_187, '#skF_5', '#skF_6')) | k1_xboole_0=A_187)), inference(negUnitSimplification, [status(thm)], [c_28, c_26, c_26, c_619])).
% 3.15/1.56  tff(c_628, plain, (![D_25]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1(D_25, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_12, c_624])).
% 3.15/1.56  tff(c_633, plain, (![D_189]: ('#skF_3'('#skF_4', '#skF_5', '#skF_6', D_189)='#skF_7' | D_189!='#skF_8' | ~m1_subset_1(D_189, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_26, c_30, c_628])).
% 3.15/1.56  tff(c_648, plain, ('#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_34, c_633])).
% 3.15/1.56  tff(c_655, plain, $false, inference(negUnitSimplification, [status(thm)], [c_285, c_648])).
% 3.15/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.56  
% 3.15/1.56  Inference rules
% 3.15/1.56  ----------------------
% 3.15/1.56  #Ref     : 0
% 3.15/1.56  #Sup     : 141
% 3.15/1.56  #Fact    : 0
% 3.15/1.56  #Define  : 0
% 3.15/1.56  #Split   : 0
% 3.15/1.56  #Chain   : 0
% 3.15/1.56  #Close   : 0
% 3.15/1.56  
% 3.15/1.56  Ordering : KBO
% 3.15/1.56  
% 3.15/1.56  Simplification rules
% 3.15/1.56  ----------------------
% 3.15/1.56  #Subsume      : 9
% 3.15/1.56  #Demod        : 51
% 3.15/1.56  #Tautology    : 51
% 3.15/1.56  #SimpNegUnit  : 10
% 3.15/1.56  #BackRed      : 5
% 3.15/1.56  
% 3.15/1.56  #Partial instantiations: 0
% 3.15/1.56  #Strategies tried      : 1
% 3.15/1.56  
% 3.15/1.56  Timing (in seconds)
% 3.15/1.56  ----------------------
% 3.15/1.56  Preprocessing        : 0.32
% 3.15/1.56  Parsing              : 0.15
% 3.15/1.56  CNF conversion       : 0.03
% 3.15/1.56  Main loop            : 0.41
% 3.15/1.56  Inferencing          : 0.17
% 3.15/1.56  Reduction            : 0.11
% 3.15/1.56  Demodulation         : 0.08
% 3.15/1.56  BG Simplification    : 0.03
% 3.15/1.56  Subsumption          : 0.07
% 3.15/1.56  Abstraction          : 0.04
% 3.15/1.56  MUC search           : 0.00
% 3.15/1.56  Cooper               : 0.00
% 3.15/1.56  Total                : 0.77
% 3.15/1.56  Index Insertion      : 0.00
% 3.15/1.56  Index Deletion       : 0.00
% 3.15/1.56  Index Matching       : 0.00
% 3.15/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
