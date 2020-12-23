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
% DateTime   : Thu Dec  3 10:10:01 EST 2020

% Result     : Theorem 2.95s
% Output     : CNFRefutation 3.05s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 140 expanded)
%              Number of leaves         :   25 (  68 expanded)
%              Depth                    :   16
%              Number of atoms          :  137 ( 663 expanded)
%              Number of equality atoms :   95 ( 417 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

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

tff(f_121,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_mcart_1)).

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

tff(f_77,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ? [D] :
            ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
            & ? [E,F,G] :
                ( D = k3_mcart_1(E,F,G)
                & ~ ( k5_mcart_1(A,B,C,D) = E
                    & k6_mcart_1(A,B,C,D) = F
                    & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_mcart_1)).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_26,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_36,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

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

tff(c_222,plain,(
    ! [A_136,B_137,C_138,D_139] :
      ( k3_mcart_1('#skF_1'(A_136,B_137,C_138,D_139),'#skF_2'(A_136,B_137,C_138,D_139),'#skF_3'(A_136,B_137,C_138,D_139)) = D_139
      | ~ m1_subset_1(D_139,k3_zfmisc_1(A_136,B_137,C_138))
      | k1_xboole_0 = C_138
      | k1_xboole_0 = B_137
      | k1_xboole_0 = A_136 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_34,plain,(
    ! [G_70,F_66,H_72] :
      ( G_70 = '#skF_7'
      | k3_mcart_1(F_66,G_70,H_72) != '#skF_8'
      | ~ m1_subset_1(H_72,'#skF_6')
      | ~ m1_subset_1(G_70,'#skF_5')
      | ~ m1_subset_1(F_66,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_308,plain,(
    ! [A_155,B_156,C_157,D_158] :
      ( '#skF_2'(A_155,B_156,C_157,D_158) = '#skF_7'
      | D_158 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_155,B_156,C_157,D_158),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_155,B_156,C_157,D_158),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_155,B_156,C_157,D_158),'#skF_4')
      | ~ m1_subset_1(D_158,k3_zfmisc_1(A_155,B_156,C_157))
      | k1_xboole_0 = C_157
      | k1_xboole_0 = B_156
      | k1_xboole_0 = A_155 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_34])).

tff(c_312,plain,(
    ! [A_7,C_9,D_25] :
      ( '#skF_2'(A_7,'#skF_5',C_9,D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_7,'#skF_5',C_9,D_25),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5',C_9,D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5',C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_10,c_308])).

tff(c_405,plain,(
    ! [A_207,C_208,D_209] :
      ( '#skF_2'(A_207,'#skF_5',C_208,D_209) = '#skF_7'
      | D_209 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_207,'#skF_5',C_208,D_209),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_207,'#skF_5',C_208,D_209),'#skF_4')
      | ~ m1_subset_1(D_209,k3_zfmisc_1(A_207,'#skF_5',C_208))
      | k1_xboole_0 = C_208
      | k1_xboole_0 = A_207 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_312])).

tff(c_409,plain,(
    ! [A_7,D_25] :
      ( '#skF_2'(A_7,'#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_7,'#skF_5','#skF_6',D_25),'#skF_4')
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_7 ) ),
    inference(resolution,[status(thm)],[c_8,c_405])).

tff(c_414,plain,(
    ! [A_210,D_211] :
      ( '#skF_2'(A_210,'#skF_5','#skF_6',D_211) = '#skF_7'
      | D_211 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_210,'#skF_5','#skF_6',D_211),'#skF_4')
      | ~ m1_subset_1(D_211,k3_zfmisc_1(A_210,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_210 ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_28,c_28,c_409])).

tff(c_418,plain,(
    ! [D_25] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_25) = '#skF_7'
      | D_25 != '#skF_8'
      | ~ m1_subset_1(D_25,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_12,c_414])).

tff(c_423,plain,(
    ! [D_212] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_212) = '#skF_7'
      | D_212 != '#skF_8'
      | ~ m1_subset_1(D_212,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_32,c_418])).

tff(c_442,plain,(
    '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_36,c_423])).

tff(c_6,plain,(
    ! [A_7,B_8,C_9,D_25] :
      ( k3_mcart_1('#skF_1'(A_7,B_8,C_9,D_25),'#skF_2'(A_7,B_8,C_9,D_25),'#skF_3'(A_7,B_8,C_9,D_25)) = D_25
      | ~ m1_subset_1(D_25,k3_zfmisc_1(A_7,B_8,C_9))
      | k1_xboole_0 = C_9
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_449,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_442,c_6])).

tff(c_460,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_449])).

tff(c_461,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_460])).

tff(c_16,plain,(
    ! [C_39,B_38,G_53,F_52,E_51,A_37] :
      ( k6_mcart_1(A_37,B_38,C_39,k3_mcart_1(E_51,F_52,G_53)) = F_52
      | ~ m1_subset_1(k3_mcart_1(E_51,F_52,G_53),k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_490,plain,(
    ! [A_37,B_38,C_39] :
      ( k6_mcart_1(A_37,B_38,C_39,k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8'))) = '#skF_7'
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_37,B_38,C_39))
      | k1_xboole_0 = C_39
      | k1_xboole_0 = B_38
      | k1_xboole_0 = A_37 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_461,c_16])).

tff(c_514,plain,(
    ! [A_213,B_214,C_215] :
      ( k6_mcart_1(A_213,B_214,C_215,'#skF_8') = '#skF_7'
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_213,B_214,C_215))
      | k1_xboole_0 = C_215
      | k1_xboole_0 = B_214
      | k1_xboole_0 = A_213 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_461,c_490])).

tff(c_520,plain,
    ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_36,c_514])).

tff(c_524,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_28,c_26,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:36:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.95/1.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.56  
% 2.95/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.95/1.56  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 2.95/1.56  
% 2.95/1.56  %Foreground sorts:
% 2.95/1.56  
% 2.95/1.56  
% 2.95/1.56  %Background operators:
% 2.95/1.56  
% 2.95/1.56  
% 2.95/1.56  %Foreground operators:
% 2.95/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.95/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.95/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.95/1.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 2.95/1.56  tff('#skF_7', type, '#skF_7': $i).
% 2.95/1.56  tff('#skF_5', type, '#skF_5': $i).
% 2.95/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.95/1.56  tff('#skF_6', type, '#skF_6': $i).
% 2.95/1.56  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 2.95/1.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 2.95/1.56  tff('#skF_8', type, '#skF_8': $i).
% 2.95/1.56  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 2.95/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.95/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.95/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.95/1.56  tff('#skF_4', type, '#skF_4': $i).
% 2.95/1.56  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 2.95/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.95/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.95/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.95/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.95/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.95/1.56  
% 3.05/1.58  tff(f_121, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 3.05/1.58  tff(f_54, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 3.05/1.58  tff(f_77, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_mcart_1)).
% 3.05/1.58  tff(c_32, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.05/1.58  tff(c_30, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.05/1.58  tff(c_28, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.05/1.58  tff(c_26, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.05/1.58  tff(c_36, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.05/1.58  tff(c_12, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_1'(A_7, B_8, C_9, D_25), A_7) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.58  tff(c_8, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_3'(A_7, B_8, C_9, D_25), C_9) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.58  tff(c_10, plain, (![A_7, B_8, C_9, D_25]: (m1_subset_1('#skF_2'(A_7, B_8, C_9, D_25), B_8) | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.58  tff(c_222, plain, (![A_136, B_137, C_138, D_139]: (k3_mcart_1('#skF_1'(A_136, B_137, C_138, D_139), '#skF_2'(A_136, B_137, C_138, D_139), '#skF_3'(A_136, B_137, C_138, D_139))=D_139 | ~m1_subset_1(D_139, k3_zfmisc_1(A_136, B_137, C_138)) | k1_xboole_0=C_138 | k1_xboole_0=B_137 | k1_xboole_0=A_136)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.58  tff(c_34, plain, (![G_70, F_66, H_72]: (G_70='#skF_7' | k3_mcart_1(F_66, G_70, H_72)!='#skF_8' | ~m1_subset_1(H_72, '#skF_6') | ~m1_subset_1(G_70, '#skF_5') | ~m1_subset_1(F_66, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_121])).
% 3.05/1.58  tff(c_308, plain, (![A_155, B_156, C_157, D_158]: ('#skF_2'(A_155, B_156, C_157, D_158)='#skF_7' | D_158!='#skF_8' | ~m1_subset_1('#skF_3'(A_155, B_156, C_157, D_158), '#skF_6') | ~m1_subset_1('#skF_2'(A_155, B_156, C_157, D_158), '#skF_5') | ~m1_subset_1('#skF_1'(A_155, B_156, C_157, D_158), '#skF_4') | ~m1_subset_1(D_158, k3_zfmisc_1(A_155, B_156, C_157)) | k1_xboole_0=C_157 | k1_xboole_0=B_156 | k1_xboole_0=A_155)), inference(superposition, [status(thm), theory('equality')], [c_222, c_34])).
% 3.05/1.58  tff(c_312, plain, (![A_7, C_9, D_25]: ('#skF_2'(A_7, '#skF_5', C_9, D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_3'(A_7, '#skF_5', C_9, D_25), '#skF_6') | ~m1_subset_1('#skF_1'(A_7, '#skF_5', C_9, D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', C_9)) | k1_xboole_0=C_9 | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_10, c_308])).
% 3.05/1.58  tff(c_405, plain, (![A_207, C_208, D_209]: ('#skF_2'(A_207, '#skF_5', C_208, D_209)='#skF_7' | D_209!='#skF_8' | ~m1_subset_1('#skF_3'(A_207, '#skF_5', C_208, D_209), '#skF_6') | ~m1_subset_1('#skF_1'(A_207, '#skF_5', C_208, D_209), '#skF_4') | ~m1_subset_1(D_209, k3_zfmisc_1(A_207, '#skF_5', C_208)) | k1_xboole_0=C_208 | k1_xboole_0=A_207)), inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_312])).
% 3.05/1.58  tff(c_409, plain, (![A_7, D_25]: ('#skF_2'(A_7, '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1('#skF_1'(A_7, '#skF_5', '#skF_6', D_25), '#skF_4') | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_7)), inference(resolution, [status(thm)], [c_8, c_405])).
% 3.05/1.58  tff(c_414, plain, (![A_210, D_211]: ('#skF_2'(A_210, '#skF_5', '#skF_6', D_211)='#skF_7' | D_211!='#skF_8' | ~m1_subset_1('#skF_1'(A_210, '#skF_5', '#skF_6', D_211), '#skF_4') | ~m1_subset_1(D_211, k3_zfmisc_1(A_210, '#skF_5', '#skF_6')) | k1_xboole_0=A_210)), inference(negUnitSimplification, [status(thm)], [c_30, c_28, c_28, c_409])).
% 3.05/1.58  tff(c_418, plain, (![D_25]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_25)='#skF_7' | D_25!='#skF_8' | ~m1_subset_1(D_25, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_12, c_414])).
% 3.05/1.58  tff(c_423, plain, (![D_212]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_212)='#skF_7' | D_212!='#skF_8' | ~m1_subset_1(D_212, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_32, c_418])).
% 3.05/1.58  tff(c_442, plain, ('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_36, c_423])).
% 3.05/1.58  tff(c_6, plain, (![A_7, B_8, C_9, D_25]: (k3_mcart_1('#skF_1'(A_7, B_8, C_9, D_25), '#skF_2'(A_7, B_8, C_9, D_25), '#skF_3'(A_7, B_8, C_9, D_25))=D_25 | ~m1_subset_1(D_25, k3_zfmisc_1(A_7, B_8, C_9)) | k1_xboole_0=C_9 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.05/1.58  tff(c_449, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_442, c_6])).
% 3.05/1.58  tff(c_460, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_449])).
% 3.05/1.58  tff(c_461, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_460])).
% 3.05/1.58  tff(c_16, plain, (![C_39, B_38, G_53, F_52, E_51, A_37]: (k6_mcart_1(A_37, B_38, C_39, k3_mcart_1(E_51, F_52, G_53))=F_52 | ~m1_subset_1(k3_mcart_1(E_51, F_52, G_53), k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.05/1.58  tff(c_490, plain, (![A_37, B_38, C_39]: (k6_mcart_1(A_37, B_38, C_39, k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8')))='#skF_7' | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_37, B_38, C_39)) | k1_xboole_0=C_39 | k1_xboole_0=B_38 | k1_xboole_0=A_37)), inference(superposition, [status(thm), theory('equality')], [c_461, c_16])).
% 3.05/1.58  tff(c_514, plain, (![A_213, B_214, C_215]: (k6_mcart_1(A_213, B_214, C_215, '#skF_8')='#skF_7' | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_213, B_214, C_215)) | k1_xboole_0=C_215 | k1_xboole_0=B_214 | k1_xboole_0=A_213)), inference(demodulation, [status(thm), theory('equality')], [c_461, c_490])).
% 3.05/1.58  tff(c_520, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_36, c_514])).
% 3.05/1.58  tff(c_524, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_28, c_26, c_520])).
% 3.05/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.05/1.58  
% 3.05/1.58  Inference rules
% 3.05/1.58  ----------------------
% 3.05/1.58  #Ref     : 0
% 3.05/1.58  #Sup     : 112
% 3.05/1.58  #Fact    : 0
% 3.05/1.58  #Define  : 0
% 3.05/1.58  #Split   : 0
% 3.05/1.58  #Chain   : 0
% 3.05/1.58  #Close   : 0
% 3.05/1.58  
% 3.05/1.58  Ordering : KBO
% 3.05/1.58  
% 3.05/1.58  Simplification rules
% 3.05/1.58  ----------------------
% 3.05/1.58  #Subsume      : 10
% 3.05/1.58  #Demod        : 62
% 3.05/1.58  #Tautology    : 26
% 3.05/1.58  #SimpNegUnit  : 10
% 3.05/1.58  #BackRed      : 0
% 3.05/1.58  
% 3.05/1.58  #Partial instantiations: 0
% 3.05/1.58  #Strategies tried      : 1
% 3.05/1.58  
% 3.05/1.58  Timing (in seconds)
% 3.05/1.58  ----------------------
% 3.05/1.58  Preprocessing        : 0.39
% 3.05/1.58  Parsing              : 0.21
% 3.05/1.58  CNF conversion       : 0.03
% 3.05/1.58  Main loop            : 0.33
% 3.05/1.58  Inferencing          : 0.13
% 3.05/1.58  Reduction            : 0.09
% 3.05/1.58  Demodulation         : 0.07
% 3.05/1.58  BG Simplification    : 0.03
% 3.05/1.58  Subsumption          : 0.06
% 3.05/1.58  Abstraction          : 0.03
% 3.05/1.58  MUC search           : 0.00
% 3.05/1.58  Cooper               : 0.00
% 3.05/1.58  Total                : 0.75
% 3.05/1.58  Index Insertion      : 0.00
% 3.05/1.58  Index Deletion       : 0.00
% 3.05/1.58  Index Matching       : 0.00
% 3.05/1.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
