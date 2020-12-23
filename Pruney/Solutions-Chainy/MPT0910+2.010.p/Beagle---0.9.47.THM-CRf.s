%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:00 EST 2020

% Result     : Theorem 3.62s
% Output     : CNFRefutation 3.62s
% Verified   : 
% Statistics : Number of formulae       :   60 ( 105 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :   14
%              Number of atoms          :  156 ( 436 expanded)
%              Number of equality atoms :  113 ( 282 expanded)
%              Maximal formula depth    :   17 (   6 average)
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

tff(f_130,negated_conjecture,(
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

tff(f_62,axiom,(
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

tff(f_106,axiom,(
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

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_70,axiom,(
    ! [A,B,C,D,E,F] :
      ( k3_mcart_1(A,B,C) = k3_mcart_1(D,E,F)
     => ( A = D
        & B = E
        & C = F ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_mcart_1)).

tff(c_32,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17,D_33] :
      ( m1_subset_1('#skF_1'(A_15,B_16,C_17,D_33),A_15)
      | ~ m1_subset_1(D_33,k3_zfmisc_1(A_15,B_16,C_17))
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17,D_33] :
      ( m1_subset_1('#skF_3'(A_15,B_16,C_17,D_33),C_17)
      | ~ m1_subset_1(D_33,k3_zfmisc_1(A_15,B_16,C_17))
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_14,plain,(
    ! [A_15,B_16,C_17,D_33] :
      ( m1_subset_1('#skF_2'(A_15,B_16,C_17,D_33),B_16)
      | ~ m1_subset_1(D_33,k3_zfmisc_1(A_15,B_16,C_17))
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_398,plain,(
    ! [A_201,B_202,C_203,D_204] :
      ( k3_mcart_1('#skF_1'(A_201,B_202,C_203,D_204),'#skF_2'(A_201,B_202,C_203,D_204),'#skF_3'(A_201,B_202,C_203,D_204)) = D_204
      | ~ m1_subset_1(D_204,k3_zfmisc_1(A_201,B_202,C_203))
      | k1_xboole_0 = C_203
      | k1_xboole_0 = B_202
      | k1_xboole_0 = A_201 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    ! [G_72,F_68,H_74] :
      ( G_72 = '#skF_7'
      | k3_mcart_1(F_68,G_72,H_74) != '#skF_8'
      | ~ m1_subset_1(H_74,'#skF_6')
      | ~ m1_subset_1(G_72,'#skF_5')
      | ~ m1_subset_1(F_68,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_735,plain,(
    ! [A_261,B_262,C_263,D_264] :
      ( '#skF_2'(A_261,B_262,C_263,D_264) = '#skF_7'
      | D_264 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_261,B_262,C_263,D_264),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_261,B_262,C_263,D_264),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_261,B_262,C_263,D_264),'#skF_4')
      | ~ m1_subset_1(D_264,k3_zfmisc_1(A_261,B_262,C_263))
      | k1_xboole_0 = C_263
      | k1_xboole_0 = B_262
      | k1_xboole_0 = A_261 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_398,c_40])).

tff(c_739,plain,(
    ! [A_15,C_17,D_33] :
      ( '#skF_2'(A_15,'#skF_5',C_17,D_33) = '#skF_7'
      | D_33 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_15,'#skF_5',C_17,D_33),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_15,'#skF_5',C_17,D_33),'#skF_4')
      | ~ m1_subset_1(D_33,k3_zfmisc_1(A_15,'#skF_5',C_17))
      | k1_xboole_0 = C_17
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_14,c_735])).

tff(c_783,plain,(
    ! [A_279,C_280,D_281] :
      ( '#skF_2'(A_279,'#skF_5',C_280,D_281) = '#skF_7'
      | D_281 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_279,'#skF_5',C_280,D_281),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_279,'#skF_5',C_280,D_281),'#skF_4')
      | ~ m1_subset_1(D_281,k3_zfmisc_1(A_279,'#skF_5',C_280))
      | k1_xboole_0 = C_280
      | k1_xboole_0 = A_279 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_36,c_739])).

tff(c_787,plain,(
    ! [A_15,D_33] :
      ( '#skF_2'(A_15,'#skF_5','#skF_6',D_33) = '#skF_7'
      | D_33 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_15,'#skF_5','#skF_6',D_33),'#skF_4')
      | ~ m1_subset_1(D_33,k3_zfmisc_1(A_15,'#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_15 ) ),
    inference(resolution,[status(thm)],[c_12,c_783])).

tff(c_850,plain,(
    ! [A_302,D_303] :
      ( '#skF_2'(A_302,'#skF_5','#skF_6',D_303) = '#skF_7'
      | D_303 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_302,'#skF_5','#skF_6',D_303),'#skF_4')
      | ~ m1_subset_1(D_303,k3_zfmisc_1(A_302,'#skF_5','#skF_6'))
      | k1_xboole_0 = A_302 ) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_34,c_34,c_787])).

tff(c_854,plain,(
    ! [D_33] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_33) = '#skF_7'
      | D_33 != '#skF_8'
      | ~ m1_subset_1(D_33,k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_16,c_850])).

tff(c_859,plain,(
    ! [D_304] :
      ( '#skF_2'('#skF_4','#skF_5','#skF_6',D_304) = '#skF_7'
      | D_304 != '#skF_8'
      | ~ m1_subset_1(D_304,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_38,c_854])).

tff(c_888,plain,(
    '#skF_2'('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_42,c_859])).

tff(c_10,plain,(
    ! [A_15,B_16,C_17,D_33] :
      ( k3_mcart_1('#skF_1'(A_15,B_16,C_17,D_33),'#skF_2'(A_15,B_16,C_17,D_33),'#skF_3'(A_15,B_16,C_17,D_33)) = D_33
      | ~ m1_subset_1(D_33,k3_zfmisc_1(A_15,B_16,C_17))
      | k1_xboole_0 = C_17
      | k1_xboole_0 = B_16
      | k1_xboole_0 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_895,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_888,c_10])).

tff(c_906,plain,
    ( k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_895])).

tff(c_907,plain,(
    k3_mcart_1('#skF_1'('#skF_4','#skF_5','#skF_6','#skF_8'),'#skF_7','#skF_3'('#skF_4','#skF_5','#skF_6','#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_906])).

tff(c_204,plain,(
    ! [A_171,B_172,C_173,D_174] :
      ( k7_mcart_1(A_171,B_172,C_173,D_174) = k2_mcart_1(D_174)
      | ~ m1_subset_1(D_174,k3_zfmisc_1(A_171,B_172,C_173))
      | k1_xboole_0 = C_173
      | k1_xboole_0 = B_172
      | k1_xboole_0 = A_171 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_222,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_42,c_204])).

tff(c_228,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_222])).

tff(c_505,plain,(
    ! [A_234,B_235,C_236,D_237] :
      ( k3_mcart_1(k5_mcart_1(A_234,B_235,C_236,D_237),k6_mcart_1(A_234,B_235,C_236,D_237),k7_mcart_1(A_234,B_235,C_236,D_237)) = D_237
      | ~ m1_subset_1(D_237,k3_zfmisc_1(A_234,B_235,C_236))
      | k1_xboole_0 = C_236
      | k1_xboole_0 = B_235
      | k1_xboole_0 = A_234 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_577,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_228,c_505])).

tff(c_584,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_577])).

tff(c_585,plain,(
    k3_mcart_1(k5_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8'),k2_mcart_1('#skF_8')) = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_36,c_34,c_584])).

tff(c_20,plain,(
    ! [D_48,C_47,A_45,B_46,E_49,F_50] :
      ( E_49 = B_46
      | k3_mcart_1(D_48,E_49,F_50) != k3_mcart_1(A_45,B_46,C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_640,plain,(
    ! [B_46,A_45,C_47] :
      ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = B_46
      | k3_mcart_1(A_45,B_46,C_47) != '#skF_8' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_585,c_20])).

tff(c_927,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_907,c_640])).

tff(c_1011,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_927])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:52:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.62/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.55  
% 3.62/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.56  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 3.62/1.56  
% 3.62/1.56  %Foreground sorts:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Background operators:
% 3.62/1.56  
% 3.62/1.56  
% 3.62/1.56  %Foreground operators:
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.62/1.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.62/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.62/1.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.62/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.62/1.56  tff('#skF_5', type, '#skF_5': $i).
% 3.62/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.62/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.62/1.56  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.62/1.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.62/1.56  tff('#skF_8', type, '#skF_8': $i).
% 3.62/1.56  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.62/1.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.62/1.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.62/1.56  tff('#skF_4', type, '#skF_4': $i).
% 3.62/1.56  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.62/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.62/1.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.62/1.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.62/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.62/1.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.62/1.56  
% 3.62/1.57  tff(f_130, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 3.62/1.57  tff(f_62, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) & (![E]: (m1_subset_1(E, A) => (![F]: (m1_subset_1(F, B) => (![G]: (m1_subset_1(G, C) => ~(D = k3_mcart_1(E, F, G)))))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l44_mcart_1)).
% 3.62/1.57  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.62/1.57  tff(f_86, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 3.62/1.57  tff(f_70, axiom, (![A, B, C, D, E, F]: ((k3_mcart_1(A, B, C) = k3_mcart_1(D, E, F)) => (((A = D) & (B = E)) & (C = F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_mcart_1)).
% 3.62/1.57  tff(c_32, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.57  tff(c_38, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.57  tff(c_36, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.57  tff(c_34, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.57  tff(c_42, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.57  tff(c_16, plain, (![A_15, B_16, C_17, D_33]: (m1_subset_1('#skF_1'(A_15, B_16, C_17, D_33), A_15) | ~m1_subset_1(D_33, k3_zfmisc_1(A_15, B_16, C_17)) | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.57  tff(c_12, plain, (![A_15, B_16, C_17, D_33]: (m1_subset_1('#skF_3'(A_15, B_16, C_17, D_33), C_17) | ~m1_subset_1(D_33, k3_zfmisc_1(A_15, B_16, C_17)) | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.57  tff(c_14, plain, (![A_15, B_16, C_17, D_33]: (m1_subset_1('#skF_2'(A_15, B_16, C_17, D_33), B_16) | ~m1_subset_1(D_33, k3_zfmisc_1(A_15, B_16, C_17)) | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.57  tff(c_398, plain, (![A_201, B_202, C_203, D_204]: (k3_mcart_1('#skF_1'(A_201, B_202, C_203, D_204), '#skF_2'(A_201, B_202, C_203, D_204), '#skF_3'(A_201, B_202, C_203, D_204))=D_204 | ~m1_subset_1(D_204, k3_zfmisc_1(A_201, B_202, C_203)) | k1_xboole_0=C_203 | k1_xboole_0=B_202 | k1_xboole_0=A_201)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.57  tff(c_40, plain, (![G_72, F_68, H_74]: (G_72='#skF_7' | k3_mcart_1(F_68, G_72, H_74)!='#skF_8' | ~m1_subset_1(H_74, '#skF_6') | ~m1_subset_1(G_72, '#skF_5') | ~m1_subset_1(F_68, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 3.62/1.57  tff(c_735, plain, (![A_261, B_262, C_263, D_264]: ('#skF_2'(A_261, B_262, C_263, D_264)='#skF_7' | D_264!='#skF_8' | ~m1_subset_1('#skF_3'(A_261, B_262, C_263, D_264), '#skF_6') | ~m1_subset_1('#skF_2'(A_261, B_262, C_263, D_264), '#skF_5') | ~m1_subset_1('#skF_1'(A_261, B_262, C_263, D_264), '#skF_4') | ~m1_subset_1(D_264, k3_zfmisc_1(A_261, B_262, C_263)) | k1_xboole_0=C_263 | k1_xboole_0=B_262 | k1_xboole_0=A_261)), inference(superposition, [status(thm), theory('equality')], [c_398, c_40])).
% 3.62/1.57  tff(c_739, plain, (![A_15, C_17, D_33]: ('#skF_2'(A_15, '#skF_5', C_17, D_33)='#skF_7' | D_33!='#skF_8' | ~m1_subset_1('#skF_3'(A_15, '#skF_5', C_17, D_33), '#skF_6') | ~m1_subset_1('#skF_1'(A_15, '#skF_5', C_17, D_33), '#skF_4') | ~m1_subset_1(D_33, k3_zfmisc_1(A_15, '#skF_5', C_17)) | k1_xboole_0=C_17 | k1_xboole_0='#skF_5' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_14, c_735])).
% 3.62/1.57  tff(c_783, plain, (![A_279, C_280, D_281]: ('#skF_2'(A_279, '#skF_5', C_280, D_281)='#skF_7' | D_281!='#skF_8' | ~m1_subset_1('#skF_3'(A_279, '#skF_5', C_280, D_281), '#skF_6') | ~m1_subset_1('#skF_1'(A_279, '#skF_5', C_280, D_281), '#skF_4') | ~m1_subset_1(D_281, k3_zfmisc_1(A_279, '#skF_5', C_280)) | k1_xboole_0=C_280 | k1_xboole_0=A_279)), inference(negUnitSimplification, [status(thm)], [c_36, c_36, c_739])).
% 3.62/1.57  tff(c_787, plain, (![A_15, D_33]: ('#skF_2'(A_15, '#skF_5', '#skF_6', D_33)='#skF_7' | D_33!='#skF_8' | ~m1_subset_1('#skF_1'(A_15, '#skF_5', '#skF_6', D_33), '#skF_4') | ~m1_subset_1(D_33, k3_zfmisc_1(A_15, '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_15)), inference(resolution, [status(thm)], [c_12, c_783])).
% 3.62/1.57  tff(c_850, plain, (![A_302, D_303]: ('#skF_2'(A_302, '#skF_5', '#skF_6', D_303)='#skF_7' | D_303!='#skF_8' | ~m1_subset_1('#skF_1'(A_302, '#skF_5', '#skF_6', D_303), '#skF_4') | ~m1_subset_1(D_303, k3_zfmisc_1(A_302, '#skF_5', '#skF_6')) | k1_xboole_0=A_302)), inference(negUnitSimplification, [status(thm)], [c_36, c_34, c_34, c_787])).
% 3.62/1.57  tff(c_854, plain, (![D_33]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_33)='#skF_7' | D_33!='#skF_8' | ~m1_subset_1(D_33, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4')), inference(resolution, [status(thm)], [c_16, c_850])).
% 3.62/1.57  tff(c_859, plain, (![D_304]: ('#skF_2'('#skF_4', '#skF_5', '#skF_6', D_304)='#skF_7' | D_304!='#skF_8' | ~m1_subset_1(D_304, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_38, c_854])).
% 3.62/1.57  tff(c_888, plain, ('#skF_2'('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(resolution, [status(thm)], [c_42, c_859])).
% 3.62/1.57  tff(c_10, plain, (![A_15, B_16, C_17, D_33]: (k3_mcart_1('#skF_1'(A_15, B_16, C_17, D_33), '#skF_2'(A_15, B_16, C_17, D_33), '#skF_3'(A_15, B_16, C_17, D_33))=D_33 | ~m1_subset_1(D_33, k3_zfmisc_1(A_15, B_16, C_17)) | k1_xboole_0=C_17 | k1_xboole_0=B_16 | k1_xboole_0=A_15)), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.62/1.57  tff(c_895, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_888, c_10])).
% 3.62/1.57  tff(c_906, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_895])).
% 3.62/1.57  tff(c_907, plain, (k3_mcart_1('#skF_1'('#skF_4', '#skF_5', '#skF_6', '#skF_8'), '#skF_7', '#skF_3'('#skF_4', '#skF_5', '#skF_6', '#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_906])).
% 3.62/1.57  tff(c_204, plain, (![A_171, B_172, C_173, D_174]: (k7_mcart_1(A_171, B_172, C_173, D_174)=k2_mcart_1(D_174) | ~m1_subset_1(D_174, k3_zfmisc_1(A_171, B_172, C_173)) | k1_xboole_0=C_173 | k1_xboole_0=B_172 | k1_xboole_0=A_171)), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.62/1.57  tff(c_222, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_42, c_204])).
% 3.62/1.57  tff(c_228, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_222])).
% 3.62/1.57  tff(c_505, plain, (![A_234, B_235, C_236, D_237]: (k3_mcart_1(k5_mcart_1(A_234, B_235, C_236, D_237), k6_mcart_1(A_234, B_235, C_236, D_237), k7_mcart_1(A_234, B_235, C_236, D_237))=D_237 | ~m1_subset_1(D_237, k3_zfmisc_1(A_234, B_235, C_236)) | k1_xboole_0=C_236 | k1_xboole_0=B_235 | k1_xboole_0=A_234)), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.62/1.57  tff(c_577, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_228, c_505])).
% 3.62/1.57  tff(c_584, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_577])).
% 3.62/1.57  tff(c_585, plain, (k3_mcart_1(k5_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8'), k2_mcart_1('#skF_8'))='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_38, c_36, c_34, c_584])).
% 3.62/1.57  tff(c_20, plain, (![D_48, C_47, A_45, B_46, E_49, F_50]: (E_49=B_46 | k3_mcart_1(D_48, E_49, F_50)!=k3_mcart_1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.62/1.57  tff(c_640, plain, (![B_46, A_45, C_47]: (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=B_46 | k3_mcart_1(A_45, B_46, C_47)!='#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_585, c_20])).
% 3.62/1.57  tff(c_927, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_907, c_640])).
% 3.62/1.57  tff(c_1011, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_927])).
% 3.62/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.62/1.57  
% 3.62/1.57  Inference rules
% 3.62/1.57  ----------------------
% 3.62/1.57  #Ref     : 12
% 3.62/1.57  #Sup     : 259
% 3.62/1.57  #Fact    : 0
% 3.62/1.57  #Define  : 0
% 3.62/1.57  #Split   : 2
% 3.62/1.57  #Chain   : 0
% 3.62/1.57  #Close   : 0
% 3.62/1.57  
% 3.62/1.57  Ordering : KBO
% 3.62/1.57  
% 3.62/1.57  Simplification rules
% 3.62/1.57  ----------------------
% 3.62/1.57  #Subsume      : 40
% 3.62/1.57  #Demod        : 44
% 3.62/1.57  #Tautology    : 39
% 3.62/1.57  #SimpNegUnit  : 12
% 3.62/1.57  #BackRed      : 0
% 3.62/1.57  
% 3.62/1.57  #Partial instantiations: 0
% 3.62/1.57  #Strategies tried      : 1
% 3.62/1.57  
% 3.62/1.57  Timing (in seconds)
% 3.62/1.57  ----------------------
% 3.62/1.57  Preprocessing        : 0.32
% 3.62/1.57  Parsing              : 0.17
% 3.62/1.57  CNF conversion       : 0.03
% 3.62/1.57  Main loop            : 0.50
% 3.62/1.57  Inferencing          : 0.18
% 3.62/1.57  Reduction            : 0.12
% 3.62/1.57  Demodulation         : 0.08
% 3.62/1.57  BG Simplification    : 0.03
% 3.62/1.57  Subsumption          : 0.14
% 3.62/1.57  Abstraction          : 0.04
% 3.62/1.57  MUC search           : 0.00
% 3.62/1.57  Cooper               : 0.00
% 3.62/1.57  Total                : 0.85
% 3.62/1.57  Index Insertion      : 0.00
% 3.62/1.57  Index Deletion       : 0.00
% 3.62/1.57  Index Matching       : 0.00
% 3.62/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------
