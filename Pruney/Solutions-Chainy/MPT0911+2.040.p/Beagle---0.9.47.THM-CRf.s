%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:07 EST 2020

% Result     : Theorem 4.57s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 387 expanded)
%              Number of leaves         :   26 ( 161 expanded)
%              Depth                    :   18
%              Number of atoms          :  194 (2191 expanded)
%              Number of equality atoms :  148 (1453 expanded)
%              Maximal formula depth    :   17 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_mcart_1)).

tff(f_49,axiom,(
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

tff(f_94,axiom,(
    ! [A,B,C,D,E] :
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

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => ~ ( A != k1_xboole_0
          & B != k1_xboole_0
          & C != k1_xboole_0
          & ? [E,F,G] :
              ( D = k3_mcart_1(E,F,G)
              & ~ ( k5_mcart_1(A,B,C,D) = E
                  & k6_mcart_1(A,B,C,D) = F
                  & k7_mcart_1(A,B,C,D) = G ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_mcart_1)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_32,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_38,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_100,plain,(
    ! [A_69,B_70,C_71,D_72] :
      ( k7_mcart_1(A_69,B_70,C_71,D_72) = k2_mcart_1(D_72)
      | ~ m1_subset_1(D_72,k3_zfmisc_1(A_69,B_70,C_71))
      | k1_xboole_0 = C_71
      | k1_xboole_0 = B_70
      | k1_xboole_0 = A_69 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8')
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_100])).

tff(c_109,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = k2_mcart_1('#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_106])).

tff(c_28,plain,(
    k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_110,plain,(
    k2_mcart_1('#skF_8') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_28])).

tff(c_26,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_1'(A_22,C_24,E_26,D_25,B_23),A_22)
      | k6_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_22,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_3'(A_22,C_24,E_26,D_25,B_23),C_24)
      | k6_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_24,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( m1_subset_1('#skF_2'(A_22,C_24,E_26,D_25,B_23),B_23)
      | k6_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_269,plain,(
    ! [B_137,A_133,D_136,C_134,E_135] :
      ( k3_mcart_1('#skF_1'(A_133,C_134,E_135,D_136,B_137),'#skF_2'(A_133,C_134,E_135,D_136,B_137),'#skF_3'(A_133,C_134,E_135,D_136,B_137)) = E_135
      | k6_mcart_1(A_133,B_137,C_134,E_135) = D_136
      | k1_xboole_0 = C_134
      | k1_xboole_0 = B_137
      | k1_xboole_0 = A_133
      | ~ m1_subset_1(E_135,k3_zfmisc_1(A_133,B_137,C_134)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_36,plain,(
    ! [H_51,F_45,G_49] :
      ( H_51 = '#skF_7'
      | k3_mcart_1(F_45,G_49,H_51) != '#skF_8'
      | ~ m1_subset_1(H_51,'#skF_6')
      | ~ m1_subset_1(G_49,'#skF_5')
      | ~ m1_subset_1(F_45,'#skF_4') ) ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_358,plain,(
    ! [C_171,E_173,B_174,D_175,A_172] :
      ( '#skF_3'(A_172,C_171,E_173,D_175,B_174) = '#skF_7'
      | E_173 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_172,C_171,E_173,D_175,B_174),'#skF_6')
      | ~ m1_subset_1('#skF_2'(A_172,C_171,E_173,D_175,B_174),'#skF_5')
      | ~ m1_subset_1('#skF_1'(A_172,C_171,E_173,D_175,B_174),'#skF_4')
      | k6_mcart_1(A_172,B_174,C_171,E_173) = D_175
      | k1_xboole_0 = C_171
      | k1_xboole_0 = B_174
      | k1_xboole_0 = A_172
      | ~ m1_subset_1(E_173,k3_zfmisc_1(A_172,B_174,C_171)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_269,c_36])).

tff(c_362,plain,(
    ! [A_22,C_24,E_26,D_25] :
      ( '#skF_3'(A_22,C_24,E_26,D_25,'#skF_5') = '#skF_7'
      | E_26 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_22,C_24,E_26,D_25,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_22,C_24,E_26,D_25,'#skF_5'),'#skF_4')
      | k6_mcart_1(A_22,'#skF_5',C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,'#skF_5',C_24)) ) ),
    inference(resolution,[status(thm)],[c_24,c_358])).

tff(c_403,plain,(
    ! [A_198,C_199,E_200,D_201] :
      ( '#skF_3'(A_198,C_199,E_200,D_201,'#skF_5') = '#skF_7'
      | E_200 != '#skF_8'
      | ~ m1_subset_1('#skF_3'(A_198,C_199,E_200,D_201,'#skF_5'),'#skF_6')
      | ~ m1_subset_1('#skF_1'(A_198,C_199,E_200,D_201,'#skF_5'),'#skF_4')
      | k6_mcart_1(A_198,'#skF_5',C_199,E_200) = D_201
      | k1_xboole_0 = C_199
      | k1_xboole_0 = A_198
      | ~ m1_subset_1(E_200,k3_zfmisc_1(A_198,'#skF_5',C_199)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_32,c_362])).

tff(c_407,plain,(
    ! [A_22,E_26,D_25] :
      ( '#skF_3'(A_22,'#skF_6',E_26,D_25,'#skF_5') = '#skF_7'
      | E_26 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_22,'#skF_6',E_26,D_25,'#skF_5'),'#skF_4')
      | k6_mcart_1(A_22,'#skF_5','#skF_6',E_26) = D_25
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,'#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_22,c_403])).

tff(c_412,plain,(
    ! [A_202,E_203,D_204] :
      ( '#skF_3'(A_202,'#skF_6',E_203,D_204,'#skF_5') = '#skF_7'
      | E_203 != '#skF_8'
      | ~ m1_subset_1('#skF_1'(A_202,'#skF_6',E_203,D_204,'#skF_5'),'#skF_4')
      | k6_mcart_1(A_202,'#skF_5','#skF_6',E_203) = D_204
      | k1_xboole_0 = A_202
      | ~ m1_subset_1(E_203,k3_zfmisc_1(A_202,'#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_30,c_30,c_407])).

tff(c_416,plain,(
    ! [E_26,D_25] :
      ( '#skF_3'('#skF_4','#skF_6',E_26,D_25,'#skF_5') = '#skF_7'
      | E_26 != '#skF_8'
      | k6_mcart_1('#skF_4','#skF_5','#skF_6',E_26) = D_25
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1(E_26,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_26,c_412])).

tff(c_421,plain,(
    ! [E_205,D_206] :
      ( '#skF_3'('#skF_4','#skF_6',E_205,D_206,'#skF_5') = '#skF_7'
      | E_205 != '#skF_8'
      | k6_mcart_1('#skF_4','#skF_5','#skF_6',E_205) = D_206
      | ~ m1_subset_1(E_205,k3_zfmisc_1('#skF_4','#skF_5','#skF_6')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_34,c_416])).

tff(c_439,plain,(
    ! [D_207] :
      ( '#skF_3'('#skF_4','#skF_6','#skF_8',D_207,'#skF_5') = '#skF_7'
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207 ) ),
    inference(resolution,[status(thm)],[c_38,c_421])).

tff(c_20,plain,(
    ! [E_26,A_22,B_23,D_25,C_24] :
      ( k3_mcart_1('#skF_1'(A_22,C_24,E_26,D_25,B_23),'#skF_2'(A_22,C_24,E_26,D_25,B_23),'#skF_3'(A_22,C_24,E_26,D_25,B_23)) = E_26
      | k6_mcart_1(A_22,B_23,C_24,E_26) = D_25
      | k1_xboole_0 = C_24
      | k1_xboole_0 = B_23
      | k1_xboole_0 = A_22
      | ~ m1_subset_1(E_26,k3_zfmisc_1(A_22,B_23,C_24)) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_448,plain,(
    ! [D_207] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_207,'#skF_5'),'#skF_2'('#skF_4','#skF_6','#skF_8',D_207,'#skF_5'),'#skF_7') = '#skF_8'
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_4','#skF_5','#skF_6'))
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_439,c_20])).

tff(c_855,plain,(
    ! [D_207] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_207,'#skF_5'),'#skF_2'('#skF_4','#skF_6','#skF_8',D_207,'#skF_5'),'#skF_7') = '#skF_8'
      | k1_xboole_0 = '#skF_6'
      | k1_xboole_0 = '#skF_5'
      | k1_xboole_0 = '#skF_4'
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_448])).

tff(c_856,plain,(
    ! [D_207] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_207,'#skF_5'),'#skF_2'('#skF_4','#skF_6','#skF_8',D_207,'#skF_5'),'#skF_7') = '#skF_8'
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_855])).

tff(c_928,plain,(
    ! [D_1981] :
      ( k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_1981,'#skF_5'),'#skF_2'('#skF_4','#skF_6','#skF_8',D_1981,'#skF_5'),'#skF_7') = '#skF_8'
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_1981 ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_855])).

tff(c_12,plain,(
    ! [G_21,E_19,C_14,A_12,B_13,F_20] :
      ( k7_mcart_1(A_12,B_13,C_14,k3_mcart_1(E_19,F_20,G_21)) = G_21
      | k1_xboole_0 = C_14
      | k1_xboole_0 = B_13
      | k1_xboole_0 = A_12
      | ~ m1_subset_1(k3_mcart_1(E_19,F_20,G_21),k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1208,plain,(
    ! [A_2308,B_2309,C_2310,D_2311] :
      ( k7_mcart_1(A_2308,B_2309,C_2310,k3_mcart_1('#skF_1'('#skF_4','#skF_6','#skF_8',D_2311,'#skF_5'),'#skF_2'('#skF_4','#skF_6','#skF_8',D_2311,'#skF_5'),'#skF_7')) = '#skF_7'
      | k1_xboole_0 = C_2310
      | k1_xboole_0 = B_2309
      | k1_xboole_0 = A_2308
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_2308,B_2309,C_2310))
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_2311 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_928,c_12])).

tff(c_1217,plain,(
    ! [A_2308,B_2309,C_2310,D_207] :
      ( k7_mcart_1(A_2308,B_2309,C_2310,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_2310
      | k1_xboole_0 = B_2309
      | k1_xboole_0 = A_2308
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_2308,B_2309,C_2310))
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_856,c_1208])).

tff(c_1241,plain,(
    ! [D_207] :
      ( k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207
      | k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207 ) ),
    inference(splitLeft,[status(thm)],[c_1217])).

tff(c_2386,plain,(
    k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_5' ),
    inference(factorization,[status(thm),theory(equality)],[c_1241])).

tff(c_1262,plain,(
    ! [D_207] : k6_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = D_207 ),
    inference(factorization,[status(thm),theory(equality)],[c_1241])).

tff(c_3261,plain,(
    ! [D_10863] : D_10863 = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_2386,c_1262])).

tff(c_3588,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3261,c_32])).

tff(c_3590,plain,(
    ! [A_13048,B_13049,C_13050] :
      ( k7_mcart_1(A_13048,B_13049,C_13050,'#skF_8') = '#skF_7'
      | k1_xboole_0 = C_13050
      | k1_xboole_0 = B_13049
      | k1_xboole_0 = A_13048
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_13048,B_13049,C_13050)) ) ),
    inference(splitRight,[status(thm)],[c_1217])).

tff(c_3597,plain,
    ( k7_mcart_1('#skF_4','#skF_5','#skF_6','#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_38,c_3590])).

tff(c_3599,plain,
    ( k2_mcart_1('#skF_8') = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_3597])).

tff(c_3601,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30,c_110,c_3599])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:55:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.57/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.82  
% 4.63/1.82  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.82  %$ m1_subset_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 4.63/1.82  
% 4.63/1.82  %Foreground sorts:
% 4.63/1.82  
% 4.63/1.82  
% 4.63/1.82  %Background operators:
% 4.63/1.82  
% 4.63/1.82  
% 4.63/1.82  %Foreground operators:
% 4.63/1.82  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.82  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 4.63/1.82  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 4.63/1.82  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.82  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 4.63/1.82  tff('#skF_7', type, '#skF_7': $i).
% 4.63/1.82  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.82  tff('#skF_6', type, '#skF_6': $i).
% 4.63/1.82  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 4.63/1.82  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 4.63/1.82  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i * $i) > $i).
% 4.63/1.82  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 4.63/1.82  tff('#skF_8', type, '#skF_8': $i).
% 4.63/1.82  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 4.63/1.82  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.82  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 4.63/1.82  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.82  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.82  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 4.63/1.82  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.82  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 4.63/1.82  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.82  
% 4.63/1.84  tff(f_118, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_mcart_1)).
% 4.63/1.84  tff(f_49, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_mcart_1)).
% 4.63/1.84  tff(f_94, axiom, (![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_mcart_1)).
% 4.63/1.84  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & (?[E, F, G]: ((D = k3_mcart_1(E, F, G)) & ~(((k5_mcart_1(A, B, C, D) = E) & (k6_mcart_1(A, B, C, D) = F)) & (k7_mcart_1(A, B, C, D) = G))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_mcart_1)).
% 4.63/1.84  tff(c_34, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.63/1.84  tff(c_32, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.63/1.84  tff(c_30, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.63/1.84  tff(c_38, plain, (m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.63/1.84  tff(c_100, plain, (![A_69, B_70, C_71, D_72]: (k7_mcart_1(A_69, B_70, C_71, D_72)=k2_mcart_1(D_72) | ~m1_subset_1(D_72, k3_zfmisc_1(A_69, B_70, C_71)) | k1_xboole_0=C_71 | k1_xboole_0=B_70 | k1_xboole_0=A_69)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.63/1.84  tff(c_106, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8') | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_100])).
% 4.63/1.84  tff(c_109, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=k2_mcart_1('#skF_8')), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_106])).
% 4.63/1.84  tff(c_28, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.63/1.84  tff(c_110, plain, (k2_mcart_1('#skF_8')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_28])).
% 4.63/1.84  tff(c_26, plain, (![E_26, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_1'(A_22, C_24, E_26, D_25, B_23), A_22) | k6_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.63/1.84  tff(c_22, plain, (![E_26, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_3'(A_22, C_24, E_26, D_25, B_23), C_24) | k6_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.63/1.84  tff(c_24, plain, (![E_26, A_22, B_23, D_25, C_24]: (m1_subset_1('#skF_2'(A_22, C_24, E_26, D_25, B_23), B_23) | k6_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.63/1.84  tff(c_269, plain, (![B_137, A_133, D_136, C_134, E_135]: (k3_mcart_1('#skF_1'(A_133, C_134, E_135, D_136, B_137), '#skF_2'(A_133, C_134, E_135, D_136, B_137), '#skF_3'(A_133, C_134, E_135, D_136, B_137))=E_135 | k6_mcart_1(A_133, B_137, C_134, E_135)=D_136 | k1_xboole_0=C_134 | k1_xboole_0=B_137 | k1_xboole_0=A_133 | ~m1_subset_1(E_135, k3_zfmisc_1(A_133, B_137, C_134)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.63/1.84  tff(c_36, plain, (![H_51, F_45, G_49]: (H_51='#skF_7' | k3_mcart_1(F_45, G_49, H_51)!='#skF_8' | ~m1_subset_1(H_51, '#skF_6') | ~m1_subset_1(G_49, '#skF_5') | ~m1_subset_1(F_45, '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_118])).
% 4.63/1.84  tff(c_358, plain, (![C_171, E_173, B_174, D_175, A_172]: ('#skF_3'(A_172, C_171, E_173, D_175, B_174)='#skF_7' | E_173!='#skF_8' | ~m1_subset_1('#skF_3'(A_172, C_171, E_173, D_175, B_174), '#skF_6') | ~m1_subset_1('#skF_2'(A_172, C_171, E_173, D_175, B_174), '#skF_5') | ~m1_subset_1('#skF_1'(A_172, C_171, E_173, D_175, B_174), '#skF_4') | k6_mcart_1(A_172, B_174, C_171, E_173)=D_175 | k1_xboole_0=C_171 | k1_xboole_0=B_174 | k1_xboole_0=A_172 | ~m1_subset_1(E_173, k3_zfmisc_1(A_172, B_174, C_171)))), inference(superposition, [status(thm), theory('equality')], [c_269, c_36])).
% 4.63/1.84  tff(c_362, plain, (![A_22, C_24, E_26, D_25]: ('#skF_3'(A_22, C_24, E_26, D_25, '#skF_5')='#skF_7' | E_26!='#skF_8' | ~m1_subset_1('#skF_3'(A_22, C_24, E_26, D_25, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'(A_22, C_24, E_26, D_25, '#skF_5'), '#skF_4') | k6_mcart_1(A_22, '#skF_5', C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0='#skF_5' | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, '#skF_5', C_24)))), inference(resolution, [status(thm)], [c_24, c_358])).
% 4.63/1.84  tff(c_403, plain, (![A_198, C_199, E_200, D_201]: ('#skF_3'(A_198, C_199, E_200, D_201, '#skF_5')='#skF_7' | E_200!='#skF_8' | ~m1_subset_1('#skF_3'(A_198, C_199, E_200, D_201, '#skF_5'), '#skF_6') | ~m1_subset_1('#skF_1'(A_198, C_199, E_200, D_201, '#skF_5'), '#skF_4') | k6_mcart_1(A_198, '#skF_5', C_199, E_200)=D_201 | k1_xboole_0=C_199 | k1_xboole_0=A_198 | ~m1_subset_1(E_200, k3_zfmisc_1(A_198, '#skF_5', C_199)))), inference(negUnitSimplification, [status(thm)], [c_32, c_32, c_362])).
% 4.63/1.84  tff(c_407, plain, (![A_22, E_26, D_25]: ('#skF_3'(A_22, '#skF_6', E_26, D_25, '#skF_5')='#skF_7' | E_26!='#skF_8' | ~m1_subset_1('#skF_1'(A_22, '#skF_6', E_26, D_25, '#skF_5'), '#skF_4') | k6_mcart_1(A_22, '#skF_5', '#skF_6', E_26)=D_25 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_22, c_403])).
% 4.63/1.84  tff(c_412, plain, (![A_202, E_203, D_204]: ('#skF_3'(A_202, '#skF_6', E_203, D_204, '#skF_5')='#skF_7' | E_203!='#skF_8' | ~m1_subset_1('#skF_1'(A_202, '#skF_6', E_203, D_204, '#skF_5'), '#skF_4') | k6_mcart_1(A_202, '#skF_5', '#skF_6', E_203)=D_204 | k1_xboole_0=A_202 | ~m1_subset_1(E_203, k3_zfmisc_1(A_202, '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_32, c_30, c_30, c_407])).
% 4.63/1.84  tff(c_416, plain, (![E_26, D_25]: ('#skF_3'('#skF_4', '#skF_6', E_26, D_25, '#skF_5')='#skF_7' | E_26!='#skF_8' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', E_26)=D_25 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1(E_26, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_26, c_412])).
% 4.63/1.84  tff(c_421, plain, (![E_205, D_206]: ('#skF_3'('#skF_4', '#skF_6', E_205, D_206, '#skF_5')='#skF_7' | E_205!='#skF_8' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', E_205)=D_206 | ~m1_subset_1(E_205, k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')))), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_34, c_416])).
% 4.63/1.84  tff(c_439, plain, (![D_207]: ('#skF_3'('#skF_4', '#skF_6', '#skF_8', D_207, '#skF_5')='#skF_7' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207)), inference(resolution, [status(thm)], [c_38, c_421])).
% 4.63/1.84  tff(c_20, plain, (![E_26, A_22, B_23, D_25, C_24]: (k3_mcart_1('#skF_1'(A_22, C_24, E_26, D_25, B_23), '#skF_2'(A_22, C_24, E_26, D_25, B_23), '#skF_3'(A_22, C_24, E_26, D_25, B_23))=E_26 | k6_mcart_1(A_22, B_23, C_24, E_26)=D_25 | k1_xboole_0=C_24 | k1_xboole_0=B_23 | k1_xboole_0=A_22 | ~m1_subset_1(E_26, k3_zfmisc_1(A_22, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_94])).
% 4.63/1.84  tff(c_448, plain, (![D_207]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_207, '#skF_5'), '#skF_2'('#skF_4', '#skF_6', '#skF_8', D_207, '#skF_5'), '#skF_7')='#skF_8' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207 | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | ~m1_subset_1('#skF_8', k3_zfmisc_1('#skF_4', '#skF_5', '#skF_6')) | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207)), inference(superposition, [status(thm), theory('equality')], [c_439, c_20])).
% 4.63/1.84  tff(c_855, plain, (![D_207]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_207, '#skF_5'), '#skF_2'('#skF_4', '#skF_6', '#skF_8', D_207, '#skF_5'), '#skF_7')='#skF_8' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_448])).
% 4.63/1.84  tff(c_856, plain, (![D_207]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_207, '#skF_5'), '#skF_2'('#skF_4', '#skF_6', '#skF_8', D_207, '#skF_5'), '#skF_7')='#skF_8' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_855])).
% 4.63/1.84  tff(c_928, plain, (![D_1981]: (k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_1981, '#skF_5'), '#skF_2'('#skF_4', '#skF_6', '#skF_8', D_1981, '#skF_5'), '#skF_7')='#skF_8' | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_1981)), inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_855])).
% 4.63/1.84  tff(c_12, plain, (![G_21, E_19, C_14, A_12, B_13, F_20]: (k7_mcart_1(A_12, B_13, C_14, k3_mcart_1(E_19, F_20, G_21))=G_21 | k1_xboole_0=C_14 | k1_xboole_0=B_13 | k1_xboole_0=A_12 | ~m1_subset_1(k3_mcart_1(E_19, F_20, G_21), k3_zfmisc_1(A_12, B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.84  tff(c_1208, plain, (![A_2308, B_2309, C_2310, D_2311]: (k7_mcart_1(A_2308, B_2309, C_2310, k3_mcart_1('#skF_1'('#skF_4', '#skF_6', '#skF_8', D_2311, '#skF_5'), '#skF_2'('#skF_4', '#skF_6', '#skF_8', D_2311, '#skF_5'), '#skF_7'))='#skF_7' | k1_xboole_0=C_2310 | k1_xboole_0=B_2309 | k1_xboole_0=A_2308 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_2308, B_2309, C_2310)) | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_2311)), inference(superposition, [status(thm), theory('equality')], [c_928, c_12])).
% 4.63/1.84  tff(c_1217, plain, (![A_2308, B_2309, C_2310, D_207]: (k7_mcart_1(A_2308, B_2309, C_2310, '#skF_8')='#skF_7' | k1_xboole_0=C_2310 | k1_xboole_0=B_2309 | k1_xboole_0=A_2308 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_2308, B_2309, C_2310)) | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207 | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207)), inference(superposition, [status(thm), theory('equality')], [c_856, c_1208])).
% 4.63/1.84  tff(c_1241, plain, (![D_207]: (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207 | k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207)), inference(splitLeft, [status(thm)], [c_1217])).
% 4.63/1.84  tff(c_2386, plain, (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_5'), inference(factorization, [status(thm), theory('equality')], [c_1241])).
% 4.63/1.84  tff(c_1262, plain, (![D_207]: (k6_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')=D_207)), inference(factorization, [status(thm), theory('equality')], [c_1241])).
% 4.63/1.84  tff(c_3261, plain, (![D_10863]: (D_10863='#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_2386, c_1262])).
% 4.63/1.84  tff(c_3588, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3261, c_32])).
% 4.63/1.84  tff(c_3590, plain, (![A_13048, B_13049, C_13050]: (k7_mcart_1(A_13048, B_13049, C_13050, '#skF_8')='#skF_7' | k1_xboole_0=C_13050 | k1_xboole_0=B_13049 | k1_xboole_0=A_13048 | ~m1_subset_1('#skF_8', k3_zfmisc_1(A_13048, B_13049, C_13050)))), inference(splitRight, [status(thm)], [c_1217])).
% 4.63/1.84  tff(c_3597, plain, (k7_mcart_1('#skF_4', '#skF_5', '#skF_6', '#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_38, c_3590])).
% 4.63/1.84  tff(c_3599, plain, (k2_mcart_1('#skF_8')='#skF_7' | k1_xboole_0='#skF_6' | k1_xboole_0='#skF_5' | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_109, c_3597])).
% 4.63/1.84  tff(c_3601, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30, c_110, c_3599])).
% 4.63/1.84  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.84  
% 4.63/1.84  Inference rules
% 4.63/1.84  ----------------------
% 4.63/1.84  #Ref     : 0
% 4.63/1.84  #Sup     : 564
% 4.63/1.84  #Fact    : 4
% 4.63/1.84  #Define  : 0
% 4.63/1.84  #Split   : 9
% 4.63/1.84  #Chain   : 0
% 4.63/1.84  #Close   : 0
% 4.63/1.84  
% 4.63/1.84  Ordering : KBO
% 4.63/1.84  
% 4.63/1.84  Simplification rules
% 4.63/1.84  ----------------------
% 4.63/1.84  #Subsume      : 66
% 4.63/1.84  #Demod        : 140
% 4.63/1.84  #Tautology    : 83
% 4.63/1.84  #SimpNegUnit  : 28
% 4.63/1.84  #BackRed      : 1
% 4.63/1.84  
% 4.63/1.84  #Partial instantiations: 3956
% 4.63/1.84  #Strategies tried      : 1
% 4.63/1.84  
% 4.63/1.84  Timing (in seconds)
% 4.63/1.84  ----------------------
% 4.63/1.84  Preprocessing        : 0.32
% 4.63/1.84  Parsing              : 0.16
% 4.63/1.84  CNF conversion       : 0.02
% 4.63/1.84  Main loop            : 0.73
% 4.63/1.84  Inferencing          : 0.35
% 4.63/1.84  Reduction            : 0.17
% 4.63/1.84  Demodulation         : 0.12
% 4.63/1.84  BG Simplification    : 0.04
% 4.63/1.84  Subsumption          : 0.13
% 4.63/1.84  Abstraction          : 0.06
% 4.63/1.84  MUC search           : 0.00
% 4.63/1.84  Cooper               : 0.00
% 4.63/1.84  Total                : 1.08
% 4.63/1.84  Index Insertion      : 0.00
% 4.63/1.84  Index Deletion       : 0.00
% 4.63/1.84  Index Matching       : 0.00
% 4.63/1.84  BG Taut test         : 0.00
%------------------------------------------------------------------------------
