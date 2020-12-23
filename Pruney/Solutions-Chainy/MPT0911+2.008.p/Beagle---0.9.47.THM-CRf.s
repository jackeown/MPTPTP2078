%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:02 EST 2020

% Result     : Theorem 37.19s
% Output     : CNFRefutation 37.46s
% Verified   : 
% Statistics : Number of formulae       :  124 ( 360 expanded)
%              Number of leaves         :   46 ( 144 expanded)
%              Depth                    :   12
%              Number of atoms          :  225 ( 864 expanded)
%              Number of equality atoms :   87 ( 361 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_6 > #skF_3 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff(k4_zfmisc_1,type,(
    k4_zfmisc_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i * $i ) > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_44,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_173,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A,B,C,D] :
      ~ ( r1_tarski(A,k2_zfmisc_1(B,C))
        & r2_hidden(D,A)
        & ! [E,F] :
            ~ ( r2_hidden(E,B)
              & r2_hidden(F,C)
              & D = k4_tarski(E,F) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_zfmisc_1)).

tff(f_94,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_134,axiom,(
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

tff(f_100,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_114,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_98,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_108,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_102,axiom,(
    ! [A,B,C,D] : k4_zfmisc_1(A,B,C,D) = k2_zfmisc_1(k3_zfmisc_1(A,B,C),D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_zfmisc_1)).

tff(f_149,axiom,(
    ! [A,B,C,D] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0 )
    <=> k4_zfmisc_1(A,B,C,D) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_mcart_1)).

tff(c_14,plain,(
    v1_xboole_0('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_86,plain,(
    ! [A_69] :
      ( k1_xboole_0 = A_69
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_90,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_14,c_86])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_94,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_80])).

tff(c_78,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_93,plain,(
    '#skF_7' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_78])).

tff(c_76,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_92,plain,(
    '#skF_3' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_76])).

tff(c_28,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_99,plain,(
    ! [B_20] : k2_zfmisc_1('#skF_3',B_20) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_28])).

tff(c_84,plain,(
    m1_subset_1('#skF_10',k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_246,plain,(
    ! [B_101,A_102] :
      ( v1_xboole_0(B_101)
      | ~ m1_subset_1(B_101,A_102)
      | ~ v1_xboole_0(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_254,plain,
    ( v1_xboole_0('#skF_10')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_246])).

tff(c_260,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_254])).

tff(c_299,plain,(
    ! [A_111,B_112] :
      ( r2_hidden('#skF_2'(A_111,B_112),A_111)
      | r1_tarski(A_111,B_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( ~ r2_hidden('#skF_2'(A_5,B_6),B_6)
      | r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_314,plain,(
    ! [A_111] : r1_tarski(A_111,A_111) ),
    inference(resolution,[status(thm)],[c_299,c_8])).

tff(c_828,plain,(
    ! [A_185,B_186,C_187,D_188] :
      ( r2_hidden('#skF_5'(A_185,B_186,C_187,D_188),C_187)
      | ~ r2_hidden(D_188,A_185)
      | ~ r1_tarski(A_185,k2_zfmisc_1(B_186,C_187)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_42,plain,(
    ! [A_26,B_27] :
      ( m1_subset_1(A_26,B_27)
      | ~ r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_13546,plain,(
    ! [A_695,B_696,C_697,D_698] :
      ( m1_subset_1('#skF_5'(A_695,B_696,C_697,D_698),C_697)
      | ~ r2_hidden(D_698,A_695)
      | ~ r1_tarski(A_695,k2_zfmisc_1(B_696,C_697)) ) ),
    inference(resolution,[status(thm)],[c_828,c_42])).

tff(c_13626,plain,(
    ! [B_696,C_697,D_698] :
      ( m1_subset_1('#skF_5'(k2_zfmisc_1(B_696,C_697),B_696,C_697,D_698),C_697)
      | ~ r2_hidden(D_698,k2_zfmisc_1(B_696,C_697)) ) ),
    inference(resolution,[status(thm)],[c_314,c_13546])).

tff(c_743,plain,(
    ! [A_175,B_176,C_177,D_178] :
      ( r2_hidden('#skF_4'(A_175,B_176,C_177,D_178),B_176)
      | ~ r2_hidden(D_178,A_175)
      | ~ r1_tarski(A_175,k2_zfmisc_1(B_176,C_177)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14826,plain,(
    ! [A_717,B_718,C_719,D_720] :
      ( m1_subset_1('#skF_4'(A_717,B_718,C_719,D_720),B_718)
      | ~ r2_hidden(D_720,A_717)
      | ~ r1_tarski(A_717,k2_zfmisc_1(B_718,C_719)) ) ),
    inference(resolution,[status(thm)],[c_743,c_42])).

tff(c_146685,plain,(
    ! [B_3193,C_3194,D_3195] :
      ( m1_subset_1('#skF_4'(k2_zfmisc_1(B_3193,C_3194),B_3193,C_3194,D_3195),B_3193)
      | ~ r2_hidden(D_3195,k2_zfmisc_1(B_3193,C_3194)) ) ),
    inference(resolution,[status(thm)],[c_314,c_14826])).

tff(c_58,plain,(
    ! [A_45,B_46,C_47,D_49] :
      ( k7_mcart_1(A_45,B_46,C_47,D_49) = k2_mcart_1(D_49)
      | ~ m1_subset_1(D_49,k3_zfmisc_1(A_45,B_46,C_47))
      | k1_xboole_0 = C_47
      | k1_xboole_0 = B_46
      | k1_xboole_0 = A_45 ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_980,plain,(
    ! [A_204,B_205,C_206,D_207] :
      ( k7_mcart_1(A_204,B_205,C_206,D_207) = k2_mcart_1(D_207)
      | ~ m1_subset_1(D_207,k3_zfmisc_1(A_204,B_205,C_206))
      | C_206 = '#skF_3'
      | B_205 = '#skF_3'
      | A_204 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_90,c_58])).

tff(c_1008,plain,
    ( k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10')
    | '#skF_3' = '#skF_8'
    | '#skF_7' = '#skF_3'
    | '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_84,c_980])).

tff(c_1018,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') = k2_mcart_1('#skF_10') ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_93,c_92,c_1008])).

tff(c_74,plain,(
    k7_mcart_1('#skF_6','#skF_7','#skF_8','#skF_10') != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_1019,plain,(
    k2_mcart_1('#skF_10') != '#skF_9' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1018,c_74])).

tff(c_387,plain,(
    ! [A_131,B_132,C_133] : k2_zfmisc_1(k2_zfmisc_1(A_131,B_132),C_133) = k3_zfmisc_1(A_131,B_132,C_133) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_44,plain,(
    ! [A_28,B_29] : v1_relat_1(k2_zfmisc_1(A_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_405,plain,(
    ! [A_131,B_132,C_133] : v1_relat_1(k3_zfmisc_1(A_131,B_132,C_133)) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_44])).

tff(c_34,plain,(
    ! [B_24,A_23] :
      ( r2_hidden(B_24,A_23)
      | ~ m1_subset_1(B_24,A_23)
      | v1_xboole_0(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_431,plain,(
    ! [A_137,B_138] :
      ( k4_tarski(k1_mcart_1(A_137),k2_mcart_1(A_137)) = A_137
      | ~ r2_hidden(A_137,B_138)
      | ~ v1_relat_1(B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_114])).

tff(c_11157,plain,(
    ! [B_633,A_634] :
      ( k4_tarski(k1_mcart_1(B_633),k2_mcart_1(B_633)) = B_633
      | ~ v1_relat_1(A_634)
      | ~ m1_subset_1(B_633,A_634)
      | v1_xboole_0(A_634) ) ),
    inference(resolution,[status(thm)],[c_34,c_431])).

tff(c_11167,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_6','#skF_7','#skF_8'))
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_11157])).

tff(c_11174,plain,
    ( k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10'
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_11167])).

tff(c_11175,plain,(
    k4_tarski(k1_mcart_1('#skF_10'),k2_mcart_1('#skF_10')) = '#skF_10' ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_11174])).

tff(c_1123,plain,(
    ! [A_221,B_222,C_223,D_224] :
      ( k4_tarski('#skF_4'(A_221,B_222,C_223,D_224),'#skF_5'(A_221,B_222,C_223,D_224)) = D_224
      | ~ r2_hidden(D_224,A_221)
      | ~ r1_tarski(A_221,k2_zfmisc_1(B_222,C_223)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_46,plain,(
    ! [A_30,B_31,C_32] : k4_tarski(k4_tarski(A_30,B_31),C_32) = k3_mcart_1(A_30,B_31,C_32) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_23125,plain,(
    ! [D_928,C_924,A_927,C_925,B_926] :
      ( k3_mcart_1('#skF_4'(A_927,B_926,C_924,D_928),'#skF_5'(A_927,B_926,C_924,D_928),C_925) = k4_tarski(D_928,C_925)
      | ~ r2_hidden(D_928,A_927)
      | ~ r1_tarski(A_927,k2_zfmisc_1(B_926,C_924)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1123,c_46])).

tff(c_82,plain,(
    ! [H_67,F_61,G_65] :
      ( H_67 = '#skF_9'
      | k3_mcart_1(F_61,G_65,H_67) != '#skF_10'
      | ~ m1_subset_1(H_67,'#skF_8')
      | ~ m1_subset_1(G_65,'#skF_7')
      | ~ m1_subset_1(F_61,'#skF_6') ) ),
    inference(cnfTransformation,[status(thm)],[f_173])).

tff(c_23667,plain,(
    ! [A_947,B_943,C_946,D_945,C_944] :
      ( C_944 = '#skF_9'
      | k4_tarski(D_945,C_944) != '#skF_10'
      | ~ m1_subset_1(C_944,'#skF_8')
      | ~ m1_subset_1('#skF_5'(A_947,B_943,C_946,D_945),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_947,B_943,C_946,D_945),'#skF_6')
      | ~ r2_hidden(D_945,A_947)
      | ~ r1_tarski(A_947,k2_zfmisc_1(B_943,C_946)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_23125,c_82])).

tff(c_23671,plain,(
    ! [A_947,B_943,C_946] :
      ( k2_mcart_1('#skF_10') = '#skF_9'
      | ~ m1_subset_1(k2_mcart_1('#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_5'(A_947,B_943,C_946,k1_mcart_1('#skF_10')),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_947,B_943,C_946,k1_mcart_1('#skF_10')),'#skF_6')
      | ~ r2_hidden(k1_mcart_1('#skF_10'),A_947)
      | ~ r1_tarski(A_947,k2_zfmisc_1(B_943,C_946)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11175,c_23667])).

tff(c_23680,plain,(
    ! [A_947,B_943,C_946] :
      ( ~ m1_subset_1(k2_mcart_1('#skF_10'),'#skF_8')
      | ~ m1_subset_1('#skF_5'(A_947,B_943,C_946,k1_mcart_1('#skF_10')),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_947,B_943,C_946,k1_mcart_1('#skF_10')),'#skF_6')
      | ~ r2_hidden(k1_mcart_1('#skF_10'),A_947)
      | ~ r1_tarski(A_947,k2_zfmisc_1(B_943,C_946)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_1019,c_23671])).

tff(c_24621,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_10'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_23680])).

tff(c_48,plain,(
    ! [A_33,B_34,C_35] : k2_zfmisc_1(k2_zfmisc_1(A_33,B_34),C_35) = k3_zfmisc_1(A_33,B_34,C_35) ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_369,plain,(
    ! [A_128,C_129,B_130] :
      ( r2_hidden(k2_mcart_1(A_128),C_129)
      | ~ r2_hidden(A_128,k2_zfmisc_1(B_130,C_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_10442,plain,(
    ! [B_616,C_617,B_618] :
      ( r2_hidden(k2_mcart_1(B_616),C_617)
      | ~ m1_subset_1(B_616,k2_zfmisc_1(B_618,C_617))
      | v1_xboole_0(k2_zfmisc_1(B_618,C_617)) ) ),
    inference(resolution,[status(thm)],[c_34,c_369])).

tff(c_10467,plain,(
    ! [B_616,C_35,A_33,B_34] :
      ( r2_hidden(k2_mcart_1(B_616),C_35)
      | ~ m1_subset_1(B_616,k3_zfmisc_1(A_33,B_34,C_35))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_33,B_34),C_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_10442])).

tff(c_96656,plain,(
    ! [B_2285,C_2286,A_2287,B_2288] :
      ( r2_hidden(k2_mcart_1(B_2285),C_2286)
      | ~ m1_subset_1(B_2285,k3_zfmisc_1(A_2287,B_2288,C_2286))
      | v1_xboole_0(k3_zfmisc_1(A_2287,B_2288,C_2286)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_10467])).

tff(c_96773,plain,
    ( r2_hidden(k2_mcart_1('#skF_10'),'#skF_8')
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_96656])).

tff(c_96796,plain,(
    r2_hidden(k2_mcart_1('#skF_10'),'#skF_8') ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_96773])).

tff(c_96822,plain,(
    m1_subset_1(k2_mcart_1('#skF_10'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_96796,c_42])).

tff(c_96840,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24621,c_96822])).

tff(c_96841,plain,(
    ! [A_947,B_943,C_946] :
      ( ~ m1_subset_1('#skF_5'(A_947,B_943,C_946,k1_mcart_1('#skF_10')),'#skF_7')
      | ~ m1_subset_1('#skF_4'(A_947,B_943,C_946,k1_mcart_1('#skF_10')),'#skF_6')
      | ~ r2_hidden(k1_mcart_1('#skF_10'),A_947)
      | ~ r1_tarski(A_947,k2_zfmisc_1(B_943,C_946)) ) ),
    inference(splitRight,[status(thm)],[c_23680])).

tff(c_146716,plain,(
    ! [C_3194] :
      ( ~ m1_subset_1('#skF_5'(k2_zfmisc_1('#skF_6',C_3194),'#skF_6',C_3194,k1_mcart_1('#skF_10')),'#skF_7')
      | ~ r1_tarski(k2_zfmisc_1('#skF_6',C_3194),k2_zfmisc_1('#skF_6',C_3194))
      | ~ r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_6',C_3194)) ) ),
    inference(resolution,[status(thm)],[c_146685,c_96841])).

tff(c_157363,plain,(
    ! [C_3336] :
      ( ~ m1_subset_1('#skF_5'(k2_zfmisc_1('#skF_6',C_3336),'#skF_6',C_3336,k1_mcart_1('#skF_10')),'#skF_7')
      | ~ r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_6',C_3336)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_146716])).

tff(c_157487,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_13626,c_157363])).

tff(c_54,plain,(
    ! [A_40,B_41,C_42] :
      ( r2_hidden(k1_mcart_1(A_40),B_41)
      | ~ r2_hidden(A_40,k2_zfmisc_1(B_41,C_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_7017,plain,(
    ! [A_524,A_525,B_526,C_527] :
      ( r2_hidden(k1_mcart_1(A_524),k2_zfmisc_1(A_525,B_526))
      | ~ r2_hidden(A_524,k3_zfmisc_1(A_525,B_526,C_527)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_387,c_54])).

tff(c_211208,plain,(
    ! [B_4244,A_4245,B_4246,C_4247] :
      ( r2_hidden(k1_mcart_1(B_4244),k2_zfmisc_1(A_4245,B_4246))
      | ~ m1_subset_1(B_4244,k3_zfmisc_1(A_4245,B_4246,C_4247))
      | v1_xboole_0(k3_zfmisc_1(A_4245,B_4246,C_4247)) ) ),
    inference(resolution,[status(thm)],[c_34,c_7017])).

tff(c_211328,plain,
    ( r2_hidden(k1_mcart_1('#skF_10'),k2_zfmisc_1('#skF_6','#skF_7'))
    | v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_84,c_211208])).

tff(c_211354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_260,c_157487,c_211328])).

tff(c_211356,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_6','#skF_7','#skF_8')) ),
    inference(splitRight,[status(thm)],[c_254])).

tff(c_12,plain,(
    ! [A_10] :
      ( k1_xboole_0 = A_10
      | ~ v1_xboole_0(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_91,plain,(
    ! [A_10] :
      ( A_10 = '#skF_3'
      | ~ v1_xboole_0(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_12])).

tff(c_211385,plain,(
    k3_zfmisc_1('#skF_6','#skF_7','#skF_8') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_211356,c_91])).

tff(c_211739,plain,(
    ! [A_4299,B_4300,C_4301,D_4302] : k2_zfmisc_1(k3_zfmisc_1(A_4299,B_4300,C_4301),D_4302) = k4_zfmisc_1(A_4299,B_4300,C_4301,D_4302) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_211782,plain,(
    ! [D_4302] : k4_zfmisc_1('#skF_6','#skF_7','#skF_8',D_4302) = k2_zfmisc_1('#skF_3',D_4302) ),
    inference(superposition,[status(thm),theory(equality)],[c_211385,c_211739])).

tff(c_211794,plain,(
    ! [D_4302] : k4_zfmisc_1('#skF_6','#skF_7','#skF_8',D_4302) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_99,c_211782])).

tff(c_64,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k4_zfmisc_1(A_50,B_51,C_52,D_53) != k1_xboole_0
      | k1_xboole_0 = D_53
      | k1_xboole_0 = C_52
      | k1_xboole_0 = B_51
      | k1_xboole_0 = A_50 ) ),
    inference(cnfTransformation,[status(thm)],[f_149])).

tff(c_211867,plain,(
    ! [A_4314,B_4315,C_4316,D_4317] :
      ( k4_zfmisc_1(A_4314,B_4315,C_4316,D_4317) != '#skF_3'
      | D_4317 = '#skF_3'
      | C_4316 = '#skF_3'
      | B_4315 = '#skF_3'
      | A_4314 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_90,c_90,c_90,c_90,c_64])).

tff(c_211870,plain,(
    ! [D_4302] :
      ( D_4302 = '#skF_3'
      | '#skF_3' = '#skF_8'
      | '#skF_7' = '#skF_3'
      | '#skF_6' = '#skF_3' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_211794,c_211867])).

tff(c_211894,plain,(
    ! [D_4318] : D_4318 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_93,c_92,c_211870])).

tff(c_212008,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_211894,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:59:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 37.19/27.91  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.19/27.92  
% 37.19/27.92  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.19/27.92  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k4_zfmisc_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_zfmisc_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_10 > #skF_6 > #skF_3 > #skF_9 > #skF_4 > #skF_8 > #skF_5 > #skF_2
% 37.19/27.92  
% 37.19/27.92  %Foreground sorts:
% 37.19/27.92  
% 37.19/27.92  
% 37.19/27.92  %Background operators:
% 37.19/27.92  
% 37.19/27.92  
% 37.19/27.92  %Foreground operators:
% 37.19/27.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 37.19/27.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 37.19/27.92  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 37.19/27.92  tff('#skF_1', type, '#skF_1': $i > $i).
% 37.19/27.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 37.19/27.92  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 37.19/27.92  tff(k4_zfmisc_1, type, k4_zfmisc_1: ($i * $i * $i * $i) > $i).
% 37.19/27.92  tff('#skF_7', type, '#skF_7': $i).
% 37.19/27.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 37.19/27.92  tff('#skF_10', type, '#skF_10': $i).
% 37.19/27.92  tff('#skF_6', type, '#skF_6': $i).
% 37.19/27.92  tff('#skF_3', type, '#skF_3': $i).
% 37.19/27.92  tff('#skF_9', type, '#skF_9': $i).
% 37.19/27.92  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 37.19/27.92  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 37.19/27.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 37.19/27.92  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 37.19/27.92  tff('#skF_8', type, '#skF_8': $i).
% 37.19/27.92  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 37.19/27.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 37.19/27.92  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 37.19/27.92  tff('#skF_5', type, '#skF_5': ($i * $i * $i * $i) > $i).
% 37.19/27.92  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 37.19/27.92  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 37.19/27.92  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 37.19/27.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 37.19/27.92  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 37.19/27.92  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 37.19/27.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 37.19/27.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 37.19/27.92  
% 37.46/27.95  tff(f_44, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_xboole_0)).
% 37.46/27.95  tff(f_42, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 37.46/27.95  tff(f_173, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 37.46/27.95  tff(f_71, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 37.46/27.95  tff(f_87, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 37.46/27.95  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 37.46/27.95  tff(f_65, axiom, (![A, B, C, D]: ~((r1_tarski(A, k2_zfmisc_1(B, C)) & r2_hidden(D, A)) & (![E, F]: ~((r2_hidden(E, B) & r2_hidden(F, C)) & (D = k4_tarski(E, F)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t103_zfmisc_1)).
% 37.46/27.95  tff(f_94, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 37.46/27.95  tff(f_134, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 37.46/27.95  tff(f_100, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 37.46/27.95  tff(f_96, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 37.46/27.95  tff(f_114, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 37.46/27.95  tff(f_98, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 37.46/27.95  tff(f_108, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 37.46/27.95  tff(f_102, axiom, (![A, B, C, D]: (k4_zfmisc_1(A, B, C, D) = k2_zfmisc_1(k3_zfmisc_1(A, B, C), D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_zfmisc_1)).
% 37.46/27.95  tff(f_149, axiom, (![A, B, C, D]: ((((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(D = k1_xboole_0)) <=> ~(k4_zfmisc_1(A, B, C, D) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_mcart_1)).
% 37.46/27.95  tff(c_14, plain, (v1_xboole_0('#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 37.46/27.95  tff(c_86, plain, (![A_69]: (k1_xboole_0=A_69 | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_42])).
% 37.46/27.95  tff(c_90, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_14, c_86])).
% 37.46/27.95  tff(c_80, plain, (k1_xboole_0!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_173])).
% 37.46/27.95  tff(c_94, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_80])).
% 37.46/27.95  tff(c_78, plain, (k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_173])).
% 37.46/27.95  tff(c_93, plain, ('#skF_7'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_78])).
% 37.46/27.95  tff(c_76, plain, (k1_xboole_0!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_173])).
% 37.46/27.95  tff(c_92, plain, ('#skF_3'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_76])).
% 37.46/27.95  tff(c_28, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_71])).
% 37.46/27.95  tff(c_99, plain, (![B_20]: (k2_zfmisc_1('#skF_3', B_20)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_28])).
% 37.46/27.95  tff(c_84, plain, (m1_subset_1('#skF_10', k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 37.46/27.95  tff(c_246, plain, (![B_101, A_102]: (v1_xboole_0(B_101) | ~m1_subset_1(B_101, A_102) | ~v1_xboole_0(A_102))), inference(cnfTransformation, [status(thm)], [f_87])).
% 37.46/27.95  tff(c_254, plain, (v1_xboole_0('#skF_10') | ~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_246])).
% 37.46/27.95  tff(c_260, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitLeft, [status(thm)], [c_254])).
% 37.46/27.95  tff(c_299, plain, (![A_111, B_112]: (r2_hidden('#skF_2'(A_111, B_112), A_111) | r1_tarski(A_111, B_112))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.46/27.95  tff(c_8, plain, (![A_5, B_6]: (~r2_hidden('#skF_2'(A_5, B_6), B_6) | r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_38])).
% 37.46/27.95  tff(c_314, plain, (![A_111]: (r1_tarski(A_111, A_111))), inference(resolution, [status(thm)], [c_299, c_8])).
% 37.46/27.95  tff(c_828, plain, (![A_185, B_186, C_187, D_188]: (r2_hidden('#skF_5'(A_185, B_186, C_187, D_188), C_187) | ~r2_hidden(D_188, A_185) | ~r1_tarski(A_185, k2_zfmisc_1(B_186, C_187)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 37.46/27.95  tff(c_42, plain, (![A_26, B_27]: (m1_subset_1(A_26, B_27) | ~r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_94])).
% 37.46/27.95  tff(c_13546, plain, (![A_695, B_696, C_697, D_698]: (m1_subset_1('#skF_5'(A_695, B_696, C_697, D_698), C_697) | ~r2_hidden(D_698, A_695) | ~r1_tarski(A_695, k2_zfmisc_1(B_696, C_697)))), inference(resolution, [status(thm)], [c_828, c_42])).
% 37.46/27.95  tff(c_13626, plain, (![B_696, C_697, D_698]: (m1_subset_1('#skF_5'(k2_zfmisc_1(B_696, C_697), B_696, C_697, D_698), C_697) | ~r2_hidden(D_698, k2_zfmisc_1(B_696, C_697)))), inference(resolution, [status(thm)], [c_314, c_13546])).
% 37.46/27.95  tff(c_743, plain, (![A_175, B_176, C_177, D_178]: (r2_hidden('#skF_4'(A_175, B_176, C_177, D_178), B_176) | ~r2_hidden(D_178, A_175) | ~r1_tarski(A_175, k2_zfmisc_1(B_176, C_177)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 37.46/27.95  tff(c_14826, plain, (![A_717, B_718, C_719, D_720]: (m1_subset_1('#skF_4'(A_717, B_718, C_719, D_720), B_718) | ~r2_hidden(D_720, A_717) | ~r1_tarski(A_717, k2_zfmisc_1(B_718, C_719)))), inference(resolution, [status(thm)], [c_743, c_42])).
% 37.46/27.95  tff(c_146685, plain, (![B_3193, C_3194, D_3195]: (m1_subset_1('#skF_4'(k2_zfmisc_1(B_3193, C_3194), B_3193, C_3194, D_3195), B_3193) | ~r2_hidden(D_3195, k2_zfmisc_1(B_3193, C_3194)))), inference(resolution, [status(thm)], [c_314, c_14826])).
% 37.46/27.95  tff(c_58, plain, (![A_45, B_46, C_47, D_49]: (k7_mcart_1(A_45, B_46, C_47, D_49)=k2_mcart_1(D_49) | ~m1_subset_1(D_49, k3_zfmisc_1(A_45, B_46, C_47)) | k1_xboole_0=C_47 | k1_xboole_0=B_46 | k1_xboole_0=A_45)), inference(cnfTransformation, [status(thm)], [f_134])).
% 37.46/27.95  tff(c_980, plain, (![A_204, B_205, C_206, D_207]: (k7_mcart_1(A_204, B_205, C_206, D_207)=k2_mcart_1(D_207) | ~m1_subset_1(D_207, k3_zfmisc_1(A_204, B_205, C_206)) | C_206='#skF_3' | B_205='#skF_3' | A_204='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_90, c_58])).
% 37.46/27.95  tff(c_1008, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10') | '#skF_3'='#skF_8' | '#skF_7'='#skF_3' | '#skF_6'='#skF_3'), inference(resolution, [status(thm)], [c_84, c_980])).
% 37.46/27.95  tff(c_1018, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')=k2_mcart_1('#skF_10')), inference(negUnitSimplification, [status(thm)], [c_94, c_93, c_92, c_1008])).
% 37.46/27.95  tff(c_74, plain, (k7_mcart_1('#skF_6', '#skF_7', '#skF_8', '#skF_10')!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_173])).
% 37.46/27.95  tff(c_1019, plain, (k2_mcart_1('#skF_10')!='#skF_9'), inference(demodulation, [status(thm), theory('equality')], [c_1018, c_74])).
% 37.46/27.95  tff(c_387, plain, (![A_131, B_132, C_133]: (k2_zfmisc_1(k2_zfmisc_1(A_131, B_132), C_133)=k3_zfmisc_1(A_131, B_132, C_133))), inference(cnfTransformation, [status(thm)], [f_100])).
% 37.46/27.95  tff(c_44, plain, (![A_28, B_29]: (v1_relat_1(k2_zfmisc_1(A_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_96])).
% 37.46/27.95  tff(c_405, plain, (![A_131, B_132, C_133]: (v1_relat_1(k3_zfmisc_1(A_131, B_132, C_133)))), inference(superposition, [status(thm), theory('equality')], [c_387, c_44])).
% 37.46/27.95  tff(c_34, plain, (![B_24, A_23]: (r2_hidden(B_24, A_23) | ~m1_subset_1(B_24, A_23) | v1_xboole_0(A_23))), inference(cnfTransformation, [status(thm)], [f_87])).
% 37.46/27.95  tff(c_431, plain, (![A_137, B_138]: (k4_tarski(k1_mcart_1(A_137), k2_mcart_1(A_137))=A_137 | ~r2_hidden(A_137, B_138) | ~v1_relat_1(B_138))), inference(cnfTransformation, [status(thm)], [f_114])).
% 37.46/27.95  tff(c_11157, plain, (![B_633, A_634]: (k4_tarski(k1_mcart_1(B_633), k2_mcart_1(B_633))=B_633 | ~v1_relat_1(A_634) | ~m1_subset_1(B_633, A_634) | v1_xboole_0(A_634))), inference(resolution, [status(thm)], [c_34, c_431])).
% 37.46/27.95  tff(c_11167, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | ~v1_relat_1(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')) | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_11157])).
% 37.46/27.95  tff(c_11174, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10' | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_405, c_11167])).
% 37.46/27.95  tff(c_11175, plain, (k4_tarski(k1_mcart_1('#skF_10'), k2_mcart_1('#skF_10'))='#skF_10'), inference(negUnitSimplification, [status(thm)], [c_260, c_11174])).
% 37.46/27.95  tff(c_1123, plain, (![A_221, B_222, C_223, D_224]: (k4_tarski('#skF_4'(A_221, B_222, C_223, D_224), '#skF_5'(A_221, B_222, C_223, D_224))=D_224 | ~r2_hidden(D_224, A_221) | ~r1_tarski(A_221, k2_zfmisc_1(B_222, C_223)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 37.46/27.95  tff(c_46, plain, (![A_30, B_31, C_32]: (k4_tarski(k4_tarski(A_30, B_31), C_32)=k3_mcart_1(A_30, B_31, C_32))), inference(cnfTransformation, [status(thm)], [f_98])).
% 37.46/27.95  tff(c_23125, plain, (![D_928, C_924, A_927, C_925, B_926]: (k3_mcart_1('#skF_4'(A_927, B_926, C_924, D_928), '#skF_5'(A_927, B_926, C_924, D_928), C_925)=k4_tarski(D_928, C_925) | ~r2_hidden(D_928, A_927) | ~r1_tarski(A_927, k2_zfmisc_1(B_926, C_924)))), inference(superposition, [status(thm), theory('equality')], [c_1123, c_46])).
% 37.46/27.95  tff(c_82, plain, (![H_67, F_61, G_65]: (H_67='#skF_9' | k3_mcart_1(F_61, G_65, H_67)!='#skF_10' | ~m1_subset_1(H_67, '#skF_8') | ~m1_subset_1(G_65, '#skF_7') | ~m1_subset_1(F_61, '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_173])).
% 37.46/27.95  tff(c_23667, plain, (![A_947, B_943, C_946, D_945, C_944]: (C_944='#skF_9' | k4_tarski(D_945, C_944)!='#skF_10' | ~m1_subset_1(C_944, '#skF_8') | ~m1_subset_1('#skF_5'(A_947, B_943, C_946, D_945), '#skF_7') | ~m1_subset_1('#skF_4'(A_947, B_943, C_946, D_945), '#skF_6') | ~r2_hidden(D_945, A_947) | ~r1_tarski(A_947, k2_zfmisc_1(B_943, C_946)))), inference(superposition, [status(thm), theory('equality')], [c_23125, c_82])).
% 37.46/27.95  tff(c_23671, plain, (![A_947, B_943, C_946]: (k2_mcart_1('#skF_10')='#skF_9' | ~m1_subset_1(k2_mcart_1('#skF_10'), '#skF_8') | ~m1_subset_1('#skF_5'(A_947, B_943, C_946, k1_mcart_1('#skF_10')), '#skF_7') | ~m1_subset_1('#skF_4'(A_947, B_943, C_946, k1_mcart_1('#skF_10')), '#skF_6') | ~r2_hidden(k1_mcart_1('#skF_10'), A_947) | ~r1_tarski(A_947, k2_zfmisc_1(B_943, C_946)))), inference(superposition, [status(thm), theory('equality')], [c_11175, c_23667])).
% 37.46/27.95  tff(c_23680, plain, (![A_947, B_943, C_946]: (~m1_subset_1(k2_mcart_1('#skF_10'), '#skF_8') | ~m1_subset_1('#skF_5'(A_947, B_943, C_946, k1_mcart_1('#skF_10')), '#skF_7') | ~m1_subset_1('#skF_4'(A_947, B_943, C_946, k1_mcart_1('#skF_10')), '#skF_6') | ~r2_hidden(k1_mcart_1('#skF_10'), A_947) | ~r1_tarski(A_947, k2_zfmisc_1(B_943, C_946)))), inference(negUnitSimplification, [status(thm)], [c_1019, c_23671])).
% 37.46/27.95  tff(c_24621, plain, (~m1_subset_1(k2_mcart_1('#skF_10'), '#skF_8')), inference(splitLeft, [status(thm)], [c_23680])).
% 37.46/27.95  tff(c_48, plain, (![A_33, B_34, C_35]: (k2_zfmisc_1(k2_zfmisc_1(A_33, B_34), C_35)=k3_zfmisc_1(A_33, B_34, C_35))), inference(cnfTransformation, [status(thm)], [f_100])).
% 37.46/27.95  tff(c_369, plain, (![A_128, C_129, B_130]: (r2_hidden(k2_mcart_1(A_128), C_129) | ~r2_hidden(A_128, k2_zfmisc_1(B_130, C_129)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.46/27.95  tff(c_10442, plain, (![B_616, C_617, B_618]: (r2_hidden(k2_mcart_1(B_616), C_617) | ~m1_subset_1(B_616, k2_zfmisc_1(B_618, C_617)) | v1_xboole_0(k2_zfmisc_1(B_618, C_617)))), inference(resolution, [status(thm)], [c_34, c_369])).
% 37.46/27.95  tff(c_10467, plain, (![B_616, C_35, A_33, B_34]: (r2_hidden(k2_mcart_1(B_616), C_35) | ~m1_subset_1(B_616, k3_zfmisc_1(A_33, B_34, C_35)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_33, B_34), C_35)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_10442])).
% 37.46/27.95  tff(c_96656, plain, (![B_2285, C_2286, A_2287, B_2288]: (r2_hidden(k2_mcart_1(B_2285), C_2286) | ~m1_subset_1(B_2285, k3_zfmisc_1(A_2287, B_2288, C_2286)) | v1_xboole_0(k3_zfmisc_1(A_2287, B_2288, C_2286)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_10467])).
% 37.46/27.95  tff(c_96773, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_8') | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_96656])).
% 37.46/27.95  tff(c_96796, plain, (r2_hidden(k2_mcart_1('#skF_10'), '#skF_8')), inference(negUnitSimplification, [status(thm)], [c_260, c_96773])).
% 37.46/27.95  tff(c_96822, plain, (m1_subset_1(k2_mcart_1('#skF_10'), '#skF_8')), inference(resolution, [status(thm)], [c_96796, c_42])).
% 37.46/27.95  tff(c_96840, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24621, c_96822])).
% 37.46/27.95  tff(c_96841, plain, (![A_947, B_943, C_946]: (~m1_subset_1('#skF_5'(A_947, B_943, C_946, k1_mcart_1('#skF_10')), '#skF_7') | ~m1_subset_1('#skF_4'(A_947, B_943, C_946, k1_mcart_1('#skF_10')), '#skF_6') | ~r2_hidden(k1_mcart_1('#skF_10'), A_947) | ~r1_tarski(A_947, k2_zfmisc_1(B_943, C_946)))), inference(splitRight, [status(thm)], [c_23680])).
% 37.46/27.95  tff(c_146716, plain, (![C_3194]: (~m1_subset_1('#skF_5'(k2_zfmisc_1('#skF_6', C_3194), '#skF_6', C_3194, k1_mcart_1('#skF_10')), '#skF_7') | ~r1_tarski(k2_zfmisc_1('#skF_6', C_3194), k2_zfmisc_1('#skF_6', C_3194)) | ~r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_6', C_3194)))), inference(resolution, [status(thm)], [c_146685, c_96841])).
% 37.46/27.95  tff(c_157363, plain, (![C_3336]: (~m1_subset_1('#skF_5'(k2_zfmisc_1('#skF_6', C_3336), '#skF_6', C_3336, k1_mcart_1('#skF_10')), '#skF_7') | ~r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_6', C_3336)))), inference(demodulation, [status(thm), theory('equality')], [c_314, c_146716])).
% 37.46/27.95  tff(c_157487, plain, (~r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_13626, c_157363])).
% 37.46/27.95  tff(c_54, plain, (![A_40, B_41, C_42]: (r2_hidden(k1_mcart_1(A_40), B_41) | ~r2_hidden(A_40, k2_zfmisc_1(B_41, C_42)))), inference(cnfTransformation, [status(thm)], [f_108])).
% 37.46/27.95  tff(c_7017, plain, (![A_524, A_525, B_526, C_527]: (r2_hidden(k1_mcart_1(A_524), k2_zfmisc_1(A_525, B_526)) | ~r2_hidden(A_524, k3_zfmisc_1(A_525, B_526, C_527)))), inference(superposition, [status(thm), theory('equality')], [c_387, c_54])).
% 37.46/27.95  tff(c_211208, plain, (![B_4244, A_4245, B_4246, C_4247]: (r2_hidden(k1_mcart_1(B_4244), k2_zfmisc_1(A_4245, B_4246)) | ~m1_subset_1(B_4244, k3_zfmisc_1(A_4245, B_4246, C_4247)) | v1_xboole_0(k3_zfmisc_1(A_4245, B_4246, C_4247)))), inference(resolution, [status(thm)], [c_34, c_7017])).
% 37.46/27.95  tff(c_211328, plain, (r2_hidden(k1_mcart_1('#skF_10'), k2_zfmisc_1('#skF_6', '#skF_7')) | v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_84, c_211208])).
% 37.46/27.95  tff(c_211354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_260, c_157487, c_211328])).
% 37.46/27.95  tff(c_211356, plain, (v1_xboole_0(k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8'))), inference(splitRight, [status(thm)], [c_254])).
% 37.46/27.95  tff(c_12, plain, (![A_10]: (k1_xboole_0=A_10 | ~v1_xboole_0(A_10))), inference(cnfTransformation, [status(thm)], [f_42])).
% 37.46/27.95  tff(c_91, plain, (![A_10]: (A_10='#skF_3' | ~v1_xboole_0(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_90, c_12])).
% 37.46/27.95  tff(c_211385, plain, (k3_zfmisc_1('#skF_6', '#skF_7', '#skF_8')='#skF_3'), inference(resolution, [status(thm)], [c_211356, c_91])).
% 37.46/27.95  tff(c_211739, plain, (![A_4299, B_4300, C_4301, D_4302]: (k2_zfmisc_1(k3_zfmisc_1(A_4299, B_4300, C_4301), D_4302)=k4_zfmisc_1(A_4299, B_4300, C_4301, D_4302))), inference(cnfTransformation, [status(thm)], [f_102])).
% 37.46/27.95  tff(c_211782, plain, (![D_4302]: (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', D_4302)=k2_zfmisc_1('#skF_3', D_4302))), inference(superposition, [status(thm), theory('equality')], [c_211385, c_211739])).
% 37.46/27.95  tff(c_211794, plain, (![D_4302]: (k4_zfmisc_1('#skF_6', '#skF_7', '#skF_8', D_4302)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_99, c_211782])).
% 37.46/27.95  tff(c_64, plain, (![A_50, B_51, C_52, D_53]: (k4_zfmisc_1(A_50, B_51, C_52, D_53)!=k1_xboole_0 | k1_xboole_0=D_53 | k1_xboole_0=C_52 | k1_xboole_0=B_51 | k1_xboole_0=A_50)), inference(cnfTransformation, [status(thm)], [f_149])).
% 37.46/27.95  tff(c_211867, plain, (![A_4314, B_4315, C_4316, D_4317]: (k4_zfmisc_1(A_4314, B_4315, C_4316, D_4317)!='#skF_3' | D_4317='#skF_3' | C_4316='#skF_3' | B_4315='#skF_3' | A_4314='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_90, c_90, c_90, c_90, c_90, c_64])).
% 37.46/27.95  tff(c_211870, plain, (![D_4302]: (D_4302='#skF_3' | '#skF_3'='#skF_8' | '#skF_7'='#skF_3' | '#skF_6'='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_211794, c_211867])).
% 37.46/27.95  tff(c_211894, plain, (![D_4318]: (D_4318='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_94, c_93, c_92, c_211870])).
% 37.46/27.95  tff(c_212008, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_211894, c_94])).
% 37.46/27.95  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 37.46/27.95  
% 37.46/27.95  Inference rules
% 37.46/27.95  ----------------------
% 37.46/27.95  #Ref     : 0
% 37.46/27.95  #Sup     : 57109
% 37.46/27.95  #Fact    : 0
% 37.46/27.95  #Define  : 0
% 37.46/27.95  #Split   : 34
% 37.46/27.95  #Chain   : 0
% 37.46/27.95  #Close   : 0
% 37.46/27.95  
% 37.46/27.95  Ordering : KBO
% 37.46/27.95  
% 37.46/27.95  Simplification rules
% 37.46/27.95  ----------------------
% 37.46/27.95  #Subsume      : 20683
% 37.46/27.95  #Demod        : 32702
% 37.46/27.95  #Tautology    : 24527
% 37.46/27.95  #SimpNegUnit  : 2481
% 37.46/27.95  #BackRed      : 1053
% 37.46/27.95  
% 37.46/27.95  #Partial instantiations: 88
% 37.46/27.95  #Strategies tried      : 1
% 37.46/27.95  
% 37.46/27.95  Timing (in seconds)
% 37.46/27.95  ----------------------
% 37.46/27.95  Preprocessing        : 0.43
% 37.46/27.95  Parsing              : 0.24
% 37.46/27.95  CNF conversion       : 0.03
% 37.46/27.95  Main loop            : 26.58
% 37.46/27.95  Inferencing          : 3.53
% 37.50/27.95  Reduction            : 6.27
% 37.50/27.95  Demodulation         : 4.35
% 37.50/27.95  BG Simplification    : 0.37
% 37.50/27.95  Subsumption          : 15.10
% 37.50/27.95  Abstraction          : 0.60
% 37.50/27.95  MUC search           : 0.00
% 37.50/27.95  Cooper               : 0.00
% 37.50/27.95  Total                : 27.06
% 37.50/27.95  Index Insertion      : 0.00
% 37.50/27.95  Index Deletion       : 0.00
% 37.50/27.95  Index Matching       : 0.00
% 37.50/27.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------
