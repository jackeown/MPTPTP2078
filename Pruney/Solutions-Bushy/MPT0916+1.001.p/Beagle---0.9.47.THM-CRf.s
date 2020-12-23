%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0916+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n032.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:37:04 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :  273 (1798 expanded)
%              Number of leaves         :   35 ( 534 expanded)
%              Depth                    :   14
%              Number of atoms          :  506 (7525 expanded)
%              Number of equality atoms :  276 (3871 expanded)
%              Maximal formula depth    :   22 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > #nlpp > k1_zfmisc_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_mcart_1,type,(
    k6_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_41,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_133,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(A))
       => ! [E] :
            ( m1_subset_1(E,k1_zfmisc_1(B))
           => ! [F] :
                ( m1_subset_1(F,k1_zfmisc_1(C))
               => ! [G] :
                    ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
                   => ( r2_hidden(G,k3_zfmisc_1(D,E,F))
                     => ( r2_hidden(k5_mcart_1(A,B,C,G),D)
                        & r2_hidden(k6_mcart_1(A,B,C,G),E)
                        & r2_hidden(k7_mcart_1(A,B,C,G),F) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_mcart_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_subset)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,B)
        & m1_subset_1(B,k1_zfmisc_1(C))
        & v1_xboole_0(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

tff(f_108,axiom,(
    ! [A,B,C,D,E,F] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & D != k1_xboole_0
        & E != k1_xboole_0
        & F != k1_xboole_0
        & ? [G] :
            ( m1_subset_1(G,k3_zfmisc_1(A,B,C))
            & ? [H] :
                ( m1_subset_1(H,k3_zfmisc_1(D,E,F))
                & G = H
                & ~ ( k5_mcart_1(A,B,C,G) = k5_mcart_1(D,E,F,H)
                    & k6_mcart_1(A,B,C,G) = k6_mcart_1(D,E,F,H)
                    & k7_mcart_1(A,B,C,G) = k7_mcart_1(D,E,F,H) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_mcart_1)).

tff(f_25,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_38,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_113,axiom,(
    ! [A,B] :
      ~ ( r2_hidden(A,B)
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_boole)).

tff(f_29,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_74,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_33,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(c_16,plain,(
    ! [A_17,B_18] :
      ( r2_hidden(A_17,B_18)
      | v1_xboole_0(B_18)
      | ~ m1_subset_1(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_12,plain,(
    ! [A_13] : m1_subset_1('#skF_1'(A_13),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_38,plain,
    ( ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_140,plain,(
    ~ r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_146,plain,
    ( v1_xboole_0('#skF_5')
    | ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(resolution,[status(thm)],[c_16,c_140])).

tff(c_153,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_40,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_14,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(A_15,B_16)
      | ~ r2_hidden(A_15,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_114,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_14])).

tff(c_46,plain,(
    m1_subset_1('#skF_6',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_125,plain,(
    ! [C_65,B_66,A_67] :
      ( ~ v1_xboole_0(C_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(C_65))
      | ~ r2_hidden(A_67,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_137,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0('#skF_3')
      | ~ r2_hidden(A_67,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_46,c_125])).

tff(c_141,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_44,plain,(
    m1_subset_1('#skF_7',k1_zfmisc_1('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_136,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0('#skF_4')
      | ~ r2_hidden(A_67,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_44,c_125])).

tff(c_139,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_136])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_138,plain,(
    ! [A_67] :
      ( ~ v1_xboole_0('#skF_2')
      | ~ r2_hidden(A_67,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_48,c_125])).

tff(c_142,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_42,plain,(
    m1_subset_1('#skF_8',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_133])).

tff(c_254,plain,(
    ! [B_111,C_115,A_113,E_116,D_110,F_114,H_112] :
      ( k6_mcart_1(D_110,E_116,F_114,H_112) = k6_mcart_1(A_113,B_111,C_115,H_112)
      | ~ m1_subset_1(H_112,k3_zfmisc_1(D_110,E_116,F_114))
      | ~ m1_subset_1(H_112,k3_zfmisc_1(A_113,B_111,C_115))
      | k1_xboole_0 = F_114
      | k1_xboole_0 = E_116
      | k1_xboole_0 = D_110
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_113 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_283,plain,(
    ! [A_113,B_111,C_115] :
      ( k6_mcart_1(A_113,B_111,C_115,'#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_113,B_111,C_115))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_113 ) ),
    inference(resolution,[status(thm)],[c_42,c_254])).

tff(c_334,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_283])).

tff(c_2,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_25])).

tff(c_10,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_49,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_345,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_334,c_49])).

tff(c_348,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_345])).

tff(c_349,plain,(
    ! [A_113,B_111,C_115] :
      ( k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_4'
      | k6_mcart_1(A_113,B_111,C_115,'#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_113,B_111,C_115))
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_113 ) ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_476,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_349])).

tff(c_492,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_476,c_49])).

tff(c_495,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_492])).

tff(c_496,plain,(
    ! [A_113,B_111,C_115] :
      ( k1_xboole_0 = '#skF_3'
      | k6_mcart_1(A_113,B_111,C_115,'#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_113,B_111,C_115))
      | k1_xboole_0 = C_115
      | k1_xboole_0 = B_111
      | k1_xboole_0 = A_113 ) ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_532,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_496])).

tff(c_550,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_532,c_49])).

tff(c_553,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_141,c_550])).

tff(c_560,plain,(
    ! [A_156,B_157,C_158] :
      ( k6_mcart_1(A_156,B_157,C_158,'#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_156,B_157,C_158))
      | k1_xboole_0 = C_158
      | k1_xboole_0 = B_157
      | k1_xboole_0 = A_156 ) ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_576,plain,
    ( k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_114,c_560])).

tff(c_608,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_576])).

tff(c_629,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_49])).

tff(c_24,plain,(
    ! [B_20,C_21] : k3_zfmisc_1(k1_xboole_0,B_20,C_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_626,plain,(
    ! [B_20,C_21] : k3_zfmisc_1('#skF_5',B_20,C_21) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_608,c_24])).

tff(c_36,plain,(
    ! [B_39,A_38] :
      ( ~ v1_xboole_0(B_39)
      | ~ r2_hidden(A_38,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_113])).

tff(c_115,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_36])).

tff(c_707,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_115])).

tff(c_711,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_629,c_707])).

tff(c_713,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_576])).

tff(c_555,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_496])).

tff(c_497,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_349])).

tff(c_350,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_283])).

tff(c_406,plain,(
    ! [B_140,C_144,E_145,A_142,F_143,H_141,D_139] :
      ( k5_mcart_1(D_139,E_145,F_143,H_141) = k5_mcart_1(A_142,B_140,C_144,H_141)
      | ~ m1_subset_1(H_141,k3_zfmisc_1(D_139,E_145,F_143))
      | ~ m1_subset_1(H_141,k3_zfmisc_1(A_142,B_140,C_144))
      | k1_xboole_0 = F_143
      | k1_xboole_0 = E_145
      | k1_xboole_0 = D_139
      | k1_xboole_0 = C_144
      | k1_xboole_0 = B_140
      | k1_xboole_0 = A_142 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_423,plain,(
    ! [A_142,B_140,C_144] :
      ( k5_mcart_1(A_142,B_140,C_144,'#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_142,B_140,C_144))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = C_144
      | k1_xboole_0 = B_140
      | k1_xboole_0 = A_142 ) ),
    inference(resolution,[status(thm)],[c_42,c_406])).

tff(c_437,plain,(
    ! [A_142,B_140,C_144] :
      ( k5_mcart_1(A_142,B_140,C_144,'#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_142,B_140,C_144))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = C_144
      | k1_xboole_0 = B_140
      | k1_xboole_0 = A_142 ) ),
    inference(negUnitSimplification,[status(thm)],[c_350,c_423])).

tff(c_725,plain,(
    ! [A_171,B_172,C_173] :
      ( k5_mcart_1(A_171,B_172,C_173,'#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_171,B_172,C_173))
      | k1_xboole_0 = C_173
      | k1_xboole_0 = B_172
      | k1_xboole_0 = A_171 ) ),
    inference(negUnitSimplification,[status(thm)],[c_555,c_497,c_437])).

tff(c_728,plain,
    ( k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_114,c_725])).

tff(c_743,plain,
    ( k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_713,c_728])).

tff(c_751,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_774,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_49])).

tff(c_22,plain,(
    ! [A_19,C_21] : k3_zfmisc_1(A_19,k1_xboole_0,C_21) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_770,plain,(
    ! [A_19,C_21] : k3_zfmisc_1(A_19,'#skF_6',C_21) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_751,c_751,c_22])).

tff(c_852,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_770,c_115])).

tff(c_856,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_774,c_852])).

tff(c_857,plain,
    ( k1_xboole_0 = '#skF_7'
    | k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_859,plain,(
    k5_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_857])).

tff(c_4,plain,(
    ! [A_1,B_2,C_3,D_4] :
      ( m1_subset_1(k5_mcart_1(A_1,B_2,C_3,D_4),A_1)
      | ~ m1_subset_1(D_4,k3_zfmisc_1(A_1,B_2,C_3)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_863,plain,
    ( m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5')
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_859,c_4])).

tff(c_867,plain,(
    m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_863])).

tff(c_869,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_867])).

tff(c_870,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_857])).

tff(c_923,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_49])).

tff(c_20,plain,(
    ! [A_19,B_20] : k3_zfmisc_1(A_19,B_20,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_921,plain,(
    ! [A_19,B_20] : k3_zfmisc_1(A_19,B_20,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_870,c_870,c_20])).

tff(c_1004,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_115])).

tff(c_1008,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_1004])).

tff(c_1009,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_28,plain,(
    ! [A_25] :
      ( k1_xboole_0 = A_25
      | ~ v1_xboole_0(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_1014,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1009,c_28])).

tff(c_1016,plain,(
    ! [B_20,C_21] : k3_zfmisc_1('#skF_5',B_20,C_21) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1014,c_1014,c_24])).

tff(c_1071,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1016,c_115])).

tff(c_1075,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_1071])).

tff(c_1077,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1081,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1077,c_28])).

tff(c_1083,plain,(
    ! [B_20,C_21] : k3_zfmisc_1('#skF_2',B_20,C_21) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_1081,c_24])).

tff(c_1097,plain,(
    ! [A_212] : ~ r2_hidden(A_212,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_1102,plain,(
    ! [A_17] :
      ( v1_xboole_0('#skF_5')
      | ~ m1_subset_1(A_17,'#skF_5') ) ),
    inference(resolution,[status(thm)],[c_16,c_1097])).

tff(c_1118,plain,(
    ! [A_216] : ~ m1_subset_1(A_216,'#skF_5') ),
    inference(splitLeft,[status(thm)],[c_1102])).

tff(c_1123,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_1118])).

tff(c_1124,plain,(
    v1_xboole_0('#skF_5') ),
    inference(splitRight,[status(thm)],[c_1102])).

tff(c_1085,plain,(
    ! [A_25] :
      ( A_25 = '#skF_2'
      | ~ v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1081,c_28])).

tff(c_1128,plain,(
    '#skF_5' = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1124,c_1085])).

tff(c_1132,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_6','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1128,c_115])).

tff(c_1139,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1083,c_1132])).

tff(c_1165,plain,(
    ! [A_217] : ~ r2_hidden(A_217,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_1170,plain,(
    ! [A_17] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_17,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_16,c_1165])).

tff(c_1186,plain,(
    ! [A_221] : ~ m1_subset_1(A_221,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_1170])).

tff(c_1191,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_1186])).

tff(c_1192,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_1170])).

tff(c_1141,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_1145,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1141,c_28])).

tff(c_1149,plain,(
    ! [A_25] :
      ( A_25 = '#skF_3'
      | ~ v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_28])).

tff(c_1196,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1192,c_1149])).

tff(c_1140,plain,(
    ! [A_67] : ~ r2_hidden(A_67,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_1205,plain,(
    ! [A_67] : ~ r2_hidden(A_67,'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_1140])).

tff(c_1146,plain,(
    ! [A_19,C_21] : k3_zfmisc_1(A_19,'#skF_3',C_21) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1145,c_1145,c_22])).

tff(c_1208,plain,(
    r2_hidden('#skF_8',k3_zfmisc_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1196,c_40])).

tff(c_1235,plain,(
    r2_hidden('#skF_8','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1146,c_1208])).

tff(c_1238,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1205,c_1235])).

tff(c_1239,plain,
    ( ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1257,plain,(
    ~ r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1239])).

tff(c_1261,plain,
    ( v1_xboole_0('#skF_7')
    | ~ m1_subset_1(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_16,c_1257])).

tff(c_1262,plain,(
    ~ m1_subset_1(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_1261])).

tff(c_1240,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_5') ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_1250,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(resolution,[status(thm)],[c_1240,c_36])).

tff(c_1241,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_137])).

tff(c_1242,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_138])).

tff(c_1357,plain,(
    ! [C_264,H_261,D_259,A_262,B_260,E_265,F_263] :
      ( k5_mcart_1(D_259,E_265,F_263,H_261) = k5_mcart_1(A_262,B_260,C_264,H_261)
      | ~ m1_subset_1(H_261,k3_zfmisc_1(D_259,E_265,F_263))
      | ~ m1_subset_1(H_261,k3_zfmisc_1(A_262,B_260,C_264))
      | k1_xboole_0 = F_263
      | k1_xboole_0 = E_265
      | k1_xboole_0 = D_259
      | k1_xboole_0 = C_264
      | k1_xboole_0 = B_260
      | k1_xboole_0 = A_262 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1386,plain,(
    ! [A_262,B_260,C_264] :
      ( k5_mcart_1(A_262,B_260,C_264,'#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_262,B_260,C_264))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = C_264
      | k1_xboole_0 = B_260
      | k1_xboole_0 = A_262 ) ),
    inference(resolution,[status(thm)],[c_42,c_1357])).

tff(c_1566,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_1386])).

tff(c_1581,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1566,c_49])).

tff(c_1584,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1242,c_1581])).

tff(c_1586,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_1386])).

tff(c_1464,plain,(
    ! [F_290,A_289,E_292,H_288,B_287,C_291,D_286] :
      ( k7_mcart_1(D_286,E_292,F_290,H_288) = k7_mcart_1(A_289,B_287,C_291,H_288)
      | ~ m1_subset_1(H_288,k3_zfmisc_1(D_286,E_292,F_290))
      | ~ m1_subset_1(H_288,k3_zfmisc_1(A_289,B_287,C_291))
      | k1_xboole_0 = F_290
      | k1_xboole_0 = E_292
      | k1_xboole_0 = D_286
      | k1_xboole_0 = C_291
      | k1_xboole_0 = B_287
      | k1_xboole_0 = A_289 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_1493,plain,(
    ! [A_289,B_287,C_291] :
      ( k7_mcart_1(A_289,B_287,C_291,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_289,B_287,C_291))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = C_291
      | k1_xboole_0 = B_287
      | k1_xboole_0 = A_289 ) ),
    inference(resolution,[status(thm)],[c_42,c_1464])).

tff(c_1621,plain,(
    ! [A_289,B_287,C_291] :
      ( k7_mcart_1(A_289,B_287,C_291,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_289,B_287,C_291))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = C_291
      | k1_xboole_0 = B_287
      | k1_xboole_0 = A_289 ) ),
    inference(negUnitSimplification,[status(thm)],[c_1586,c_1493])).

tff(c_1622,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1621])).

tff(c_1639,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1622,c_49])).

tff(c_1642,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1241,c_1639])).

tff(c_1643,plain,(
    ! [A_289,B_287,C_291] :
      ( k1_xboole_0 = '#skF_4'
      | k7_mcart_1(A_289,B_287,C_291,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_289,B_287,C_291))
      | k1_xboole_0 = C_291
      | k1_xboole_0 = B_287
      | k1_xboole_0 = A_289 ) ),
    inference(splitRight,[status(thm)],[c_1621])).

tff(c_1645,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_1643])).

tff(c_1663,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1645,c_49])).

tff(c_1666,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_1663])).

tff(c_1669,plain,(
    ! [A_310,B_311,C_312] :
      ( k7_mcart_1(A_310,B_311,C_312,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_310,B_311,C_312))
      | k1_xboole_0 = C_312
      | k1_xboole_0 = B_311
      | k1_xboole_0 = A_310 ) ),
    inference(splitRight,[status(thm)],[c_1643])).

tff(c_1685,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_114,c_1669])).

tff(c_1693,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1685])).

tff(c_1713,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1693,c_49])).

tff(c_1716,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1250,c_1713])).

tff(c_1717,plain,
    ( k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_7'
    | k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_1685])).

tff(c_1746,plain,(
    k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_1717])).

tff(c_8,plain,(
    ! [A_9,B_10,C_11,D_12] :
      ( m1_subset_1(k7_mcart_1(A_9,B_10,C_11,D_12),C_11)
      | ~ m1_subset_1(D_12,k3_zfmisc_1(A_9,B_10,C_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1750,plain,
    ( m1_subset_1(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7')
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1746,c_8])).

tff(c_1754,plain,(
    m1_subset_1(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_1750])).

tff(c_1756,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1262,c_1754])).

tff(c_1757,plain,
    ( k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_1717])).

tff(c_1759,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_1757])).

tff(c_1781,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_49])).

tff(c_1777,plain,(
    ! [A_19,C_21] : k3_zfmisc_1(A_19,'#skF_6',C_21) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1759,c_1759,c_22])).

tff(c_1834,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1777,c_115])).

tff(c_1838,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1834])).

tff(c_1839,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_1757])).

tff(c_1891,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_49])).

tff(c_1889,plain,(
    ! [A_19,B_20] : k3_zfmisc_1(A_19,B_20,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1839,c_1839,c_20])).

tff(c_1991,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1889,c_115])).

tff(c_1995,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1891,c_1991])).

tff(c_1996,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_1261])).

tff(c_2001,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1996,c_28])).

tff(c_2004,plain,(
    ! [A_19,B_20] : k3_zfmisc_1(A_19,B_20,'#skF_7') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2001,c_2001,c_20])).

tff(c_2031,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2004,c_115])).

tff(c_2035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1996,c_2031])).

tff(c_2037,plain,(
    r2_hidden(k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_7') ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_2049,plain,(
    ~ v1_xboole_0('#skF_7') ),
    inference(resolution,[status(thm)],[c_2037,c_36])).

tff(c_2036,plain,(
    ~ r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_1239])).

tff(c_2041,plain,
    ( v1_xboole_0('#skF_6')
    | ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_16,c_2036])).

tff(c_2050,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2041])).

tff(c_2140,plain,(
    ! [E_385,B_380,F_383,D_379,H_381,C_384,A_382] :
      ( k5_mcart_1(D_379,E_385,F_383,H_381) = k5_mcart_1(A_382,B_380,C_384,H_381)
      | ~ m1_subset_1(H_381,k3_zfmisc_1(D_379,E_385,F_383))
      | ~ m1_subset_1(H_381,k3_zfmisc_1(A_382,B_380,C_384))
      | k1_xboole_0 = F_383
      | k1_xboole_0 = E_385
      | k1_xboole_0 = D_379
      | k1_xboole_0 = C_384
      | k1_xboole_0 = B_380
      | k1_xboole_0 = A_382 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2169,plain,(
    ! [A_382,B_380,C_384] :
      ( k5_mcart_1(A_382,B_380,C_384,'#skF_8') = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_382,B_380,C_384))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = C_384
      | k1_xboole_0 = B_380
      | k1_xboole_0 = A_382 ) ),
    inference(resolution,[status(thm)],[c_42,c_2140])).

tff(c_2221,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_2169])).

tff(c_2232,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2221,c_49])).

tff(c_2235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1242,c_2232])).

tff(c_2237,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_2169])).

tff(c_2288,plain,(
    ! [H_412,D_410,B_411,F_414,C_415,A_413,E_416] :
      ( k7_mcart_1(D_410,E_416,F_414,H_412) = k7_mcart_1(A_413,B_411,C_415,H_412)
      | ~ m1_subset_1(H_412,k3_zfmisc_1(D_410,E_416,F_414))
      | ~ m1_subset_1(H_412,k3_zfmisc_1(A_413,B_411,C_415))
      | k1_xboole_0 = F_414
      | k1_xboole_0 = E_416
      | k1_xboole_0 = D_410
      | k1_xboole_0 = C_415
      | k1_xboole_0 = B_411
      | k1_xboole_0 = A_413 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2305,plain,(
    ! [A_413,B_411,C_415] :
      ( k7_mcart_1(A_413,B_411,C_415,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_413,B_411,C_415))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = C_415
      | k1_xboole_0 = B_411
      | k1_xboole_0 = A_413 ) ),
    inference(resolution,[status(thm)],[c_42,c_2288])).

tff(c_2319,plain,(
    ! [A_413,B_411,C_415] :
      ( k7_mcart_1(A_413,B_411,C_415,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_413,B_411,C_415))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = C_415
      | k1_xboole_0 = B_411
      | k1_xboole_0 = A_413 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2237,c_2305])).

tff(c_2368,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_2319])).

tff(c_2384,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2368,c_49])).

tff(c_2387,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1241,c_2384])).

tff(c_2388,plain,(
    ! [A_413,B_411,C_415] :
      ( k1_xboole_0 = '#skF_4'
      | k7_mcart_1(A_413,B_411,C_415,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_413,B_411,C_415))
      | k1_xboole_0 = C_415
      | k1_xboole_0 = B_411
      | k1_xboole_0 = A_413 ) ),
    inference(splitRight,[status(thm)],[c_2319])).

tff(c_2424,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2388])).

tff(c_2443,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2424,c_49])).

tff(c_2446,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_139,c_2443])).

tff(c_2449,plain,(
    ! [A_430,B_431,C_432] :
      ( k7_mcart_1(A_430,B_431,C_432,'#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_430,B_431,C_432))
      | k1_xboole_0 = C_432
      | k1_xboole_0 = B_431
      | k1_xboole_0 = A_430 ) ),
    inference(splitRight,[status(thm)],[c_2388])).

tff(c_2465,plain,
    ( k7_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_114,c_2449])).

tff(c_2473,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_2465])).

tff(c_2493,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_49])).

tff(c_2496,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1250,c_2493])).

tff(c_2498,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2465])).

tff(c_2448,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2388])).

tff(c_2389,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_2319])).

tff(c_2390,plain,(
    ! [F_427,A_426,B_424,C_428,D_423,H_425,E_429] :
      ( k6_mcart_1(D_423,E_429,F_427,H_425) = k6_mcart_1(A_426,B_424,C_428,H_425)
      | ~ m1_subset_1(H_425,k3_zfmisc_1(D_423,E_429,F_427))
      | ~ m1_subset_1(H_425,k3_zfmisc_1(A_426,B_424,C_428))
      | k1_xboole_0 = F_427
      | k1_xboole_0 = E_429
      | k1_xboole_0 = D_423
      | k1_xboole_0 = C_428
      | k1_xboole_0 = B_424
      | k1_xboole_0 = A_426 ) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_2407,plain,(
    ! [A_426,B_424,C_428] :
      ( k6_mcart_1(A_426,B_424,C_428,'#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_426,B_424,C_428))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = '#skF_3'
      | k1_xboole_0 = '#skF_2'
      | k1_xboole_0 = C_428
      | k1_xboole_0 = B_424
      | k1_xboole_0 = A_426 ) ),
    inference(resolution,[status(thm)],[c_42,c_2390])).

tff(c_2421,plain,(
    ! [A_426,B_424,C_428] :
      ( k6_mcart_1(A_426,B_424,C_428,'#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_426,B_424,C_428))
      | k1_xboole_0 = '#skF_4'
      | k1_xboole_0 = C_428
      | k1_xboole_0 = B_424
      | k1_xboole_0 = A_426 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2237,c_2389,c_2407])).

tff(c_2500,plain,(
    ! [A_433,B_434,C_435] :
      ( k6_mcart_1(A_433,B_434,C_435,'#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
      | ~ m1_subset_1('#skF_8',k3_zfmisc_1(A_433,B_434,C_435))
      | k1_xboole_0 = C_435
      | k1_xboole_0 = B_434
      | k1_xboole_0 = A_433 ) ),
    inference(negUnitSimplification,[status(thm)],[c_2448,c_2421])).

tff(c_2516,plain,
    ( k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6'
    | k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_114,c_2500])).

tff(c_2534,plain,
    ( k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8')
    | k1_xboole_0 = '#skF_7'
    | k1_xboole_0 = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_2498,c_2516])).

tff(c_2535,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_2534])).

tff(c_2557,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2535,c_49])).

tff(c_2553,plain,(
    ! [A_19,C_21] : k3_zfmisc_1(A_19,'#skF_6',C_21) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2535,c_2535,c_22])).

tff(c_2651,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2553,c_115])).

tff(c_2655,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2557,c_2651])).

tff(c_2656,plain,
    ( k1_xboole_0 = '#skF_7'
    | k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitRight,[status(thm)],[c_2534])).

tff(c_2658,plain,(
    k6_mcart_1('#skF_5','#skF_6','#skF_7','#skF_8') = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8') ),
    inference(splitLeft,[status(thm)],[c_2656])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7,D_8] :
      ( m1_subset_1(k6_mcart_1(A_5,B_6,C_7,D_8),B_6)
      | ~ m1_subset_1(D_8,k3_zfmisc_1(A_5,B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2689,plain,
    ( m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6')
    | ~ m1_subset_1('#skF_8',k3_zfmisc_1('#skF_5','#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2658,c_6])).

tff(c_2693,plain,(
    m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_8'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_2689])).

tff(c_2695,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2050,c_2693])).

tff(c_2696,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_2656])).

tff(c_2720,plain,(
    v1_xboole_0('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2696,c_49])).

tff(c_2723,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2049,c_2720])).

tff(c_2724,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2041])).

tff(c_2729,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_2724,c_28])).

tff(c_2730,plain,(
    ! [A_19,C_21] : k3_zfmisc_1(A_19,'#skF_6',C_21) = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2729,c_2729,c_22])).

tff(c_2754,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2730,c_115])).

tff(c_2758,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2724,c_2754])).

tff(c_2759,plain,(
    ! [A_67] : ~ r2_hidden(A_67,'#skF_5') ),
    inference(splitRight,[status(thm)],[c_138])).

tff(c_2789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2759,c_1240])).

tff(c_2791,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2795,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2791,c_28])).

tff(c_2804,plain,(
    ! [A_19,C_21] : k3_zfmisc_1(A_19,'#skF_3',C_21) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_2795,c_22])).

tff(c_2820,plain,(
    ! [A_455] : ~ r2_hidden(A_455,'#skF_6') ),
    inference(splitRight,[status(thm)],[c_137])).

tff(c_2825,plain,(
    ! [A_17] :
      ( v1_xboole_0('#skF_6')
      | ~ m1_subset_1(A_17,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_16,c_2820])).

tff(c_2833,plain,(
    ! [A_457] : ~ m1_subset_1(A_457,'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_2825])).

tff(c_2838,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_2833])).

tff(c_2839,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_2825])).

tff(c_2807,plain,(
    ! [A_25] :
      ( A_25 = '#skF_3'
      | ~ v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2795,c_28])).

tff(c_2845,plain,(
    '#skF_6' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_2839,c_2807])).

tff(c_2849,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_3','#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2845,c_115])).

tff(c_2931,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2791,c_2804,c_2849])).

tff(c_2933,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2953,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2933,c_28])).

tff(c_2957,plain,(
    ! [A_19,B_20] : k3_zfmisc_1(A_19,B_20,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2953,c_2953,c_20])).

tff(c_2971,plain,(
    ! [A_471] : ~ r2_hidden(A_471,'#skF_7') ),
    inference(splitRight,[status(thm)],[c_136])).

tff(c_2976,plain,(
    ! [A_17] :
      ( v1_xboole_0('#skF_7')
      | ~ m1_subset_1(A_17,'#skF_7') ) ),
    inference(resolution,[status(thm)],[c_16,c_2971])).

tff(c_2999,plain,(
    ! [A_475] : ~ m1_subset_1(A_475,'#skF_7') ),
    inference(splitLeft,[status(thm)],[c_2976])).

tff(c_3004,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_12,c_2999])).

tff(c_3005,plain,(
    v1_xboole_0('#skF_7') ),
    inference(splitRight,[status(thm)],[c_2976])).

tff(c_2958,plain,(
    ! [A_25] :
      ( A_25 = '#skF_4'
      | ~ v1_xboole_0(A_25) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2953,c_28])).

tff(c_3009,plain,(
    '#skF_7' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_3005,c_2958])).

tff(c_3013,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_5','#skF_6','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3009,c_115])).

tff(c_3020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2933,c_2957,c_3013])).

%------------------------------------------------------------------------------
