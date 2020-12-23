%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:00 EST 2020

% Result     : Theorem 6.59s
% Output     : CNFRefutation 6.96s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 247 expanded)
%              Number of leaves         :   35 ( 101 expanded)
%              Depth                    :   14
%              Number of atoms          :  165 ( 741 expanded)
%              Number of equality atoms :   80 ( 369 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_mcart_1,type,(
    k3_mcart_1: ( $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k7_mcart_1,type,(
    k7_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff(k3_zfmisc_1,type,(
    k3_zfmisc_1: ( $i * $i * $i ) > $i )).

tff(k5_mcart_1,type,(
    k5_mcart_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_122,negated_conjecture,(
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

tff(f_98,axiom,(
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

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_66,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_60,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_302,plain,(
    ! [A_108,B_109,C_110,D_111] :
      ( k7_mcart_1(A_108,B_109,C_110,D_111) = k2_mcart_1(D_111)
      | ~ m1_subset_1(D_111,k3_zfmisc_1(A_108,B_109,C_110))
      | k1_xboole_0 = C_110
      | k1_xboole_0 = B_109
      | k1_xboole_0 = A_108 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_321,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_302])).

tff(c_337,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_321])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( m1_subset_1(k7_mcart_1(A_15,B_16,C_17,D_18),C_17)
      | ~ m1_subset_1(D_18,k3_zfmisc_1(A_15,B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_344,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_337,c_16])).

tff(c_348,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_344])).

tff(c_116,plain,(
    ! [A_64,B_65,C_66] : k2_zfmisc_1(k2_zfmisc_1(A_64,B_65),C_66) = k3_zfmisc_1(A_64,B_65,C_66) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_126,plain,(
    ! [A_64,B_65,C_66] : v1_relat_1(k3_zfmisc_1(A_64,B_65,C_66)) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_10])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_212,plain,(
    ! [A_90,B_91] :
      ( k4_tarski(k1_mcart_1(A_90),k2_mcart_1(A_90)) = A_90
      | ~ r2_hidden(A_90,B_91)
      | ~ v1_relat_1(B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1643,plain,(
    ! [A_226,B_227] :
      ( k4_tarski(k1_mcart_1(A_226),k2_mcart_1(A_226)) = A_226
      | ~ v1_relat_1(B_227)
      | v1_xboole_0(B_227)
      | ~ m1_subset_1(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_8,c_212])).

tff(c_1681,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_1643])).

tff(c_1708,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_1681])).

tff(c_1739,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_1708])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_95,plain,(
    ! [B_54,A_55] :
      ( ~ v1_xboole_0(B_54)
      | B_54 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_98,plain,(
    ! [A_55] :
      ( k1_xboole_0 = A_55
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_2,c_95])).

tff(c_1745,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1739,c_98])).

tff(c_24,plain,(
    ! [A_24,B_25,C_26] :
      ( k3_zfmisc_1(A_24,B_25,C_26) != k1_xboole_0
      | k1_xboole_0 = C_26
      | k1_xboole_0 = B_25
      | k1_xboole_0 = A_24 ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_1772,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_1745,c_24])).

tff(c_1787,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_1772])).

tff(c_1788,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1708])).

tff(c_38,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_571,plain,(
    ! [A_132,B_133,C_134,D_135] :
      ( k5_mcart_1(A_132,B_133,C_134,D_135) = k1_mcart_1(k1_mcart_1(D_135))
      | ~ m1_subset_1(D_135,k3_zfmisc_1(A_132,B_133,C_134))
      | k1_xboole_0 = C_134
      | k1_xboole_0 = B_133
      | k1_xboole_0 = A_132 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_606,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_571])).

tff(c_626,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_606])).

tff(c_1789,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_1708])).

tff(c_14,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    ! [A_73,B_74,C_75] :
      ( r2_hidden(k1_mcart_1(A_73),B_74)
      | ~ r2_hidden(A_73,k2_zfmisc_1(B_74,C_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_772,plain,(
    ! [A_148,A_149,B_150,C_151] :
      ( r2_hidden(k1_mcart_1(A_148),k2_zfmisc_1(A_149,B_150))
      | ~ r2_hidden(A_148,k3_zfmisc_1(A_149,B_150,C_151)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_145])).

tff(c_4190,plain,(
    ! [A_354,A_355,B_356,C_357] :
      ( r2_hidden(k1_mcart_1(A_354),k2_zfmisc_1(A_355,B_356))
      | v1_xboole_0(k3_zfmisc_1(A_355,B_356,C_357))
      | ~ m1_subset_1(A_354,k3_zfmisc_1(A_355,B_356,C_357)) ) ),
    inference(resolution,[status(thm)],[c_8,c_772])).

tff(c_4287,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_4190])).

tff(c_4328,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1789,c_4287])).

tff(c_20,plain,(
    ! [A_19,B_20,C_21] :
      ( r2_hidden(k1_mcart_1(A_19),B_20)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4335,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4328,c_20])).

tff(c_4345,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_626,c_4335])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4368,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4345,c_6])).

tff(c_390,plain,(
    ! [A_116,B_117,C_118,D_119] :
      ( k6_mcart_1(A_116,B_117,C_118,D_119) = k2_mcart_1(k1_mcart_1(D_119))
      | ~ m1_subset_1(D_119,k3_zfmisc_1(A_116,B_117,C_118))
      | k1_xboole_0 = C_118
      | k1_xboole_0 = B_117
      | k1_xboole_0 = A_116 ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_409,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_390])).

tff(c_425,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_409])).

tff(c_18,plain,(
    ! [A_19,C_21,B_20] :
      ( r2_hidden(k2_mcart_1(A_19),C_21)
      | ~ r2_hidden(A_19,k2_zfmisc_1(B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_4337,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4328,c_18])).

tff(c_4347,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_4337])).

tff(c_4375,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_4347,c_6])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k4_tarski(k1_mcart_1(A_22),k2_mcart_1(A_22)) = A_22
      | ~ r2_hidden(A_22,B_23)
      | ~ v1_relat_1(B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4333,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_4328,c_22])).

tff(c_4343,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_425,c_626,c_4333])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k4_tarski(k4_tarski(A_9,B_10),C_11) = k3_mcart_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_4939,plain,(
    ! [C_392] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_392) = k4_tarski(k1_mcart_1('#skF_5'),C_392) ),
    inference(superposition,[status(thm),theory(equality)],[c_4343,c_12])).

tff(c_46,plain,(
    ! [G_43,F_39,H_45] :
      ( G_43 = '#skF_4'
      | k3_mcart_1(F_39,G_43,H_45) != '#skF_5'
      | ~ m1_subset_1(H_45,'#skF_3')
      | ~ m1_subset_1(G_43,'#skF_2')
      | ~ m1_subset_1(F_39,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_4946,plain,(
    ! [C_392] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_392) != '#skF_5'
      | ~ m1_subset_1(C_392,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4939,c_46])).

tff(c_4953,plain,(
    ! [C_392] :
      ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_392) != '#skF_5'
      | ~ m1_subset_1(C_392,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4368,c_4375,c_4946])).

tff(c_4956,plain,(
    ! [C_393] :
      ( k4_tarski(k1_mcart_1('#skF_5'),C_393) != '#skF_5'
      | ~ m1_subset_1(C_393,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_4953])).

tff(c_4959,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1788,c_4956])).

tff(c_4963,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_4959])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:41:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.59/2.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.96/2.56  
% 6.96/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.96/2.56  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.96/2.56  
% 6.96/2.56  %Foreground sorts:
% 6.96/2.56  
% 6.96/2.56  
% 6.96/2.56  %Background operators:
% 6.96/2.56  
% 6.96/2.56  
% 6.96/2.56  %Foreground operators:
% 6.96/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.96/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.96/2.56  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 6.96/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.96/2.56  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 6.96/2.56  tff('#skF_5', type, '#skF_5': $i).
% 6.96/2.56  tff('#skF_2', type, '#skF_2': $i).
% 6.96/2.56  tff('#skF_3', type, '#skF_3': $i).
% 6.96/2.56  tff('#skF_1', type, '#skF_1': $i).
% 6.96/2.56  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 6.96/2.56  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 6.96/2.56  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 6.96/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.96/2.56  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 6.96/2.56  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.96/2.56  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.96/2.56  tff('#skF_4', type, '#skF_4': $i).
% 6.96/2.56  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 6.96/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.96/2.56  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 6.96/2.56  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.96/2.56  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.96/2.56  
% 6.96/2.58  tff(f_122, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 6.96/2.58  tff(f_98, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 6.96/2.58  tff(f_54, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 6.96/2.58  tff(f_50, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 6.96/2.58  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.96/2.58  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 6.96/2.58  tff(f_66, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 6.96/2.58  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.96/2.58  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 6.96/2.58  tff(f_78, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 6.96/2.58  tff(f_60, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 6.96/2.58  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 6.96/2.58  tff(f_48, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 6.96/2.58  tff(c_48, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.96/2.58  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.96/2.58  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.96/2.58  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.96/2.58  tff(c_302, plain, (![A_108, B_109, C_110, D_111]: (k7_mcart_1(A_108, B_109, C_110, D_111)=k2_mcart_1(D_111) | ~m1_subset_1(D_111, k3_zfmisc_1(A_108, B_109, C_110)) | k1_xboole_0=C_110 | k1_xboole_0=B_109 | k1_xboole_0=A_108)), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.96/2.58  tff(c_321, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_302])).
% 6.96/2.58  tff(c_337, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_321])).
% 6.96/2.58  tff(c_16, plain, (![A_15, B_16, C_17, D_18]: (m1_subset_1(k7_mcart_1(A_15, B_16, C_17, D_18), C_17) | ~m1_subset_1(D_18, k3_zfmisc_1(A_15, B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.96/2.58  tff(c_344, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_337, c_16])).
% 6.96/2.58  tff(c_348, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_344])).
% 6.96/2.58  tff(c_116, plain, (![A_64, B_65, C_66]: (k2_zfmisc_1(k2_zfmisc_1(A_64, B_65), C_66)=k3_zfmisc_1(A_64, B_65, C_66))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.96/2.58  tff(c_10, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 6.96/2.58  tff(c_126, plain, (![A_64, B_65, C_66]: (v1_relat_1(k3_zfmisc_1(A_64, B_65, C_66)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_10])).
% 6.96/2.58  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.96/2.58  tff(c_212, plain, (![A_90, B_91]: (k4_tarski(k1_mcart_1(A_90), k2_mcart_1(A_90))=A_90 | ~r2_hidden(A_90, B_91) | ~v1_relat_1(B_91))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.96/2.58  tff(c_1643, plain, (![A_226, B_227]: (k4_tarski(k1_mcart_1(A_226), k2_mcart_1(A_226))=A_226 | ~v1_relat_1(B_227) | v1_xboole_0(B_227) | ~m1_subset_1(A_226, B_227))), inference(resolution, [status(thm)], [c_8, c_212])).
% 6.96/2.58  tff(c_1681, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_1643])).
% 6.96/2.58  tff(c_1708, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_1681])).
% 6.96/2.58  tff(c_1739, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_1708])).
% 6.96/2.58  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.96/2.58  tff(c_95, plain, (![B_54, A_55]: (~v1_xboole_0(B_54) | B_54=A_55 | ~v1_xboole_0(A_55))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.96/2.58  tff(c_98, plain, (![A_55]: (k1_xboole_0=A_55 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_2, c_95])).
% 6.96/2.58  tff(c_1745, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1739, c_98])).
% 6.96/2.58  tff(c_24, plain, (![A_24, B_25, C_26]: (k3_zfmisc_1(A_24, B_25, C_26)!=k1_xboole_0 | k1_xboole_0=C_26 | k1_xboole_0=B_25 | k1_xboole_0=A_24)), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.96/2.58  tff(c_1772, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_1745, c_24])).
% 6.96/2.58  tff(c_1787, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_1772])).
% 6.96/2.58  tff(c_1788, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_1708])).
% 6.96/2.58  tff(c_38, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.96/2.58  tff(c_571, plain, (![A_132, B_133, C_134, D_135]: (k5_mcart_1(A_132, B_133, C_134, D_135)=k1_mcart_1(k1_mcart_1(D_135)) | ~m1_subset_1(D_135, k3_zfmisc_1(A_132, B_133, C_134)) | k1_xboole_0=C_134 | k1_xboole_0=B_133 | k1_xboole_0=A_132)), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.96/2.58  tff(c_606, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_571])).
% 6.96/2.58  tff(c_626, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_606])).
% 6.96/2.58  tff(c_1789, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_1708])).
% 6.96/2.58  tff(c_14, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_50])).
% 6.96/2.58  tff(c_145, plain, (![A_73, B_74, C_75]: (r2_hidden(k1_mcart_1(A_73), B_74) | ~r2_hidden(A_73, k2_zfmisc_1(B_74, C_75)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.96/2.58  tff(c_772, plain, (![A_148, A_149, B_150, C_151]: (r2_hidden(k1_mcart_1(A_148), k2_zfmisc_1(A_149, B_150)) | ~r2_hidden(A_148, k3_zfmisc_1(A_149, B_150, C_151)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_145])).
% 6.96/2.58  tff(c_4190, plain, (![A_354, A_355, B_356, C_357]: (r2_hidden(k1_mcart_1(A_354), k2_zfmisc_1(A_355, B_356)) | v1_xboole_0(k3_zfmisc_1(A_355, B_356, C_357)) | ~m1_subset_1(A_354, k3_zfmisc_1(A_355, B_356, C_357)))), inference(resolution, [status(thm)], [c_8, c_772])).
% 6.96/2.58  tff(c_4287, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_4190])).
% 6.96/2.58  tff(c_4328, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1789, c_4287])).
% 6.96/2.58  tff(c_20, plain, (![A_19, B_20, C_21]: (r2_hidden(k1_mcart_1(A_19), B_20) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.96/2.58  tff(c_4335, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_4328, c_20])).
% 6.96/2.58  tff(c_4345, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_626, c_4335])).
% 6.96/2.58  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.96/2.58  tff(c_4368, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_4345, c_6])).
% 6.96/2.58  tff(c_390, plain, (![A_116, B_117, C_118, D_119]: (k6_mcart_1(A_116, B_117, C_118, D_119)=k2_mcart_1(k1_mcart_1(D_119)) | ~m1_subset_1(D_119, k3_zfmisc_1(A_116, B_117, C_118)) | k1_xboole_0=C_118 | k1_xboole_0=B_117 | k1_xboole_0=A_116)), inference(cnfTransformation, [status(thm)], [f_98])).
% 6.96/2.58  tff(c_409, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_390])).
% 6.96/2.58  tff(c_425, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_409])).
% 6.96/2.58  tff(c_18, plain, (![A_19, C_21, B_20]: (r2_hidden(k2_mcart_1(A_19), C_21) | ~r2_hidden(A_19, k2_zfmisc_1(B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 6.96/2.58  tff(c_4337, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_4328, c_18])).
% 6.96/2.58  tff(c_4347, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_425, c_4337])).
% 6.96/2.58  tff(c_4375, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_4347, c_6])).
% 6.96/2.58  tff(c_22, plain, (![A_22, B_23]: (k4_tarski(k1_mcart_1(A_22), k2_mcart_1(A_22))=A_22 | ~r2_hidden(A_22, B_23) | ~v1_relat_1(B_23))), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.96/2.58  tff(c_4333, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_4328, c_22])).
% 6.96/2.58  tff(c_4343, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_425, c_626, c_4333])).
% 6.96/2.58  tff(c_12, plain, (![A_9, B_10, C_11]: (k4_tarski(k4_tarski(A_9, B_10), C_11)=k3_mcart_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_48])).
% 6.96/2.58  tff(c_4939, plain, (![C_392]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_392)=k4_tarski(k1_mcart_1('#skF_5'), C_392))), inference(superposition, [status(thm), theory('equality')], [c_4343, c_12])).
% 6.96/2.58  tff(c_46, plain, (![G_43, F_39, H_45]: (G_43='#skF_4' | k3_mcart_1(F_39, G_43, H_45)!='#skF_5' | ~m1_subset_1(H_45, '#skF_3') | ~m1_subset_1(G_43, '#skF_2') | ~m1_subset_1(F_39, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.96/2.58  tff(c_4946, plain, (![C_392]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_392)!='#skF_5' | ~m1_subset_1(C_392, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4939, c_46])).
% 6.96/2.58  tff(c_4953, plain, (![C_392]: (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_392)!='#skF_5' | ~m1_subset_1(C_392, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4368, c_4375, c_4946])).
% 6.96/2.58  tff(c_4956, plain, (![C_393]: (k4_tarski(k1_mcart_1('#skF_5'), C_393)!='#skF_5' | ~m1_subset_1(C_393, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_4953])).
% 6.96/2.58  tff(c_4959, plain, (~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1788, c_4956])).
% 6.96/2.58  tff(c_4963, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_348, c_4959])).
% 6.96/2.58  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.96/2.58  
% 6.96/2.58  Inference rules
% 6.96/2.58  ----------------------
% 6.96/2.58  #Ref     : 0
% 6.96/2.58  #Sup     : 1296
% 6.96/2.58  #Fact    : 0
% 6.96/2.58  #Define  : 0
% 6.96/2.58  #Split   : 5
% 6.96/2.58  #Chain   : 0
% 6.96/2.58  #Close   : 0
% 6.96/2.58  
% 6.96/2.58  Ordering : KBO
% 6.96/2.58  
% 6.96/2.58  Simplification rules
% 6.96/2.58  ----------------------
% 6.96/2.58  #Subsume      : 329
% 6.96/2.58  #Demod        : 218
% 6.96/2.58  #Tautology    : 149
% 6.96/2.58  #SimpNegUnit  : 10
% 6.96/2.58  #BackRed      : 2
% 6.96/2.58  
% 6.96/2.58  #Partial instantiations: 0
% 6.96/2.58  #Strategies tried      : 1
% 6.96/2.58  
% 6.96/2.58  Timing (in seconds)
% 6.96/2.58  ----------------------
% 6.96/2.58  Preprocessing        : 0.40
% 6.96/2.58  Parsing              : 0.22
% 6.96/2.58  CNF conversion       : 0.03
% 6.96/2.58  Main loop            : 1.28
% 6.96/2.58  Inferencing          : 0.41
% 6.96/2.58  Reduction            : 0.31
% 6.96/2.58  Demodulation         : 0.21
% 6.96/2.58  BG Simplification    : 0.06
% 6.96/2.58  Subsumption          : 0.40
% 6.96/2.58  Abstraction          : 0.08
% 6.96/2.58  MUC search           : 0.00
% 6.96/2.58  Cooper               : 0.00
% 6.96/2.58  Total                : 1.72
% 6.96/2.58  Index Insertion      : 0.00
% 6.96/2.58  Index Deletion       : 0.00
% 6.96/2.58  Index Matching       : 0.00
% 6.96/2.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------
