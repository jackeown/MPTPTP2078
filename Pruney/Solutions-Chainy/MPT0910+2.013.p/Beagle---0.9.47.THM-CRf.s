%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:01 EST 2020

% Result     : Theorem 7.89s
% Output     : CNFRefutation 7.89s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 276 expanded)
%              Number of leaves         :   32 ( 112 expanded)
%              Depth                    :   11
%              Number of atoms          :  197 ( 950 expanded)
%              Number of equality atoms :   86 ( 512 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(f_52,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_86,axiom,(
    ! [A,B,C] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0
        & ~ ! [D] :
              ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
             => D = k3_mcart_1(k5_mcart_1(A,B,C,D),k6_mcart_1(A,B,C,D),k7_mcart_1(A,B,C,D)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => m1_subset_1(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

tff(c_36,plain,(
    k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_46,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_292,plain,(
    ! [A_106,B_107,C_108,D_109] :
      ( k7_mcart_1(A_106,B_107,C_108,D_109) = k2_mcart_1(D_109)
      | ~ m1_subset_1(D_109,k3_zfmisc_1(A_106,B_107,C_108))
      | k1_xboole_0 = C_108
      | k1_xboole_0 = B_107
      | k1_xboole_0 = A_106 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_311,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_292])).

tff(c_327,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_311])).

tff(c_14,plain,(
    ! [A_13,B_14,C_15,D_16] :
      ( m1_subset_1(k7_mcart_1(A_13,B_14,C_15,D_16),C_15)
      | ~ m1_subset_1(D_16,k3_zfmisc_1(A_13,B_14,C_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_334,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_14])).

tff(c_338,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_334])).

tff(c_661,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( k3_mcart_1(k5_mcart_1(A_138,B_139,C_140,D_141),k6_mcart_1(A_138,B_139,C_140,D_141),k7_mcart_1(A_138,B_139,C_140,D_141)) = D_141
      | ~ m1_subset_1(D_141,k3_zfmisc_1(A_138,B_139,C_140))
      | k1_xboole_0 = C_140
      | k1_xboole_0 = B_139
      | k1_xboole_0 = A_138 ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_672,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_661])).

tff(c_676,plain,
    ( k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_672])).

tff(c_677,plain,(
    k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_676])).

tff(c_44,plain,(
    ! [G_44,F_40,H_46] :
      ( G_44 = '#skF_4'
      | k3_mcart_1(F_40,G_44,H_46) != '#skF_5'
      | ~ m1_subset_1(H_46,'#skF_3')
      | ~ m1_subset_1(G_44,'#skF_2')
      | ~ m1_subset_1(F_40,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_130])).

tff(c_720,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_677,c_44])).

tff(c_725,plain,
    ( k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = '#skF_4'
    | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_720])).

tff(c_726,plain,
    ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
    | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_725])).

tff(c_839,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_726])).

tff(c_472,plain,(
    ! [A_122,B_123,C_124,D_125] :
      ( k5_mcart_1(A_122,B_123,C_124,D_125) = k1_mcart_1(k1_mcart_1(D_125))
      | ~ m1_subset_1(D_125,k3_zfmisc_1(A_122,B_123,C_124))
      | k1_xboole_0 = C_124
      | k1_xboole_0 = B_123
      | k1_xboole_0 = A_122 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_503,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_472])).

tff(c_522,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_503])).

tff(c_12,plain,(
    ! [A_10,B_11,C_12] : k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12) = k3_zfmisc_1(A_10,B_11,C_12) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r2_hidden(A_5,B_6)
      | v1_xboole_0(B_6)
      | ~ m1_subset_1(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_108,plain,(
    ! [A_60,C_61,B_62] :
      ( r2_hidden(k2_mcart_1(A_60),C_61)
      | ~ r2_hidden(A_60,k2_zfmisc_1(B_62,C_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1896,plain,(
    ! [A_256,C_257,B_258] :
      ( r2_hidden(k2_mcart_1(A_256),C_257)
      | v1_xboole_0(k2_zfmisc_1(B_258,C_257))
      | ~ m1_subset_1(A_256,k2_zfmisc_1(B_258,C_257)) ) ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_1984,plain,(
    ! [A_256,C_12,A_10,B_11] :
      ( r2_hidden(k2_mcart_1(A_256),C_12)
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12))
      | ~ m1_subset_1(A_256,k3_zfmisc_1(A_10,B_11,C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1896])).

tff(c_3544,plain,(
    ! [A_347,C_348,A_349,B_350] :
      ( r2_hidden(k2_mcart_1(A_347),C_348)
      | v1_xboole_0(k3_zfmisc_1(A_349,B_350,C_348))
      | ~ m1_subset_1(A_347,k3_zfmisc_1(A_349,B_350,C_348)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1984])).

tff(c_3680,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_3544])).

tff(c_3684,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3680])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_93,plain,(
    ! [B_55,A_56] :
      ( ~ v1_xboole_0(B_55)
      | B_55 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [A_56] :
      ( k1_xboole_0 = A_56
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_2,c_93])).

tff(c_3690,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_3684,c_96])).

tff(c_20,plain,(
    ! [A_20,B_21,C_22] :
      ( k3_zfmisc_1(A_20,B_21,C_22) != k1_xboole_0
      | k1_xboole_0 = C_22
      | k1_xboole_0 = B_21
      | k1_xboole_0 = A_20 ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_3724,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_3690,c_20])).

tff(c_3747,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_3724])).

tff(c_3749,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_3680])).

tff(c_145,plain,(
    ! [A_69,B_70,C_71] :
      ( r2_hidden(k1_mcart_1(A_69),B_70)
      | ~ r2_hidden(A_69,k2_zfmisc_1(B_70,C_71)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1634,plain,(
    ! [A_241,B_242,C_243] :
      ( r2_hidden(k1_mcart_1(A_241),B_242)
      | v1_xboole_0(k2_zfmisc_1(B_242,C_243))
      | ~ m1_subset_1(A_241,k2_zfmisc_1(B_242,C_243)) ) ),
    inference(resolution,[status(thm)],[c_8,c_145])).

tff(c_1710,plain,(
    ! [A_241,A_10,B_11,C_12] :
      ( r2_hidden(k1_mcart_1(A_241),k2_zfmisc_1(A_10,B_11))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10,B_11),C_12))
      | ~ m1_subset_1(A_241,k3_zfmisc_1(A_10,B_11,C_12)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1634])).

tff(c_3907,plain,(
    ! [A_361,A_362,B_363,C_364] :
      ( r2_hidden(k1_mcart_1(A_361),k2_zfmisc_1(A_362,B_363))
      | v1_xboole_0(k3_zfmisc_1(A_362,B_363,C_364))
      | ~ m1_subset_1(A_361,k3_zfmisc_1(A_362,B_363,C_364)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_1710])).

tff(c_4007,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_3907])).

tff(c_4049,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_3749,c_4007])).

tff(c_18,plain,(
    ! [A_17,B_18,C_19] :
      ( r2_hidden(k1_mcart_1(A_17),B_18)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4054,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4049,c_18])).

tff(c_4061,plain,(
    r2_hidden(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_522,c_4054])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( m1_subset_1(A_3,B_4)
      | ~ r2_hidden(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4075,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_4061,c_6])).

tff(c_4079,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_839,c_4075])).

tff(c_4080,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_726])).

tff(c_357,plain,(
    ! [A_112,B_113,C_114,D_115] :
      ( k6_mcart_1(A_112,B_113,C_114,D_115) = k2_mcart_1(k1_mcart_1(D_115))
      | ~ m1_subset_1(D_115,k3_zfmisc_1(A_112,B_113,C_114))
      | k1_xboole_0 = C_114
      | k1_xboole_0 = B_113
      | k1_xboole_0 = A_112 ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_376,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_46,c_357])).

tff(c_392,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_376])).

tff(c_113,plain,(
    ! [A_63,B_64,C_65] : k2_zfmisc_1(k2_zfmisc_1(A_63,B_64),C_65) = k3_zfmisc_1(A_63,B_64,C_65) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_16,plain,(
    ! [A_17,C_19,B_18] :
      ( r2_hidden(k2_mcart_1(A_17),C_19)
      | ~ r2_hidden(A_17,k2_zfmisc_1(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_152,plain,(
    ! [A_72,C_73,A_74,B_75] :
      ( r2_hidden(k2_mcart_1(A_72),C_73)
      | ~ r2_hidden(A_72,k3_zfmisc_1(A_74,B_75,C_73)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_113,c_16])).

tff(c_6622,plain,(
    ! [A_540,C_541,A_542,B_543] :
      ( r2_hidden(k2_mcart_1(A_540),C_541)
      | v1_xboole_0(k3_zfmisc_1(A_542,B_543,C_541))
      | ~ m1_subset_1(A_540,k3_zfmisc_1(A_542,B_543,C_541)) ) ),
    inference(resolution,[status(thm)],[c_8,c_152])).

tff(c_6758,plain,
    ( r2_hidden(k2_mcart_1('#skF_5'),'#skF_3')
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_6622])).

tff(c_6762,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_6758])).

tff(c_6768,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6762,c_96])).

tff(c_6802,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_6768,c_20])).

tff(c_6825,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_40,c_38,c_6802])).

tff(c_6827,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_6758])).

tff(c_4147,plain,(
    ! [A_375,A_376,B_377,C_378] :
      ( r2_hidden(k1_mcart_1(A_375),k2_zfmisc_1(A_376,B_377))
      | ~ r2_hidden(A_375,k3_zfmisc_1(A_376,B_377,C_378)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_145])).

tff(c_7106,plain,(
    ! [A_562,A_563,B_564,C_565] :
      ( r2_hidden(k1_mcart_1(A_562),k2_zfmisc_1(A_563,B_564))
      | v1_xboole_0(k3_zfmisc_1(A_563,B_564,C_565))
      | ~ m1_subset_1(A_562,k3_zfmisc_1(A_563,B_564,C_565)) ) ),
    inference(resolution,[status(thm)],[c_8,c_4147])).

tff(c_7203,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_46,c_7106])).

tff(c_7244,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_6827,c_7203])).

tff(c_7251,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7244,c_16])).

tff(c_7258,plain,(
    r2_hidden(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_392,c_7251])).

tff(c_7275,plain,(
    m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_7258,c_6])).

tff(c_7279,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_4080,c_7275])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:58:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.89/2.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/2.84  
% 7.89/2.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/2.85  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.89/2.85  
% 7.89/2.85  %Foreground sorts:
% 7.89/2.85  
% 7.89/2.85  
% 7.89/2.85  %Background operators:
% 7.89/2.85  
% 7.89/2.85  
% 7.89/2.85  %Foreground operators:
% 7.89/2.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.89/2.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.89/2.85  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 7.89/2.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.89/2.85  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 7.89/2.85  tff('#skF_5', type, '#skF_5': $i).
% 7.89/2.85  tff('#skF_2', type, '#skF_2': $i).
% 7.89/2.85  tff('#skF_3', type, '#skF_3': $i).
% 7.89/2.85  tff('#skF_1', type, '#skF_1': $i).
% 7.89/2.85  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 7.89/2.85  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 7.89/2.85  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 7.89/2.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.89/2.85  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 7.89/2.85  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.89/2.85  tff('#skF_4', type, '#skF_4': $i).
% 7.89/2.85  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 7.89/2.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.89/2.85  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 7.89/2.85  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 7.89/2.85  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 7.89/2.85  
% 7.89/2.86  tff(f_130, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = G)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k6_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_mcart_1)).
% 7.89/2.86  tff(f_106, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 7.89/2.86  tff(f_52, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 7.89/2.86  tff(f_86, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (D = k3_mcart_1(k5_mcart_1(A, B, C, D), k6_mcart_1(A, B, C, D), k7_mcart_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_mcart_1)).
% 7.89/2.86  tff(f_48, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 7.89/2.86  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 7.89/2.86  tff(f_58, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 7.89/2.86  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 7.89/2.86  tff(f_34, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 7.89/2.86  tff(f_70, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 7.89/2.86  tff(f_38, axiom, (![A, B]: (r2_hidden(A, B) => m1_subset_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_subset)).
% 7.89/2.86  tff(c_36, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.89/2.86  tff(c_46, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.89/2.86  tff(c_42, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.89/2.86  tff(c_40, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.89/2.86  tff(c_38, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.89/2.86  tff(c_292, plain, (![A_106, B_107, C_108, D_109]: (k7_mcart_1(A_106, B_107, C_108, D_109)=k2_mcart_1(D_109) | ~m1_subset_1(D_109, k3_zfmisc_1(A_106, B_107, C_108)) | k1_xboole_0=C_108 | k1_xboole_0=B_107 | k1_xboole_0=A_106)), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.89/2.86  tff(c_311, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_292])).
% 7.89/2.86  tff(c_327, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_311])).
% 7.89/2.86  tff(c_14, plain, (![A_13, B_14, C_15, D_16]: (m1_subset_1(k7_mcart_1(A_13, B_14, C_15, D_16), C_15) | ~m1_subset_1(D_16, k3_zfmisc_1(A_13, B_14, C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 7.89/2.86  tff(c_334, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_327, c_14])).
% 7.89/2.86  tff(c_338, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_46, c_334])).
% 7.89/2.86  tff(c_661, plain, (![A_138, B_139, C_140, D_141]: (k3_mcart_1(k5_mcart_1(A_138, B_139, C_140, D_141), k6_mcart_1(A_138, B_139, C_140, D_141), k7_mcart_1(A_138, B_139, C_140, D_141))=D_141 | ~m1_subset_1(D_141, k3_zfmisc_1(A_138, B_139, C_140)) | k1_xboole_0=C_140 | k1_xboole_0=B_139 | k1_xboole_0=A_138)), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.89/2.86  tff(c_672, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_327, c_661])).
% 7.89/2.86  tff(c_676, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_672])).
% 7.89/2.86  tff(c_677, plain, (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_676])).
% 7.89/2.86  tff(c_44, plain, (![G_44, F_40, H_46]: (G_44='#skF_4' | k3_mcart_1(F_40, G_44, H_46)!='#skF_5' | ~m1_subset_1(H_46, '#skF_3') | ~m1_subset_1(G_44, '#skF_2') | ~m1_subset_1(F_40, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_130])).
% 7.89/2.86  tff(c_720, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_677, c_44])).
% 7.89/2.86  tff(c_725, plain, (k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')='#skF_4' | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_338, c_720])).
% 7.89/2.86  tff(c_726, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_36, c_725])).
% 7.89/2.86  tff(c_839, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_726])).
% 7.89/2.86  tff(c_472, plain, (![A_122, B_123, C_124, D_125]: (k5_mcart_1(A_122, B_123, C_124, D_125)=k1_mcart_1(k1_mcart_1(D_125)) | ~m1_subset_1(D_125, k3_zfmisc_1(A_122, B_123, C_124)) | k1_xboole_0=C_124 | k1_xboole_0=B_123 | k1_xboole_0=A_122)), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.89/2.86  tff(c_503, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_472])).
% 7.89/2.86  tff(c_522, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_503])).
% 7.89/2.86  tff(c_12, plain, (![A_10, B_11, C_12]: (k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)=k3_zfmisc_1(A_10, B_11, C_12))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.89/2.86  tff(c_8, plain, (![A_5, B_6]: (r2_hidden(A_5, B_6) | v1_xboole_0(B_6) | ~m1_subset_1(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 7.89/2.86  tff(c_108, plain, (![A_60, C_61, B_62]: (r2_hidden(k2_mcart_1(A_60), C_61) | ~r2_hidden(A_60, k2_zfmisc_1(B_62, C_61)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.89/2.86  tff(c_1896, plain, (![A_256, C_257, B_258]: (r2_hidden(k2_mcart_1(A_256), C_257) | v1_xboole_0(k2_zfmisc_1(B_258, C_257)) | ~m1_subset_1(A_256, k2_zfmisc_1(B_258, C_257)))), inference(resolution, [status(thm)], [c_8, c_108])).
% 7.89/2.86  tff(c_1984, plain, (![A_256, C_12, A_10, B_11]: (r2_hidden(k2_mcart_1(A_256), C_12) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)) | ~m1_subset_1(A_256, k3_zfmisc_1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1896])).
% 7.89/2.86  tff(c_3544, plain, (![A_347, C_348, A_349, B_350]: (r2_hidden(k2_mcart_1(A_347), C_348) | v1_xboole_0(k3_zfmisc_1(A_349, B_350, C_348)) | ~m1_subset_1(A_347, k3_zfmisc_1(A_349, B_350, C_348)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1984])).
% 7.89/2.86  tff(c_3680, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_3544])).
% 7.89/2.86  tff(c_3684, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_3680])).
% 7.89/2.86  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 7.89/2.86  tff(c_93, plain, (![B_55, A_56]: (~v1_xboole_0(B_55) | B_55=A_56 | ~v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_34])).
% 7.89/2.86  tff(c_96, plain, (![A_56]: (k1_xboole_0=A_56 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_2, c_93])).
% 7.89/2.86  tff(c_3690, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_3684, c_96])).
% 7.89/2.86  tff(c_20, plain, (![A_20, B_21, C_22]: (k3_zfmisc_1(A_20, B_21, C_22)!=k1_xboole_0 | k1_xboole_0=C_22 | k1_xboole_0=B_21 | k1_xboole_0=A_20)), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.89/2.86  tff(c_3724, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_3690, c_20])).
% 7.89/2.86  tff(c_3747, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_3724])).
% 7.89/2.86  tff(c_3749, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_3680])).
% 7.89/2.86  tff(c_145, plain, (![A_69, B_70, C_71]: (r2_hidden(k1_mcart_1(A_69), B_70) | ~r2_hidden(A_69, k2_zfmisc_1(B_70, C_71)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.89/2.86  tff(c_1634, plain, (![A_241, B_242, C_243]: (r2_hidden(k1_mcart_1(A_241), B_242) | v1_xboole_0(k2_zfmisc_1(B_242, C_243)) | ~m1_subset_1(A_241, k2_zfmisc_1(B_242, C_243)))), inference(resolution, [status(thm)], [c_8, c_145])).
% 7.89/2.86  tff(c_1710, plain, (![A_241, A_10, B_11, C_12]: (r2_hidden(k1_mcart_1(A_241), k2_zfmisc_1(A_10, B_11)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_10, B_11), C_12)) | ~m1_subset_1(A_241, k3_zfmisc_1(A_10, B_11, C_12)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1634])).
% 7.89/2.86  tff(c_3907, plain, (![A_361, A_362, B_363, C_364]: (r2_hidden(k1_mcart_1(A_361), k2_zfmisc_1(A_362, B_363)) | v1_xboole_0(k3_zfmisc_1(A_362, B_363, C_364)) | ~m1_subset_1(A_361, k3_zfmisc_1(A_362, B_363, C_364)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_1710])).
% 7.89/2.86  tff(c_4007, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_3907])).
% 7.89/2.86  tff(c_4049, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_3749, c_4007])).
% 7.89/2.86  tff(c_18, plain, (![A_17, B_18, C_19]: (r2_hidden(k1_mcart_1(A_17), B_18) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.89/2.86  tff(c_4054, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1')), inference(resolution, [status(thm)], [c_4049, c_18])).
% 7.89/2.86  tff(c_4061, plain, (r2_hidden(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_522, c_4054])).
% 7.89/2.86  tff(c_6, plain, (![A_3, B_4]: (m1_subset_1(A_3, B_4) | ~r2_hidden(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_38])).
% 7.89/2.86  tff(c_4075, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(resolution, [status(thm)], [c_4061, c_6])).
% 7.89/2.86  tff(c_4079, plain, $false, inference(negUnitSimplification, [status(thm)], [c_839, c_4075])).
% 7.89/2.86  tff(c_4080, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitRight, [status(thm)], [c_726])).
% 7.89/2.86  tff(c_357, plain, (![A_112, B_113, C_114, D_115]: (k6_mcart_1(A_112, B_113, C_114, D_115)=k2_mcart_1(k1_mcart_1(D_115)) | ~m1_subset_1(D_115, k3_zfmisc_1(A_112, B_113, C_114)) | k1_xboole_0=C_114 | k1_xboole_0=B_113 | k1_xboole_0=A_112)), inference(cnfTransformation, [status(thm)], [f_106])).
% 7.89/2.86  tff(c_376, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_46, c_357])).
% 7.89/2.86  tff(c_392, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_376])).
% 7.89/2.86  tff(c_113, plain, (![A_63, B_64, C_65]: (k2_zfmisc_1(k2_zfmisc_1(A_63, B_64), C_65)=k3_zfmisc_1(A_63, B_64, C_65))), inference(cnfTransformation, [status(thm)], [f_48])).
% 7.89/2.86  tff(c_16, plain, (![A_17, C_19, B_18]: (r2_hidden(k2_mcart_1(A_17), C_19) | ~r2_hidden(A_17, k2_zfmisc_1(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 7.89/2.86  tff(c_152, plain, (![A_72, C_73, A_74, B_75]: (r2_hidden(k2_mcart_1(A_72), C_73) | ~r2_hidden(A_72, k3_zfmisc_1(A_74, B_75, C_73)))), inference(superposition, [status(thm), theory('equality')], [c_113, c_16])).
% 7.89/2.86  tff(c_6622, plain, (![A_540, C_541, A_542, B_543]: (r2_hidden(k2_mcart_1(A_540), C_541) | v1_xboole_0(k3_zfmisc_1(A_542, B_543, C_541)) | ~m1_subset_1(A_540, k3_zfmisc_1(A_542, B_543, C_541)))), inference(resolution, [status(thm)], [c_8, c_152])).
% 7.89/2.86  tff(c_6758, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_3') | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_6622])).
% 7.89/2.86  tff(c_6762, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_6758])).
% 7.89/2.86  tff(c_6768, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_6762, c_96])).
% 7.89/2.86  tff(c_6802, plain, (k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_6768, c_20])).
% 7.89/2.86  tff(c_6825, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_40, c_38, c_6802])).
% 7.89/2.86  tff(c_6827, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_6758])).
% 7.89/2.86  tff(c_4147, plain, (![A_375, A_376, B_377, C_378]: (r2_hidden(k1_mcart_1(A_375), k2_zfmisc_1(A_376, B_377)) | ~r2_hidden(A_375, k3_zfmisc_1(A_376, B_377, C_378)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_145])).
% 7.89/2.86  tff(c_7106, plain, (![A_562, A_563, B_564, C_565]: (r2_hidden(k1_mcart_1(A_562), k2_zfmisc_1(A_563, B_564)) | v1_xboole_0(k3_zfmisc_1(A_563, B_564, C_565)) | ~m1_subset_1(A_562, k3_zfmisc_1(A_563, B_564, C_565)))), inference(resolution, [status(thm)], [c_8, c_4147])).
% 7.89/2.86  tff(c_7203, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_46, c_7106])).
% 7.89/2.86  tff(c_7244, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_6827, c_7203])).
% 7.89/2.86  tff(c_7251, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2')), inference(resolution, [status(thm)], [c_7244, c_16])).
% 7.89/2.86  tff(c_7258, plain, (r2_hidden(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_392, c_7251])).
% 7.89/2.86  tff(c_7275, plain, (m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(resolution, [status(thm)], [c_7258, c_6])).
% 7.89/2.86  tff(c_7279, plain, $false, inference(negUnitSimplification, [status(thm)], [c_4080, c_7275])).
% 7.89/2.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.89/2.86  
% 7.89/2.86  Inference rules
% 7.89/2.86  ----------------------
% 7.89/2.86  #Ref     : 0
% 7.89/2.86  #Sup     : 1878
% 7.89/2.86  #Fact    : 0
% 7.89/2.86  #Define  : 0
% 7.89/2.86  #Split   : 6
% 7.89/2.86  #Chain   : 0
% 7.89/2.86  #Close   : 0
% 7.89/2.86  
% 7.89/2.86  Ordering : KBO
% 7.89/2.86  
% 7.89/2.86  Simplification rules
% 7.89/2.86  ----------------------
% 7.89/2.86  #Subsume      : 534
% 7.89/2.86  #Demod        : 395
% 7.89/2.86  #Tautology    : 219
% 7.89/2.86  #SimpNegUnit  : 35
% 7.89/2.86  #BackRed      : 4
% 7.89/2.86  
% 7.89/2.86  #Partial instantiations: 0
% 7.89/2.86  #Strategies tried      : 1
% 7.89/2.86  
% 7.89/2.86  Timing (in seconds)
% 7.89/2.86  ----------------------
% 7.89/2.87  Preprocessing        : 0.37
% 7.89/2.87  Parsing              : 0.19
% 7.89/2.87  CNF conversion       : 0.03
% 7.89/2.87  Main loop            : 1.68
% 7.89/2.87  Inferencing          : 0.53
% 7.89/2.87  Reduction            : 0.40
% 7.89/2.87  Demodulation         : 0.26
% 7.89/2.87  BG Simplification    : 0.07
% 7.89/2.87  Subsumption          : 0.54
% 7.89/2.87  Abstraction          : 0.09
% 7.89/2.87  MUC search           : 0.00
% 7.89/2.87  Cooper               : 0.00
% 7.89/2.87  Total                : 2.09
% 7.89/2.87  Index Insertion      : 0.00
% 7.89/2.87  Index Deletion       : 0.00
% 7.89/2.87  Index Matching       : 0.00
% 7.89/2.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------
