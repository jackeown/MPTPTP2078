%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:04 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 4.05s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 824 expanded)
%              Number of leaves         :   39 ( 298 expanded)
%              Depth                    :   21
%              Number of atoms          :  314 (2544 expanded)
%              Number of equality atoms :  167 (1307 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_126,negated_conjecture,(
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

tff(f_102,axiom,(
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

tff(f_70,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_58,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_40,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_82,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k6_mcart_1(A,B,C,D),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_mcart_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k5_mcart_1(A,B,C,D),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k5_mcart_1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_56,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( A != k1_xboole_0
        & B != k1_xboole_0
        & ~ ( k1_relat_1(k2_zfmisc_1(A,B)) = A
            & k2_relat_1(k2_zfmisc_1(A,B)) = B ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t195_relat_1)).

tff(c_44,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_42,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_48,plain,(
    m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1170,plain,(
    ! [A_253,B_254,C_255,D_256] :
      ( k7_mcart_1(A_253,B_254,C_255,D_256) = k2_mcart_1(D_256)
      | ~ m1_subset_1(D_256,k3_zfmisc_1(A_253,B_254,C_255))
      | k1_xboole_0 = C_255
      | k1_xboole_0 = B_254
      | k1_xboole_0 = A_253 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1188,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_1170])).

tff(c_1194,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_1188])).

tff(c_38,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1195,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1194,c_38])).

tff(c_24,plain,(
    ! [A_23,B_24,C_25,D_26] :
      ( m1_subset_1(k7_mcart_1(A_23,B_24,C_25,D_26),C_25)
      | ~ m1_subset_1(D_26,k3_zfmisc_1(A_23,B_24,C_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1199,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1194,c_24])).

tff(c_1203,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1199])).

tff(c_392,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( k7_mcart_1(A_134,B_135,C_136,D_137) = k2_mcart_1(D_137)
      | ~ m1_subset_1(D_137,k3_zfmisc_1(A_134,B_135,C_136))
      | k1_xboole_0 = C_136
      | k1_xboole_0 = B_135
      | k1_xboole_0 = A_134 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_410,plain,
    ( k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_392])).

tff(c_416,plain,(
    k7_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') = k2_mcart_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_410])).

tff(c_417,plain,(
    k2_mcart_1('#skF_5') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_38])).

tff(c_421,plain,
    ( m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3')
    | ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_24])).

tff(c_425,plain,(
    m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_421])).

tff(c_96,plain,(
    ! [A_61,B_62,C_63] : k2_zfmisc_1(k2_zfmisc_1(A_61,B_62),C_63) = k3_zfmisc_1(A_61,B_62,C_63) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_10,plain,(
    ! [A_5,B_6] : v1_relat_1(k2_zfmisc_1(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_104,plain,(
    ! [A_61,B_62,C_63] : v1_relat_1(k3_zfmisc_1(A_61,B_62,C_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_10])).

tff(c_8,plain,(
    ! [A_4] :
      ( v1_xboole_0(k1_relat_1(A_4))
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_55,plain,(
    ! [A_54] :
      ( v1_xboole_0(k1_relat_1(A_54))
      | ~ v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_60,plain,(
    ! [A_55] :
      ( k1_relat_1(A_55) = k1_xboole_0
      | ~ v1_xboole_0(A_55) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_65,plain,(
    ! [A_56] :
      ( k1_relat_1(k1_relat_1(A_56)) = k1_xboole_0
      | ~ v1_xboole_0(A_56) ) ),
    inference(resolution,[status(thm)],[c_8,c_60])).

tff(c_74,plain,(
    ! [A_56] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(k1_relat_1(A_56))
      | ~ v1_xboole_0(A_56) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_65,c_8])).

tff(c_84,plain,(
    ! [A_57] :
      ( ~ v1_xboole_0(k1_relat_1(A_57))
      | ~ v1_xboole_0(A_57) ) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_91,plain,(
    ! [A_4] : ~ v1_xboole_0(A_4) ),
    inference(resolution,[status(thm)],[c_8,c_84])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | v1_xboole_0(B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_94,plain,(
    ! [A_2,B_3] :
      ( r2_hidden(A_2,B_3)
      | ~ m1_subset_1(A_2,B_3) ) ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_6])).

tff(c_174,plain,(
    ! [A_83,B_84] :
      ( k4_tarski(k1_mcart_1(A_83),k2_mcart_1(A_83)) = A_83
      | ~ r2_hidden(A_83,B_84)
      | ~ v1_relat_1(B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_209,plain,(
    ! [A_103,B_104] :
      ( k4_tarski(k1_mcart_1(A_103),k2_mcart_1(A_103)) = A_103
      | ~ v1_relat_1(B_104)
      | ~ m1_subset_1(A_103,B_104) ) ),
    inference(resolution,[status(thm)],[c_94,c_174])).

tff(c_213,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_209])).

tff(c_217,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_213])).

tff(c_22,plain,(
    ! [A_19,B_20,C_21,D_22] :
      ( m1_subset_1(k6_mcart_1(A_19,B_20,C_21,D_22),B_20)
      | ~ m1_subset_1(D_22,k3_zfmisc_1(A_19,B_20,C_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_533,plain,(
    ! [A_150,B_151,C_152,D_153] :
      ( k6_mcart_1(A_150,B_151,C_152,D_153) = k2_mcart_1(k1_mcart_1(D_153))
      | ~ m1_subset_1(D_153,k3_zfmisc_1(A_150,B_151,C_152))
      | k1_xboole_0 = C_152
      | k1_xboole_0 = B_151
      | k1_xboole_0 = A_150 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_551,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_533])).

tff(c_557,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_551])).

tff(c_20,plain,(
    ! [A_15,B_16,C_17,D_18] :
      ( m1_subset_1(k5_mcart_1(A_15,B_16,C_17,D_18),A_15)
      | ~ m1_subset_1(D_18,k3_zfmisc_1(A_15,B_16,C_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_456,plain,(
    ! [A_145,B_146,C_147,D_148] :
      ( k5_mcart_1(A_145,B_146,C_147,D_148) = k1_mcart_1(k1_mcart_1(D_148))
      | ~ m1_subset_1(D_148,k3_zfmisc_1(A_145,B_146,C_147))
      | k1_xboole_0 = C_147
      | k1_xboole_0 = B_146
      | k1_xboole_0 = A_145 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_474,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_456])).

tff(c_480,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_474])).

tff(c_18,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14) = k3_zfmisc_1(A_12,B_13,C_14) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_167,plain,(
    ! [A_80,B_81,C_82] :
      ( r2_hidden(k1_mcart_1(A_80),B_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_81,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_285,plain,(
    ! [A_117,A_118,B_119,C_120] :
      ( r2_hidden(k1_mcart_1(A_117),k2_zfmisc_1(A_118,B_119))
      | ~ r2_hidden(A_117,k3_zfmisc_1(A_118,B_119,C_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_167])).

tff(c_335,plain,(
    ! [A_129,A_130,B_131,C_132] :
      ( r2_hidden(k1_mcart_1(A_129),k2_zfmisc_1(A_130,B_131))
      | ~ m1_subset_1(A_129,k3_zfmisc_1(A_130,B_131,C_132)) ) ),
    inference(resolution,[status(thm)],[c_94,c_285])).

tff(c_353,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_48,c_335])).

tff(c_30,plain,(
    ! [A_30,B_31] :
      ( k4_tarski(k1_mcart_1(A_30),k2_mcart_1(A_30)) = A_30
      | ~ r2_hidden(A_30,B_31)
      | ~ v1_relat_1(B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_355,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_353,c_30])).

tff(c_362,plain,(
    k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_355])).

tff(c_16,plain,(
    ! [A_9,B_10,C_11] : k4_tarski(k4_tarski(A_9,B_10),C_11) = k3_mcart_1(A_9,B_10,C_11) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_381,plain,(
    ! [C_133] : k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5')),C_133) = k4_tarski(k1_mcart_1('#skF_5'),C_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_16])).

tff(c_46,plain,(
    ! [H_50,F_44,G_48] :
      ( H_50 = '#skF_4'
      | k3_mcart_1(F_44,G_48,H_50) != '#skF_5'
      | ~ m1_subset_1(H_50,'#skF_3')
      | ~ m1_subset_1(G_48,'#skF_2')
      | ~ m1_subset_1(F_44,'#skF_1') ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_386,plain,(
    ! [C_133] :
      ( C_133 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_133) != '#skF_5'
      | ~ m1_subset_1(C_133,'#skF_3')
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2')
      | ~ m1_subset_1(k1_mcart_1(k1_mcart_1('#skF_5')),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_381,c_46])).

tff(c_501,plain,(
    ! [C_133] :
      ( C_133 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_133) != '#skF_5'
      | ~ m1_subset_1(C_133,'#skF_3')
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_386])).

tff(c_502,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_501])).

tff(c_505,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_502])).

tff(c_509,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_505])).

tff(c_511,plain,(
    m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitRight,[status(thm)],[c_501])).

tff(c_377,plain,(
    ! [C_11] : k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5')),C_11) = k4_tarski(k1_mcart_1('#skF_5'),C_11) ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_16])).

tff(c_515,plain,(
    ! [C_149] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k2_mcart_1(k1_mcart_1('#skF_5')),C_149) = k4_tarski(k1_mcart_1('#skF_5'),C_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_480,c_377])).

tff(c_522,plain,(
    ! [C_149] :
      ( C_149 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_149) != '#skF_5'
      | ~ m1_subset_1(C_149,'#skF_3')
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_515,c_46])).

tff(c_529,plain,(
    ! [C_149] :
      ( C_149 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_149) != '#skF_5'
      | ~ m1_subset_1(C_149,'#skF_3')
      | ~ m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_511,c_522])).

tff(c_578,plain,(
    ! [C_149] :
      ( C_149 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_149) != '#skF_5'
      | ~ m1_subset_1(C_149,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_557,c_529])).

tff(c_579,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_578])).

tff(c_582,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_579])).

tff(c_586,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_582])).

tff(c_592,plain,(
    ! [C_154] :
      ( C_154 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_154) != '#skF_5'
      | ~ m1_subset_1(C_154,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_578])).

tff(c_595,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_592])).

tff(c_598,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_425,c_595])).

tff(c_600,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_417,c_598])).

tff(c_601,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_59,plain,(
    ! [A_54] :
      ( k1_relat_1(A_54) = k1_xboole_0
      | ~ v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_55,c_4])).

tff(c_608,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_601,c_59])).

tff(c_628,plain,(
    ! [A_157,B_158,C_159] : k2_zfmisc_1(k2_zfmisc_1(A_157,B_158),C_159) = k3_zfmisc_1(A_157,B_158,C_159) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_636,plain,(
    ! [A_157,B_158,C_159] : v1_relat_1(k3_zfmisc_1(A_157,B_158,C_159)) ),
    inference(superposition,[status(thm),theory(equality)],[c_628,c_10])).

tff(c_721,plain,(
    ! [A_185,B_186] :
      ( k4_tarski(k1_mcart_1(A_185),k2_mcart_1(A_185)) = A_185
      | ~ r2_hidden(A_185,B_186)
      | ~ v1_relat_1(B_186) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_829,plain,(
    ! [A_226,B_227] :
      ( k4_tarski(k1_mcart_1(A_226),k2_mcart_1(A_226)) = A_226
      | ~ v1_relat_1(B_227)
      | v1_xboole_0(B_227)
      | ~ m1_subset_1(A_226,B_227) ) ),
    inference(resolution,[status(thm)],[c_6,c_721])).

tff(c_837,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_1','#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_829])).

tff(c_843,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5'
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_636,c_837])).

tff(c_844,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_852,plain,(
    k3_zfmisc_1('#skF_1','#skF_2','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_844,c_4])).

tff(c_657,plain,(
    ! [A_169,B_170] :
      ( k2_relat_1(k2_zfmisc_1(A_169,B_170)) = B_170
      | k1_xboole_0 = B_170
      | k1_xboole_0 = A_169 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_666,plain,(
    ! [A_12,B_13,C_14] :
      ( k2_relat_1(k3_zfmisc_1(A_12,B_13,C_14)) = C_14
      | k1_xboole_0 = C_14
      | k2_zfmisc_1(A_12,B_13) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_657])).

tff(c_889,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_666])).

tff(c_897,plain,
    ( k2_relat_1(k1_xboole_0) = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_889])).

tff(c_922,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_897])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k1_relat_1(k2_zfmisc_1(A_7,B_8)) = A_7
      | k1_xboole_0 = B_8
      | k1_xboole_0 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_964,plain,
    ( k1_relat_1(k1_xboole_0) = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_14])).

tff(c_985,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_964])).

tff(c_987,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_44,c_985])).

tff(c_989,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_897])).

tff(c_672,plain,(
    ! [A_171,B_172] :
      ( k1_relat_1(k2_zfmisc_1(A_171,B_172)) = A_171
      | k1_xboole_0 = B_172
      | k1_xboole_0 = A_171 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1119,plain,(
    ! [A_249,B_250,C_251] :
      ( k1_relat_1(k3_zfmisc_1(A_249,B_250,C_251)) = k2_zfmisc_1(A_249,B_250)
      | k1_xboole_0 = C_251
      | k2_zfmisc_1(A_249,B_250) = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_672])).

tff(c_1134,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_relat_1(k1_xboole_0)
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_852,c_1119])).

tff(c_1140,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_3'
    | k2_zfmisc_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_1134])).

tff(c_1142,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_989,c_40,c_989,c_1140])).

tff(c_1143,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_1326,plain,(
    ! [A_278,B_279,C_280,D_281] :
      ( k5_mcart_1(A_278,B_279,C_280,D_281) = k1_mcart_1(k1_mcart_1(D_281))
      | ~ m1_subset_1(D_281,k3_zfmisc_1(A_278,B_279,C_280))
      | k1_xboole_0 = C_280
      | k1_xboole_0 = B_279
      | k1_xboole_0 = A_278 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1344,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_1326])).

tff(c_1350,plain,(
    k1_mcart_1(k1_mcart_1('#skF_5')) = k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_1344])).

tff(c_1235,plain,(
    ! [A_263,B_264,C_265,D_266] :
      ( k6_mcart_1(A_263,B_264,C_265,D_266) = k2_mcart_1(k1_mcart_1(D_266))
      | ~ m1_subset_1(D_266,k3_zfmisc_1(A_263,B_264,C_265))
      | k1_xboole_0 = C_265
      | k1_xboole_0 = B_264
      | k1_xboole_0 = A_263 ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_1253,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_1235])).

tff(c_1259,plain,(
    k2_mcart_1(k1_mcart_1('#skF_5')) = k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_42,c_40,c_1253])).

tff(c_1144,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_647,plain,(
    ! [A_166,B_167,C_168] :
      ( r2_hidden(k1_mcart_1(A_166),B_167)
      | ~ r2_hidden(A_166,k2_zfmisc_1(B_167,C_168)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_795,plain,(
    ! [A_220,B_221,C_222] :
      ( r2_hidden(k1_mcart_1(A_220),B_221)
      | v1_xboole_0(k2_zfmisc_1(B_221,C_222))
      | ~ m1_subset_1(A_220,k2_zfmisc_1(B_221,C_222)) ) ),
    inference(resolution,[status(thm)],[c_6,c_647])).

tff(c_806,plain,(
    ! [A_220,A_12,B_13,C_14] :
      ( r2_hidden(k1_mcart_1(A_220),k2_zfmisc_1(A_12,B_13))
      | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_12,B_13),C_14))
      | ~ m1_subset_1(A_220,k3_zfmisc_1(A_12,B_13,C_14)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_795])).

tff(c_1293,plain,(
    ! [A_274,A_275,B_276,C_277] :
      ( r2_hidden(k1_mcart_1(A_274),k2_zfmisc_1(A_275,B_276))
      | v1_xboole_0(k3_zfmisc_1(A_275,B_276,C_277))
      | ~ m1_subset_1(A_274,k3_zfmisc_1(A_275,B_276,C_277)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_806])).

tff(c_1306,plain,
    ( r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2'))
    | v1_xboole_0(k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_48,c_1293])).

tff(c_1313,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_1144,c_1306])).

tff(c_1315,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k2_mcart_1(k1_mcart_1('#skF_5'))) = k1_mcart_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_1313,c_30])).

tff(c_1322,plain,(
    k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_1259,c_1315])).

tff(c_1365,plain,(
    k4_tarski(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5')) = k1_mcart_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_1322])).

tff(c_1378,plain,(
    ! [C_282] : k3_mcart_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),C_282) = k4_tarski(k1_mcart_1('#skF_5'),C_282) ),
    inference(superposition,[status(thm),theory(equality)],[c_1365,c_16])).

tff(c_1385,plain,(
    ! [C_282] :
      ( C_282 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_282) != '#skF_5'
      | ~ m1_subset_1(C_282,'#skF_3')
      | ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1378,c_46])).

tff(c_1410,plain,(
    ~ m1_subset_1(k5_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_1385])).

tff(c_1413,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_1410])).

tff(c_1417,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1413])).

tff(c_1418,plain,(
    ! [C_282] :
      ( ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2')
      | C_282 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_282) != '#skF_5'
      | ~ m1_subset_1(C_282,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1385])).

tff(c_1423,plain,(
    ~ m1_subset_1(k6_mcart_1('#skF_1','#skF_2','#skF_3','#skF_5'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1418])).

tff(c_1426,plain,(
    ~ m1_subset_1('#skF_5',k3_zfmisc_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1423])).

tff(c_1430,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1426])).

tff(c_1455,plain,(
    ! [C_295] :
      ( C_295 = '#skF_4'
      | k4_tarski(k1_mcart_1('#skF_5'),C_295) != '#skF_5'
      | ~ m1_subset_1(C_295,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_1418])).

tff(c_1458,plain,
    ( k2_mcart_1('#skF_5') = '#skF_4'
    | ~ m1_subset_1(k2_mcart_1('#skF_5'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_1455])).

tff(c_1461,plain,(
    k2_mcart_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1203,c_1458])).

tff(c_1463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1195,c_1461])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:37:16 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.64  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.66  
% 3.80/1.66  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.66  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_relat_1 > k2_mcart_1 > k1_relat_1 > k1_mcart_1 > o_0_0_xboole_0 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.80/1.66  
% 3.80/1.66  %Foreground sorts:
% 3.80/1.66  
% 3.80/1.66  
% 3.80/1.66  %Background operators:
% 3.80/1.66  
% 3.80/1.66  
% 3.80/1.66  %Foreground operators:
% 3.80/1.66  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 3.80/1.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.66  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.66  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.80/1.66  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.80/1.66  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 3.80/1.66  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.80/1.66  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.66  tff('#skF_2', type, '#skF_2': $i).
% 3.80/1.66  tff('#skF_3', type, '#skF_3': $i).
% 3.80/1.66  tff('#skF_1', type, '#skF_1': $i).
% 3.80/1.66  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 3.80/1.66  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 3.80/1.66  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 3.80/1.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.66  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 3.80/1.66  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.80/1.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.80/1.66  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.66  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 3.80/1.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.66  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 3.80/1.66  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.80/1.66  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.80/1.66  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.80/1.66  
% 3.80/1.68  tff(f_126, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = H)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k7_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_mcart_1)).
% 3.80/1.68  tff(f_102, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 3.80/1.68  tff(f_70, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 3.80/1.68  tff(f_58, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 3.80/1.68  tff(f_42, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 3.80/1.68  tff(f_40, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc10_relat_1)).
% 3.80/1.68  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.80/1.68  tff(f_36, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.80/1.68  tff(f_82, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 3.80/1.68  tff(f_66, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k6_mcart_1(A, B, C, D), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_mcart_1)).
% 3.80/1.68  tff(f_62, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k5_mcart_1(A, B, C, D), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k5_mcart_1)).
% 3.80/1.68  tff(f_76, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 3.80/1.68  tff(f_56, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 3.80/1.68  tff(f_54, axiom, (![A, B]: ~((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~((k1_relat_1(k2_zfmisc_1(A, B)) = A) & (k2_relat_1(k2_zfmisc_1(A, B)) = B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t195_relat_1)).
% 3.80/1.68  tff(c_44, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.68  tff(c_42, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.68  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.68  tff(c_48, plain, (m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.68  tff(c_1170, plain, (![A_253, B_254, C_255, D_256]: (k7_mcart_1(A_253, B_254, C_255, D_256)=k2_mcart_1(D_256) | ~m1_subset_1(D_256, k3_zfmisc_1(A_253, B_254, C_255)) | k1_xboole_0=C_255 | k1_xboole_0=B_254 | k1_xboole_0=A_253)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.80/1.68  tff(c_1188, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_1170])).
% 3.80/1.68  tff(c_1194, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_1188])).
% 3.80/1.68  tff(c_38, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.68  tff(c_1195, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1194, c_38])).
% 3.80/1.68  tff(c_24, plain, (![A_23, B_24, C_25, D_26]: (m1_subset_1(k7_mcart_1(A_23, B_24, C_25, D_26), C_25) | ~m1_subset_1(D_26, k3_zfmisc_1(A_23, B_24, C_25)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.80/1.68  tff(c_1199, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1194, c_24])).
% 3.80/1.68  tff(c_1203, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1199])).
% 3.80/1.68  tff(c_392, plain, (![A_134, B_135, C_136, D_137]: (k7_mcart_1(A_134, B_135, C_136, D_137)=k2_mcart_1(D_137) | ~m1_subset_1(D_137, k3_zfmisc_1(A_134, B_135, C_136)) | k1_xboole_0=C_136 | k1_xboole_0=B_135 | k1_xboole_0=A_134)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.80/1.68  tff(c_410, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_392])).
% 3.80/1.68  tff(c_416, plain, (k7_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')=k2_mcart_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_410])).
% 3.80/1.68  tff(c_417, plain, (k2_mcart_1('#skF_5')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_416, c_38])).
% 3.80/1.68  tff(c_421, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3') | ~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_416, c_24])).
% 3.80/1.68  tff(c_425, plain, (m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_421])).
% 3.80/1.68  tff(c_96, plain, (![A_61, B_62, C_63]: (k2_zfmisc_1(k2_zfmisc_1(A_61, B_62), C_63)=k3_zfmisc_1(A_61, B_62, C_63))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.68  tff(c_10, plain, (![A_5, B_6]: (v1_relat_1(k2_zfmisc_1(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 3.80/1.68  tff(c_104, plain, (![A_61, B_62, C_63]: (v1_relat_1(k3_zfmisc_1(A_61, B_62, C_63)))), inference(superposition, [status(thm), theory('equality')], [c_96, c_10])).
% 3.80/1.68  tff(c_8, plain, (![A_4]: (v1_xboole_0(k1_relat_1(A_4)) | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.80/1.68  tff(c_55, plain, (![A_54]: (v1_xboole_0(k1_relat_1(A_54)) | ~v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.80/1.68  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.80/1.68  tff(c_60, plain, (![A_55]: (k1_relat_1(A_55)=k1_xboole_0 | ~v1_xboole_0(A_55))), inference(resolution, [status(thm)], [c_55, c_4])).
% 3.80/1.68  tff(c_65, plain, (![A_56]: (k1_relat_1(k1_relat_1(A_56))=k1_xboole_0 | ~v1_xboole_0(A_56))), inference(resolution, [status(thm)], [c_8, c_60])).
% 3.80/1.68  tff(c_74, plain, (![A_56]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(k1_relat_1(A_56)) | ~v1_xboole_0(A_56))), inference(superposition, [status(thm), theory('equality')], [c_65, c_8])).
% 3.80/1.68  tff(c_84, plain, (![A_57]: (~v1_xboole_0(k1_relat_1(A_57)) | ~v1_xboole_0(A_57))), inference(splitLeft, [status(thm)], [c_74])).
% 3.80/1.68  tff(c_91, plain, (![A_4]: (~v1_xboole_0(A_4))), inference(resolution, [status(thm)], [c_8, c_84])).
% 3.80/1.68  tff(c_6, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | v1_xboole_0(B_3) | ~m1_subset_1(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.80/1.68  tff(c_94, plain, (![A_2, B_3]: (r2_hidden(A_2, B_3) | ~m1_subset_1(A_2, B_3))), inference(negUnitSimplification, [status(thm)], [c_91, c_6])).
% 3.80/1.68  tff(c_174, plain, (![A_83, B_84]: (k4_tarski(k1_mcart_1(A_83), k2_mcart_1(A_83))=A_83 | ~r2_hidden(A_83, B_84) | ~v1_relat_1(B_84))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.80/1.68  tff(c_209, plain, (![A_103, B_104]: (k4_tarski(k1_mcart_1(A_103), k2_mcart_1(A_103))=A_103 | ~v1_relat_1(B_104) | ~m1_subset_1(A_103, B_104))), inference(resolution, [status(thm)], [c_94, c_174])).
% 3.80/1.68  tff(c_213, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_209])).
% 3.80/1.68  tff(c_217, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_104, c_213])).
% 3.80/1.68  tff(c_22, plain, (![A_19, B_20, C_21, D_22]: (m1_subset_1(k6_mcart_1(A_19, B_20, C_21, D_22), B_20) | ~m1_subset_1(D_22, k3_zfmisc_1(A_19, B_20, C_21)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.80/1.68  tff(c_533, plain, (![A_150, B_151, C_152, D_153]: (k6_mcart_1(A_150, B_151, C_152, D_153)=k2_mcart_1(k1_mcart_1(D_153)) | ~m1_subset_1(D_153, k3_zfmisc_1(A_150, B_151, C_152)) | k1_xboole_0=C_152 | k1_xboole_0=B_151 | k1_xboole_0=A_150)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.80/1.68  tff(c_551, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_533])).
% 3.80/1.68  tff(c_557, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_551])).
% 3.80/1.68  tff(c_20, plain, (![A_15, B_16, C_17, D_18]: (m1_subset_1(k5_mcart_1(A_15, B_16, C_17, D_18), A_15) | ~m1_subset_1(D_18, k3_zfmisc_1(A_15, B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.80/1.68  tff(c_456, plain, (![A_145, B_146, C_147, D_148]: (k5_mcart_1(A_145, B_146, C_147, D_148)=k1_mcart_1(k1_mcart_1(D_148)) | ~m1_subset_1(D_148, k3_zfmisc_1(A_145, B_146, C_147)) | k1_xboole_0=C_147 | k1_xboole_0=B_146 | k1_xboole_0=A_145)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.80/1.68  tff(c_474, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_456])).
% 3.80/1.68  tff(c_480, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_474])).
% 3.80/1.68  tff(c_18, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)=k3_zfmisc_1(A_12, B_13, C_14))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.68  tff(c_167, plain, (![A_80, B_81, C_82]: (r2_hidden(k1_mcart_1(A_80), B_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_81, C_82)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.68  tff(c_285, plain, (![A_117, A_118, B_119, C_120]: (r2_hidden(k1_mcart_1(A_117), k2_zfmisc_1(A_118, B_119)) | ~r2_hidden(A_117, k3_zfmisc_1(A_118, B_119, C_120)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_167])).
% 3.80/1.68  tff(c_335, plain, (![A_129, A_130, B_131, C_132]: (r2_hidden(k1_mcart_1(A_129), k2_zfmisc_1(A_130, B_131)) | ~m1_subset_1(A_129, k3_zfmisc_1(A_130, B_131, C_132)))), inference(resolution, [status(thm)], [c_94, c_285])).
% 3.80/1.68  tff(c_353, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_48, c_335])).
% 3.80/1.68  tff(c_30, plain, (![A_30, B_31]: (k4_tarski(k1_mcart_1(A_30), k2_mcart_1(A_30))=A_30 | ~r2_hidden(A_30, B_31) | ~v1_relat_1(B_31))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.80/1.68  tff(c_355, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_353, c_30])).
% 3.80/1.68  tff(c_362, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_355])).
% 3.80/1.68  tff(c_16, plain, (![A_9, B_10, C_11]: (k4_tarski(k4_tarski(A_9, B_10), C_11)=k3_mcart_1(A_9, B_10, C_11))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.80/1.68  tff(c_381, plain, (![C_133]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')), C_133)=k4_tarski(k1_mcart_1('#skF_5'), C_133))), inference(superposition, [status(thm), theory('equality')], [c_362, c_16])).
% 3.80/1.68  tff(c_46, plain, (![H_50, F_44, G_48]: (H_50='#skF_4' | k3_mcart_1(F_44, G_48, H_50)!='#skF_5' | ~m1_subset_1(H_50, '#skF_3') | ~m1_subset_1(G_48, '#skF_2') | ~m1_subset_1(F_44, '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_126])).
% 3.80/1.68  tff(c_386, plain, (![C_133]: (C_133='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_133)!='#skF_5' | ~m1_subset_1(C_133, '#skF_3') | ~m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2') | ~m1_subset_1(k1_mcart_1(k1_mcart_1('#skF_5')), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_381, c_46])).
% 3.80/1.68  tff(c_501, plain, (![C_133]: (C_133='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_133)!='#skF_5' | ~m1_subset_1(C_133, '#skF_3') | ~m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_386])).
% 3.80/1.68  tff(c_502, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_501])).
% 3.80/1.68  tff(c_505, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_502])).
% 3.80/1.68  tff(c_509, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_505])).
% 3.80/1.68  tff(c_511, plain, (m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitRight, [status(thm)], [c_501])).
% 3.80/1.68  tff(c_377, plain, (![C_11]: (k3_mcart_1(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')), C_11)=k4_tarski(k1_mcart_1('#skF_5'), C_11))), inference(superposition, [status(thm), theory('equality')], [c_362, c_16])).
% 3.80/1.68  tff(c_515, plain, (![C_149]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k2_mcart_1(k1_mcart_1('#skF_5')), C_149)=k4_tarski(k1_mcart_1('#skF_5'), C_149))), inference(demodulation, [status(thm), theory('equality')], [c_480, c_377])).
% 3.80/1.68  tff(c_522, plain, (![C_149]: (C_149='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_149)!='#skF_5' | ~m1_subset_1(C_149, '#skF_3') | ~m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_515, c_46])).
% 3.80/1.68  tff(c_529, plain, (![C_149]: (C_149='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_149)!='#skF_5' | ~m1_subset_1(C_149, '#skF_3') | ~m1_subset_1(k2_mcart_1(k1_mcart_1('#skF_5')), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_511, c_522])).
% 3.80/1.68  tff(c_578, plain, (![C_149]: (C_149='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_149)!='#skF_5' | ~m1_subset_1(C_149, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_557, c_529])).
% 3.80/1.68  tff(c_579, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_578])).
% 3.80/1.68  tff(c_582, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_579])).
% 3.80/1.68  tff(c_586, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_582])).
% 3.80/1.68  tff(c_592, plain, (![C_154]: (C_154='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_154)!='#skF_5' | ~m1_subset_1(C_154, '#skF_3'))), inference(splitRight, [status(thm)], [c_578])).
% 3.80/1.68  tff(c_595, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_217, c_592])).
% 3.80/1.68  tff(c_598, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_425, c_595])).
% 3.80/1.68  tff(c_600, plain, $false, inference(negUnitSimplification, [status(thm)], [c_417, c_598])).
% 3.80/1.68  tff(c_601, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_74])).
% 3.80/1.68  tff(c_59, plain, (![A_54]: (k1_relat_1(A_54)=k1_xboole_0 | ~v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_55, c_4])).
% 3.80/1.68  tff(c_608, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_601, c_59])).
% 3.80/1.68  tff(c_628, plain, (![A_157, B_158, C_159]: (k2_zfmisc_1(k2_zfmisc_1(A_157, B_158), C_159)=k3_zfmisc_1(A_157, B_158, C_159))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.80/1.68  tff(c_636, plain, (![A_157, B_158, C_159]: (v1_relat_1(k3_zfmisc_1(A_157, B_158, C_159)))), inference(superposition, [status(thm), theory('equality')], [c_628, c_10])).
% 3.80/1.68  tff(c_721, plain, (![A_185, B_186]: (k4_tarski(k1_mcart_1(A_185), k2_mcart_1(A_185))=A_185 | ~r2_hidden(A_185, B_186) | ~v1_relat_1(B_186))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.80/1.68  tff(c_829, plain, (![A_226, B_227]: (k4_tarski(k1_mcart_1(A_226), k2_mcart_1(A_226))=A_226 | ~v1_relat_1(B_227) | v1_xboole_0(B_227) | ~m1_subset_1(A_226, B_227))), inference(resolution, [status(thm)], [c_6, c_721])).
% 3.80/1.68  tff(c_837, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | ~v1_relat_1(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_829])).
% 3.80/1.68  tff(c_843, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5' | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_636, c_837])).
% 3.80/1.68  tff(c_844, plain, (v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_843])).
% 3.80/1.68  tff(c_852, plain, (k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_844, c_4])).
% 3.80/1.68  tff(c_657, plain, (![A_169, B_170]: (k2_relat_1(k2_zfmisc_1(A_169, B_170))=B_170 | k1_xboole_0=B_170 | k1_xboole_0=A_169)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.80/1.68  tff(c_666, plain, (![A_12, B_13, C_14]: (k2_relat_1(k3_zfmisc_1(A_12, B_13, C_14))=C_14 | k1_xboole_0=C_14 | k2_zfmisc_1(A_12, B_13)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_657])).
% 3.80/1.68  tff(c_889, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_852, c_666])).
% 3.80/1.68  tff(c_897, plain, (k2_relat_1(k1_xboole_0)='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_889])).
% 3.80/1.68  tff(c_922, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_897])).
% 3.80/1.68  tff(c_14, plain, (![A_7, B_8]: (k1_relat_1(k2_zfmisc_1(A_7, B_8))=A_7 | k1_xboole_0=B_8 | k1_xboole_0=A_7)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.80/1.68  tff(c_964, plain, (k1_relat_1(k1_xboole_0)='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_922, c_14])).
% 3.80/1.68  tff(c_985, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_608, c_964])).
% 3.80/1.68  tff(c_987, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_44, c_985])).
% 3.80/1.68  tff(c_989, plain, (k2_zfmisc_1('#skF_1', '#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_897])).
% 3.80/1.68  tff(c_672, plain, (![A_171, B_172]: (k1_relat_1(k2_zfmisc_1(A_171, B_172))=A_171 | k1_xboole_0=B_172 | k1_xboole_0=A_171)), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.80/1.68  tff(c_1119, plain, (![A_249, B_250, C_251]: (k1_relat_1(k3_zfmisc_1(A_249, B_250, C_251))=k2_zfmisc_1(A_249, B_250) | k1_xboole_0=C_251 | k2_zfmisc_1(A_249, B_250)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_18, c_672])).
% 3.80/1.68  tff(c_1134, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_relat_1(k1_xboole_0) | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_852, c_1119])).
% 3.80/1.68  tff(c_1140, plain, (k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_3' | k2_zfmisc_1('#skF_1', '#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_608, c_1134])).
% 3.80/1.68  tff(c_1142, plain, $false, inference(negUnitSimplification, [status(thm)], [c_989, c_40, c_989, c_1140])).
% 3.80/1.68  tff(c_1143, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(splitRight, [status(thm)], [c_843])).
% 3.80/1.68  tff(c_1326, plain, (![A_278, B_279, C_280, D_281]: (k5_mcart_1(A_278, B_279, C_280, D_281)=k1_mcart_1(k1_mcart_1(D_281)) | ~m1_subset_1(D_281, k3_zfmisc_1(A_278, B_279, C_280)) | k1_xboole_0=C_280 | k1_xboole_0=B_279 | k1_xboole_0=A_278)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.80/1.68  tff(c_1344, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_1326])).
% 3.80/1.68  tff(c_1350, plain, (k1_mcart_1(k1_mcart_1('#skF_5'))=k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_1344])).
% 3.80/1.68  tff(c_1235, plain, (![A_263, B_264, C_265, D_266]: (k6_mcart_1(A_263, B_264, C_265, D_266)=k2_mcart_1(k1_mcart_1(D_266)) | ~m1_subset_1(D_266, k3_zfmisc_1(A_263, B_264, C_265)) | k1_xboole_0=C_265 | k1_xboole_0=B_264 | k1_xboole_0=A_263)), inference(cnfTransformation, [status(thm)], [f_102])).
% 3.80/1.68  tff(c_1253, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5') | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_1235])).
% 3.80/1.68  tff(c_1259, plain, (k2_mcart_1(k1_mcart_1('#skF_5'))=k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5')), inference(negUnitSimplification, [status(thm)], [c_44, c_42, c_40, c_1253])).
% 3.80/1.68  tff(c_1144, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitRight, [status(thm)], [c_843])).
% 3.80/1.68  tff(c_647, plain, (![A_166, B_167, C_168]: (r2_hidden(k1_mcart_1(A_166), B_167) | ~r2_hidden(A_166, k2_zfmisc_1(B_167, C_168)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.80/1.68  tff(c_795, plain, (![A_220, B_221, C_222]: (r2_hidden(k1_mcart_1(A_220), B_221) | v1_xboole_0(k2_zfmisc_1(B_221, C_222)) | ~m1_subset_1(A_220, k2_zfmisc_1(B_221, C_222)))), inference(resolution, [status(thm)], [c_6, c_647])).
% 4.05/1.68  tff(c_806, plain, (![A_220, A_12, B_13, C_14]: (r2_hidden(k1_mcart_1(A_220), k2_zfmisc_1(A_12, B_13)) | v1_xboole_0(k2_zfmisc_1(k2_zfmisc_1(A_12, B_13), C_14)) | ~m1_subset_1(A_220, k3_zfmisc_1(A_12, B_13, C_14)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_795])).
% 4.05/1.68  tff(c_1293, plain, (![A_274, A_275, B_276, C_277]: (r2_hidden(k1_mcart_1(A_274), k2_zfmisc_1(A_275, B_276)) | v1_xboole_0(k3_zfmisc_1(A_275, B_276, C_277)) | ~m1_subset_1(A_274, k3_zfmisc_1(A_275, B_276, C_277)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_806])).
% 4.05/1.68  tff(c_1306, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2')) | v1_xboole_0(k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_48, c_1293])).
% 4.05/1.68  tff(c_1313, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_zfmisc_1('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_1144, c_1306])).
% 4.05/1.68  tff(c_1315, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k2_mcart_1(k1_mcart_1('#skF_5')))=k1_mcart_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_1313, c_30])).
% 4.05/1.68  tff(c_1322, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_5')), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_1259, c_1315])).
% 4.05/1.68  tff(c_1365, plain, (k4_tarski(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'))=k1_mcart_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_1322])).
% 4.05/1.68  tff(c_1378, plain, (![C_282]: (k3_mcart_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), C_282)=k4_tarski(k1_mcart_1('#skF_5'), C_282))), inference(superposition, [status(thm), theory('equality')], [c_1365, c_16])).
% 4.05/1.68  tff(c_1385, plain, (![C_282]: (C_282='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_282)!='#skF_5' | ~m1_subset_1(C_282, '#skF_3') | ~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | ~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1378, c_46])).
% 4.05/1.68  tff(c_1410, plain, (~m1_subset_1(k5_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_1')), inference(splitLeft, [status(thm)], [c_1385])).
% 4.05/1.68  tff(c_1413, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_20, c_1410])).
% 4.05/1.68  tff(c_1417, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1413])).
% 4.05/1.68  tff(c_1418, plain, (![C_282]: (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2') | C_282='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_282)!='#skF_5' | ~m1_subset_1(C_282, '#skF_3'))), inference(splitRight, [status(thm)], [c_1385])).
% 4.05/1.68  tff(c_1423, plain, (~m1_subset_1(k6_mcart_1('#skF_1', '#skF_2', '#skF_3', '#skF_5'), '#skF_2')), inference(splitLeft, [status(thm)], [c_1418])).
% 4.05/1.68  tff(c_1426, plain, (~m1_subset_1('#skF_5', k3_zfmisc_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1423])).
% 4.05/1.68  tff(c_1430, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1426])).
% 4.05/1.68  tff(c_1455, plain, (![C_295]: (C_295='#skF_4' | k4_tarski(k1_mcart_1('#skF_5'), C_295)!='#skF_5' | ~m1_subset_1(C_295, '#skF_3'))), inference(splitRight, [status(thm)], [c_1418])).
% 4.05/1.68  tff(c_1458, plain, (k2_mcart_1('#skF_5')='#skF_4' | ~m1_subset_1(k2_mcart_1('#skF_5'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1143, c_1455])).
% 4.05/1.68  tff(c_1461, plain, (k2_mcart_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1203, c_1458])).
% 4.05/1.68  tff(c_1463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1195, c_1461])).
% 4.05/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.05/1.68  
% 4.05/1.68  Inference rules
% 4.05/1.68  ----------------------
% 4.05/1.68  #Ref     : 0
% 4.05/1.68  #Sup     : 348
% 4.05/1.68  #Fact    : 0
% 4.05/1.68  #Define  : 0
% 4.05/1.68  #Split   : 16
% 4.05/1.68  #Chain   : 0
% 4.05/1.68  #Close   : 0
% 4.05/1.68  
% 4.05/1.68  Ordering : KBO
% 4.05/1.68  
% 4.05/1.68  Simplification rules
% 4.05/1.68  ----------------------
% 4.05/1.68  #Subsume      : 43
% 4.05/1.68  #Demod        : 119
% 4.05/1.68  #Tautology    : 111
% 4.05/1.68  #SimpNegUnit  : 21
% 4.05/1.68  #BackRed      : 12
% 4.05/1.68  
% 4.05/1.68  #Partial instantiations: 0
% 4.05/1.68  #Strategies tried      : 1
% 4.05/1.68  
% 4.05/1.68  Timing (in seconds)
% 4.05/1.68  ----------------------
% 4.05/1.69  Preprocessing        : 0.32
% 4.05/1.69  Parsing              : 0.17
% 4.05/1.69  CNF conversion       : 0.02
% 4.05/1.69  Main loop            : 0.56
% 4.05/1.69  Inferencing          : 0.22
% 4.05/1.69  Reduction            : 0.16
% 4.05/1.69  Demodulation         : 0.10
% 4.05/1.69  BG Simplification    : 0.03
% 4.05/1.69  Subsumption          : 0.10
% 4.05/1.69  Abstraction          : 0.04
% 4.05/1.69  MUC search           : 0.00
% 4.05/1.69  Cooper               : 0.00
% 4.05/1.69  Total                : 0.94
% 4.05/1.69  Index Insertion      : 0.00
% 4.05/1.69  Index Deletion       : 0.00
% 4.05/1.69  Index Matching       : 0.00
% 4.05/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------
