%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:57 EST 2020

% Result     : Theorem 14.64s
% Output     : CNFRefutation 14.94s
% Verified   : 
% Statistics : Number of formulae       :  121 ( 366 expanded)
%              Number of leaves         :   36 ( 139 expanded)
%              Depth                    :   13
%              Number of atoms          :  213 (1122 expanded)
%              Number of equality atoms :   90 ( 446 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4

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

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D,E] :
        ( m1_subset_1(E,k3_zfmisc_1(A,B,C))
       => ( ! [F] :
              ( m1_subset_1(F,A)
             => ! [G] :
                  ( m1_subset_1(G,B)
                 => ! [H] :
                      ( m1_subset_1(H,C)
                     => ( E = k3_mcart_1(F,G,H)
                       => D = F ) ) ) )
         => ( A = k1_xboole_0
            | B = k1_xboole_0
            | C = k1_xboole_0
            | D = k5_mcart_1(A,B,C,E) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_mcart_1)).

tff(f_107,axiom,(
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

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k3_zfmisc_1(A,B,C))
     => m1_subset_1(k7_mcart_1(A,B,C,D),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_mcart_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k3_zfmisc_1(A,B,C) = k2_zfmisc_1(k2_zfmisc_1(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r2_hidden(A,B)
       => A = k4_tarski(k1_mcart_1(A),k2_mcart_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_mcart_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_mcart_1(A,B,C) = k4_tarski(k4_tarski(A,B),C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_mcart_1)).

tff(f_32,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( A != k1_xboole_0
        & B != k1_xboole_0
        & C != k1_xboole_0 )
    <=> k3_zfmisc_1(A,B,C) != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_mcart_1)).

tff(c_56,plain,(
    m1_subset_1('#skF_6',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_48,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_433,plain,(
    ! [A_114,B_115,C_116,D_117] :
      ( k7_mcart_1(A_114,B_115,C_116,D_117) = k2_mcart_1(D_117)
      | ~ m1_subset_1(D_117,k3_zfmisc_1(A_114,B_115,C_116))
      | k1_xboole_0 = C_116
      | k1_xboole_0 = B_115
      | k1_xboole_0 = A_114 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_448,plain,
    ( k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_433])).

tff(c_463,plain,(
    k7_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = k2_mcart_1('#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_448])).

tff(c_24,plain,(
    ! [A_17,B_18,C_19,D_20] :
      ( m1_subset_1(k7_mcart_1(A_17,B_18,C_19,D_20),C_19)
      | ~ m1_subset_1(D_20,k3_zfmisc_1(A_17,B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_471,plain,
    ( m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4')
    | ~ m1_subset_1('#skF_6',k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_463,c_24])).

tff(c_475,plain,(
    m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_471])).

tff(c_119,plain,(
    ! [B_62,A_63] :
      ( v1_xboole_0(B_62)
      | ~ m1_subset_1(B_62,A_63)
      | ~ v1_xboole_0(A_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_123,plain,
    ( v1_xboole_0('#skF_6')
    | ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_119])).

tff(c_129,plain,(
    ~ v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_123])).

tff(c_150,plain,(
    ! [A_74,B_75,C_76] : k2_zfmisc_1(k2_zfmisc_1(A_74,B_75),C_76) = k3_zfmisc_1(A_74,B_75,C_76) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_18,plain,(
    ! [A_9,B_10] : v1_relat_1(k2_zfmisc_1(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_158,plain,(
    ! [A_74,B_75,C_76] : v1_relat_1(k3_zfmisc_1(A_74,B_75,C_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_18])).

tff(c_12,plain,(
    ! [B_8,A_7] :
      ( r2_hidden(B_8,A_7)
      | ~ m1_subset_1(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_263,plain,(
    ! [A_96,B_97] :
      ( k4_tarski(k1_mcart_1(A_96),k2_mcart_1(A_96)) = A_96
      | ~ r2_hidden(A_96,B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3601,plain,(
    ! [B_276,A_277] :
      ( k4_tarski(k1_mcart_1(B_276),k2_mcart_1(B_276)) = B_276
      | ~ v1_relat_1(A_277)
      | ~ m1_subset_1(B_276,A_277)
      | v1_xboole_0(A_277) ) ),
    inference(resolution,[status(thm)],[c_12,c_263])).

tff(c_3611,plain,
    ( k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | ~ v1_relat_1(k3_zfmisc_1('#skF_2','#skF_3','#skF_4'))
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_3601])).

tff(c_3620,plain,
    ( k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6'
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_158,c_3611])).

tff(c_3621,plain,(
    k4_tarski(k1_mcart_1('#skF_6'),k2_mcart_1('#skF_6')) = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_3620])).

tff(c_46,plain,(
    k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4,plain,(
    ! [A_1] :
      ( v1_xboole_0(A_1)
      | r2_hidden('#skF_1'(A_1),A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_202,plain,(
    ! [A_86,B_87,C_88] :
      ( r2_hidden(k1_mcart_1(A_86),B_87)
      | ~ r2_hidden(A_86,k2_zfmisc_1(B_87,C_88)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_740,plain,(
    ! [B_146,C_147] :
      ( r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_146,C_147))),B_146)
      | v1_xboole_0(k2_zfmisc_1(B_146,C_147)) ) ),
    inference(resolution,[status(thm)],[c_4,c_202])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_786,plain,(
    ! [B_146,C_147] :
      ( ~ v1_xboole_0(B_146)
      | v1_xboole_0(k2_zfmisc_1(B_146,C_147)) ) ),
    inference(resolution,[status(thm)],[c_740,c_2])).

tff(c_22,plain,(
    ! [A_14,B_15,C_16] : k2_zfmisc_1(k2_zfmisc_1(A_14,B_15),C_16) = k3_zfmisc_1(A_14,B_15,C_16) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_791,plain,(
    ! [B_148,C_149] :
      ( ~ v1_xboole_0(B_148)
      | v1_xboole_0(k2_zfmisc_1(B_148,C_149)) ) ),
    inference(resolution,[status(thm)],[c_740,c_2])).

tff(c_978,plain,(
    ! [A_164,B_165,C_166] :
      ( ~ v1_xboole_0(k2_zfmisc_1(A_164,B_165))
      | v1_xboole_0(k3_zfmisc_1(A_164,B_165,C_166)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_791])).

tff(c_1020,plain,(
    ~ v1_xboole_0(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_978,c_129])).

tff(c_1034,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_786,c_1020])).

tff(c_482,plain,(
    ! [A_118,B_119,C_120,D_121] :
      ( k5_mcart_1(A_118,B_119,C_120,D_121) = k1_mcart_1(k1_mcart_1(D_121))
      | ~ m1_subset_1(D_121,k3_zfmisc_1(A_118,B_119,C_120))
      | k1_xboole_0 = C_120
      | k1_xboole_0 = B_119
      | k1_xboole_0 = A_118 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_497,plain,
    ( k1_mcart_1(k1_mcart_1('#skF_6')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_482])).

tff(c_512,plain,(
    k1_mcart_1(k1_mcart_1('#skF_6')) = k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_497])).

tff(c_1979,plain,(
    ! [A_210,A_211,B_212,C_213] :
      ( r2_hidden(k1_mcart_1(A_210),k2_zfmisc_1(A_211,B_212))
      | ~ r2_hidden(A_210,k3_zfmisc_1(A_211,B_212,C_213)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_202])).

tff(c_49357,plain,(
    ! [B_1105,A_1106,B_1107,C_1108] :
      ( r2_hidden(k1_mcart_1(B_1105),k2_zfmisc_1(A_1106,B_1107))
      | ~ m1_subset_1(B_1105,k3_zfmisc_1(A_1106,B_1107,C_1108))
      | v1_xboole_0(k3_zfmisc_1(A_1106,B_1107,C_1108)) ) ),
    inference(resolution,[status(thm)],[c_12,c_1979])).

tff(c_49432,plain,
    ( r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3'))
    | v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_56,c_49357])).

tff(c_49448,plain,(
    r2_hidden(k1_mcart_1('#skF_6'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_49432])).

tff(c_28,plain,(
    ! [A_21,B_22,C_23] :
      ( r2_hidden(k1_mcart_1(A_21),B_22)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_49457,plain,(
    r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')),'#skF_2') ),
    inference(resolution,[status(thm)],[c_49448,c_28])).

tff(c_49470,plain,(
    r2_hidden(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_512,c_49457])).

tff(c_10,plain,(
    ! [B_8,A_7] :
      ( m1_subset_1(B_8,A_7)
      | ~ r2_hidden(B_8,A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_49501,plain,
    ( m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_49470,c_10])).

tff(c_49508,plain,(
    m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_1034,c_49501])).

tff(c_174,plain,(
    ! [A_80,C_81,B_82] :
      ( r2_hidden(k2_mcart_1(A_80),C_81)
      | ~ r2_hidden(A_80,k2_zfmisc_1(B_82,C_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_287,plain,(
    ! [B_101,C_102] :
      ( r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_101,C_102))),C_102)
      | v1_xboole_0(k2_zfmisc_1(B_101,C_102)) ) ),
    inference(resolution,[status(thm)],[c_4,c_174])).

tff(c_318,plain,(
    ! [C_102,B_101] :
      ( ~ v1_xboole_0(C_102)
      | v1_xboole_0(k2_zfmisc_1(B_101,C_102)) ) ),
    inference(resolution,[status(thm)],[c_287,c_2])).

tff(c_1035,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_318,c_1020])).

tff(c_559,plain,(
    ! [A_128,B_129,C_130,D_131] :
      ( k6_mcart_1(A_128,B_129,C_130,D_131) = k2_mcart_1(k1_mcart_1(D_131))
      | ~ m1_subset_1(D_131,k3_zfmisc_1(A_128,B_129,C_130))
      | k1_xboole_0 = C_130
      | k1_xboole_0 = B_129
      | k1_xboole_0 = A_128 ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_574,plain,
    ( k2_mcart_1(k1_mcart_1('#skF_6')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')
    | k1_xboole_0 = '#skF_4'
    | k1_xboole_0 = '#skF_3'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_56,c_559])).

tff(c_589,plain,(
    k2_mcart_1(k1_mcart_1('#skF_6')) = k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_50,c_48,c_574])).

tff(c_26,plain,(
    ! [A_21,C_23,B_22] :
      ( r2_hidden(k2_mcart_1(A_21),C_23)
      | ~ r2_hidden(A_21,k2_zfmisc_1(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_49459,plain,(
    r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_49448,c_26])).

tff(c_49472,plain,(
    r2_hidden(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_589,c_49459])).

tff(c_49514,plain,
    ( m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_49472,c_10])).

tff(c_49521,plain,(
    m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_1035,c_49514])).

tff(c_30,plain,(
    ! [A_24,B_25] :
      ( k4_tarski(k1_mcart_1(A_24),k2_mcart_1(A_24)) = A_24
      | ~ r2_hidden(A_24,B_25)
      | ~ v1_relat_1(B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_49455,plain,
    ( k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')),k2_mcart_1(k1_mcart_1('#skF_6'))) = k1_mcart_1('#skF_6')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_49448,c_30])).

tff(c_49468,plain,(
    k4_tarski(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6')) = k1_mcart_1('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_512,c_589,c_49455])).

tff(c_20,plain,(
    ! [A_11,B_12,C_13] : k4_tarski(k4_tarski(A_11,B_12),C_13) = k3_mcart_1(A_11,B_12,C_13) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_57726,plain,(
    ! [C_1170] : k3_mcart_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),C_1170) = k4_tarski(k1_mcart_1('#skF_6'),C_1170) ),
    inference(superposition,[status(thm),theory(equality)],[c_49468,c_20])).

tff(c_54,plain,(
    ! [F_41,G_45,H_47] :
      ( F_41 = '#skF_5'
      | k3_mcart_1(F_41,G_45,H_47) != '#skF_6'
      | ~ m1_subset_1(H_47,'#skF_4')
      | ~ m1_subset_1(G_45,'#skF_3')
      | ~ m1_subset_1(F_41,'#skF_2') ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_57733,plain,(
    ! [C_1170] :
      ( k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5'
      | k4_tarski(k1_mcart_1('#skF_6'),C_1170) != '#skF_6'
      | ~ m1_subset_1(C_1170,'#skF_4')
      | ~ m1_subset_1(k6_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_3')
      | ~ m1_subset_1(k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6'),'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57726,c_54])).

tff(c_57740,plain,(
    ! [C_1170] :
      ( k5_mcart_1('#skF_2','#skF_3','#skF_4','#skF_6') = '#skF_5'
      | k4_tarski(k1_mcart_1('#skF_6'),C_1170) != '#skF_6'
      | ~ m1_subset_1(C_1170,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_49508,c_49521,c_57733])).

tff(c_57743,plain,(
    ! [C_1171] :
      ( k4_tarski(k1_mcart_1('#skF_6'),C_1171) != '#skF_6'
      | ~ m1_subset_1(C_1171,'#skF_4') ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_57740])).

tff(c_57746,plain,(
    ~ m1_subset_1(k2_mcart_1('#skF_6'),'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3621,c_57743])).

tff(c_57750,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_475,c_57746])).

tff(c_57751,plain,(
    v1_xboole_0('#skF_6') ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_6,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_104,plain,(
    ! [B_58,A_59] :
      ( ~ v1_xboole_0(B_58)
      | B_58 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_107,plain,(
    ! [A_59] :
      ( k1_xboole_0 = A_59
      | ~ v1_xboole_0(A_59) ) ),
    inference(resolution,[status(thm)],[c_6,c_104])).

tff(c_57758,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(resolution,[status(thm)],[c_57751,c_107])).

tff(c_57767,plain,(
    '#skF_6' != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57758,c_52])).

tff(c_57766,plain,(
    '#skF_6' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57758,c_50])).

tff(c_57765,plain,(
    '#skF_6' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_57758,c_48])).

tff(c_57752,plain,(
    v1_xboole_0(k3_zfmisc_1('#skF_2','#skF_3','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_123])).

tff(c_8,plain,(
    ! [B_6,A_5] :
      ( ~ v1_xboole_0(B_6)
      | B_6 = A_5
      | ~ v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57759,plain,(
    ! [A_5] :
      ( A_5 = '#skF_6'
      | ~ v1_xboole_0(A_5) ) ),
    inference(resolution,[status(thm)],[c_57751,c_8])).

tff(c_57790,plain,(
    k3_zfmisc_1('#skF_2','#skF_3','#skF_4') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_57752,c_57759])).

tff(c_32,plain,(
    ! [A_26,B_27,C_28] :
      ( k3_zfmisc_1(A_26,B_27,C_28) != k1_xboole_0
      | k1_xboole_0 = C_28
      | k1_xboole_0 = B_27
      | k1_xboole_0 = A_26 ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_57993,plain,(
    ! [A_1211,B_1212,C_1213] :
      ( k3_zfmisc_1(A_1211,B_1212,C_1213) != '#skF_6'
      | C_1213 = '#skF_6'
      | B_1212 = '#skF_6'
      | A_1211 = '#skF_6' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_57758,c_57758,c_57758,c_57758,c_32])).

tff(c_57996,plain,
    ( '#skF_6' = '#skF_4'
    | '#skF_6' = '#skF_3'
    | '#skF_6' = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_57790,c_57993])).

tff(c_58009,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57767,c_57766,c_57765,c_57996])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:10:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.64/7.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.64/7.46  
% 14.64/7.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.87/7.46  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > v1_relat_1 > k7_mcart_1 > k6_mcart_1 > k5_mcart_1 > k3_zfmisc_1 > k3_mcart_1 > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_mcart_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_4
% 14.87/7.46  
% 14.87/7.46  %Foreground sorts:
% 14.87/7.46  
% 14.87/7.46  
% 14.87/7.46  %Background operators:
% 14.87/7.46  
% 14.87/7.46  
% 14.87/7.46  %Foreground operators:
% 14.87/7.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.87/7.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.87/7.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 14.87/7.46  tff('#skF_1', type, '#skF_1': $i > $i).
% 14.87/7.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.87/7.46  tff(k3_mcart_1, type, k3_mcart_1: ($i * $i * $i) > $i).
% 14.87/7.46  tff('#skF_5', type, '#skF_5': $i).
% 14.87/7.46  tff('#skF_6', type, '#skF_6': $i).
% 14.87/7.46  tff('#skF_2', type, '#skF_2': $i).
% 14.87/7.46  tff('#skF_3', type, '#skF_3': $i).
% 14.87/7.46  tff(k7_mcart_1, type, k7_mcart_1: ($i * $i * $i * $i) > $i).
% 14.87/7.46  tff(k3_zfmisc_1, type, k3_zfmisc_1: ($i * $i * $i) > $i).
% 14.87/7.46  tff(k5_mcart_1, type, k5_mcart_1: ($i * $i * $i * $i) > $i).
% 14.87/7.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.87/7.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 14.87/7.46  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 14.87/7.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 14.87/7.46  tff('#skF_4', type, '#skF_4': $i).
% 14.87/7.46  tff(k6_mcart_1, type, k6_mcart_1: ($i * $i * $i * $i) > $i).
% 14.87/7.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.87/7.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 14.87/7.46  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 14.87/7.46  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 14.87/7.46  
% 14.94/7.48  tff(f_131, negated_conjecture, ~(![A, B, C, D, E]: (m1_subset_1(E, k3_zfmisc_1(A, B, C)) => ((![F]: (m1_subset_1(F, A) => (![G]: (m1_subset_1(G, B) => (![H]: (m1_subset_1(H, C) => ((E = k3_mcart_1(F, G, H)) => (D = F)))))))) => ((((A = k1_xboole_0) | (B = k1_xboole_0)) | (C = k1_xboole_0)) | (D = k5_mcart_1(A, B, C, E)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_mcart_1)).
% 14.94/7.48  tff(f_107, axiom, (![A, B, C]: ~(((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) & ~(![D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => (((k5_mcart_1(A, B, C, D) = k1_mcart_1(k1_mcart_1(D))) & (k6_mcart_1(A, B, C, D) = k2_mcart_1(k1_mcart_1(D)))) & (k7_mcart_1(A, B, C, D) = k2_mcart_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_mcart_1)).
% 14.94/7.48  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(D, k3_zfmisc_1(A, B, C)) => m1_subset_1(k7_mcart_1(A, B, C, D), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_mcart_1)).
% 14.94/7.48  tff(f_53, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 14.94/7.48  tff(f_59, axiom, (![A, B, C]: (k3_zfmisc_1(A, B, C) = k2_zfmisc_1(k2_zfmisc_1(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_zfmisc_1)).
% 14.94/7.48  tff(f_55, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 14.94/7.48  tff(f_75, axiom, (![A, B]: (v1_relat_1(B) => (r2_hidden(A, B) => (A = k4_tarski(k1_mcart_1(A), k2_mcart_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t23_mcart_1)).
% 14.94/7.48  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 14.94/7.48  tff(f_69, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 14.94/7.48  tff(f_57, axiom, (![A, B, C]: (k3_mcart_1(A, B, C) = k4_tarski(k4_tarski(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_mcart_1)).
% 14.94/7.48  tff(f_32, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 14.94/7.48  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 14.94/7.48  tff(f_87, axiom, (![A, B, C]: (((~(A = k1_xboole_0) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0)) <=> ~(k3_zfmisc_1(A, B, C) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_mcart_1)).
% 14.94/7.48  tff(c_56, plain, (m1_subset_1('#skF_6', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.94/7.48  tff(c_52, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.94/7.48  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.94/7.48  tff(c_48, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.94/7.48  tff(c_433, plain, (![A_114, B_115, C_116, D_117]: (k7_mcart_1(A_114, B_115, C_116, D_117)=k2_mcart_1(D_117) | ~m1_subset_1(D_117, k3_zfmisc_1(A_114, B_115, C_116)) | k1_xboole_0=C_116 | k1_xboole_0=B_115 | k1_xboole_0=A_114)), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.94/7.48  tff(c_448, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_56, c_433])).
% 14.94/7.48  tff(c_463, plain, (k7_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')=k2_mcart_1('#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_448])).
% 14.94/7.48  tff(c_24, plain, (![A_17, B_18, C_19, D_20]: (m1_subset_1(k7_mcart_1(A_17, B_18, C_19, D_20), C_19) | ~m1_subset_1(D_20, k3_zfmisc_1(A_17, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 14.94/7.48  tff(c_471, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4') | ~m1_subset_1('#skF_6', k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_463, c_24])).
% 14.94/7.48  tff(c_475, plain, (m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_471])).
% 14.94/7.48  tff(c_119, plain, (![B_62, A_63]: (v1_xboole_0(B_62) | ~m1_subset_1(B_62, A_63) | ~v1_xboole_0(A_63))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.94/7.48  tff(c_123, plain, (v1_xboole_0('#skF_6') | ~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_119])).
% 14.94/7.48  tff(c_129, plain, (~v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitLeft, [status(thm)], [c_123])).
% 14.94/7.48  tff(c_150, plain, (![A_74, B_75, C_76]: (k2_zfmisc_1(k2_zfmisc_1(A_74, B_75), C_76)=k3_zfmisc_1(A_74, B_75, C_76))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.94/7.48  tff(c_18, plain, (![A_9, B_10]: (v1_relat_1(k2_zfmisc_1(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 14.94/7.48  tff(c_158, plain, (![A_74, B_75, C_76]: (v1_relat_1(k3_zfmisc_1(A_74, B_75, C_76)))), inference(superposition, [status(thm), theory('equality')], [c_150, c_18])).
% 14.94/7.48  tff(c_12, plain, (![B_8, A_7]: (r2_hidden(B_8, A_7) | ~m1_subset_1(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.94/7.48  tff(c_263, plain, (![A_96, B_97]: (k4_tarski(k1_mcart_1(A_96), k2_mcart_1(A_96))=A_96 | ~r2_hidden(A_96, B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.94/7.48  tff(c_3601, plain, (![B_276, A_277]: (k4_tarski(k1_mcart_1(B_276), k2_mcart_1(B_276))=B_276 | ~v1_relat_1(A_277) | ~m1_subset_1(B_276, A_277) | v1_xboole_0(A_277))), inference(resolution, [status(thm)], [c_12, c_263])).
% 14.94/7.48  tff(c_3611, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | ~v1_relat_1(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_3601])).
% 14.94/7.48  tff(c_3620, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6' | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_158, c_3611])).
% 14.94/7.48  tff(c_3621, plain, (k4_tarski(k1_mcart_1('#skF_6'), k2_mcart_1('#skF_6'))='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_129, c_3620])).
% 14.94/7.48  tff(c_46, plain, (k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.94/7.48  tff(c_4, plain, (![A_1]: (v1_xboole_0(A_1) | r2_hidden('#skF_1'(A_1), A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.94/7.48  tff(c_202, plain, (![A_86, B_87, C_88]: (r2_hidden(k1_mcart_1(A_86), B_87) | ~r2_hidden(A_86, k2_zfmisc_1(B_87, C_88)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.94/7.48  tff(c_740, plain, (![B_146, C_147]: (r2_hidden(k1_mcart_1('#skF_1'(k2_zfmisc_1(B_146, C_147))), B_146) | v1_xboole_0(k2_zfmisc_1(B_146, C_147)))), inference(resolution, [status(thm)], [c_4, c_202])).
% 14.94/7.48  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 14.94/7.48  tff(c_786, plain, (![B_146, C_147]: (~v1_xboole_0(B_146) | v1_xboole_0(k2_zfmisc_1(B_146, C_147)))), inference(resolution, [status(thm)], [c_740, c_2])).
% 14.94/7.48  tff(c_22, plain, (![A_14, B_15, C_16]: (k2_zfmisc_1(k2_zfmisc_1(A_14, B_15), C_16)=k3_zfmisc_1(A_14, B_15, C_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 14.94/7.48  tff(c_791, plain, (![B_148, C_149]: (~v1_xboole_0(B_148) | v1_xboole_0(k2_zfmisc_1(B_148, C_149)))), inference(resolution, [status(thm)], [c_740, c_2])).
% 14.94/7.48  tff(c_978, plain, (![A_164, B_165, C_166]: (~v1_xboole_0(k2_zfmisc_1(A_164, B_165)) | v1_xboole_0(k3_zfmisc_1(A_164, B_165, C_166)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_791])).
% 14.94/7.48  tff(c_1020, plain, (~v1_xboole_0(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_978, c_129])).
% 14.94/7.48  tff(c_1034, plain, (~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_786, c_1020])).
% 14.94/7.48  tff(c_482, plain, (![A_118, B_119, C_120, D_121]: (k5_mcart_1(A_118, B_119, C_120, D_121)=k1_mcart_1(k1_mcart_1(D_121)) | ~m1_subset_1(D_121, k3_zfmisc_1(A_118, B_119, C_120)) | k1_xboole_0=C_120 | k1_xboole_0=B_119 | k1_xboole_0=A_118)), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.94/7.48  tff(c_497, plain, (k1_mcart_1(k1_mcart_1('#skF_6'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_56, c_482])).
% 14.94/7.48  tff(c_512, plain, (k1_mcart_1(k1_mcart_1('#skF_6'))=k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_497])).
% 14.94/7.48  tff(c_1979, plain, (![A_210, A_211, B_212, C_213]: (r2_hidden(k1_mcart_1(A_210), k2_zfmisc_1(A_211, B_212)) | ~r2_hidden(A_210, k3_zfmisc_1(A_211, B_212, C_213)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_202])).
% 14.94/7.48  tff(c_49357, plain, (![B_1105, A_1106, B_1107, C_1108]: (r2_hidden(k1_mcart_1(B_1105), k2_zfmisc_1(A_1106, B_1107)) | ~m1_subset_1(B_1105, k3_zfmisc_1(A_1106, B_1107, C_1108)) | v1_xboole_0(k3_zfmisc_1(A_1106, B_1107, C_1108)))), inference(resolution, [status(thm)], [c_12, c_1979])).
% 14.94/7.48  tff(c_49432, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3')) | v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_56, c_49357])).
% 14.94/7.48  tff(c_49448, plain, (r2_hidden(k1_mcart_1('#skF_6'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_129, c_49432])).
% 14.94/7.48  tff(c_28, plain, (![A_21, B_22, C_23]: (r2_hidden(k1_mcart_1(A_21), B_22) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.94/7.48  tff(c_49457, plain, (r2_hidden(k1_mcart_1(k1_mcart_1('#skF_6')), '#skF_2')), inference(resolution, [status(thm)], [c_49448, c_28])).
% 14.94/7.48  tff(c_49470, plain, (r2_hidden(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_512, c_49457])).
% 14.94/7.48  tff(c_10, plain, (![B_8, A_7]: (m1_subset_1(B_8, A_7) | ~r2_hidden(B_8, A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_53])).
% 14.94/7.48  tff(c_49501, plain, (m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_49470, c_10])).
% 14.94/7.48  tff(c_49508, plain, (m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_1034, c_49501])).
% 14.94/7.48  tff(c_174, plain, (![A_80, C_81, B_82]: (r2_hidden(k2_mcart_1(A_80), C_81) | ~r2_hidden(A_80, k2_zfmisc_1(B_82, C_81)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.94/7.48  tff(c_287, plain, (![B_101, C_102]: (r2_hidden(k2_mcart_1('#skF_1'(k2_zfmisc_1(B_101, C_102))), C_102) | v1_xboole_0(k2_zfmisc_1(B_101, C_102)))), inference(resolution, [status(thm)], [c_4, c_174])).
% 14.94/7.48  tff(c_318, plain, (![C_102, B_101]: (~v1_xboole_0(C_102) | v1_xboole_0(k2_zfmisc_1(B_101, C_102)))), inference(resolution, [status(thm)], [c_287, c_2])).
% 14.94/7.48  tff(c_1035, plain, (~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_318, c_1020])).
% 14.94/7.48  tff(c_559, plain, (![A_128, B_129, C_130, D_131]: (k6_mcart_1(A_128, B_129, C_130, D_131)=k2_mcart_1(k1_mcart_1(D_131)) | ~m1_subset_1(D_131, k3_zfmisc_1(A_128, B_129, C_130)) | k1_xboole_0=C_130 | k1_xboole_0=B_129 | k1_xboole_0=A_128)), inference(cnfTransformation, [status(thm)], [f_107])).
% 14.94/7.48  tff(c_574, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6') | k1_xboole_0='#skF_4' | k1_xboole_0='#skF_3' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_56, c_559])).
% 14.94/7.48  tff(c_589, plain, (k2_mcart_1(k1_mcart_1('#skF_6'))=k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_52, c_50, c_48, c_574])).
% 14.94/7.48  tff(c_26, plain, (![A_21, C_23, B_22]: (r2_hidden(k2_mcart_1(A_21), C_23) | ~r2_hidden(A_21, k2_zfmisc_1(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 14.94/7.48  tff(c_49459, plain, (r2_hidden(k2_mcart_1(k1_mcart_1('#skF_6')), '#skF_3')), inference(resolution, [status(thm)], [c_49448, c_26])).
% 14.94/7.48  tff(c_49472, plain, (r2_hidden(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_589, c_49459])).
% 14.94/7.48  tff(c_49514, plain, (m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_49472, c_10])).
% 14.94/7.48  tff(c_49521, plain, (m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_1035, c_49514])).
% 14.94/7.48  tff(c_30, plain, (![A_24, B_25]: (k4_tarski(k1_mcart_1(A_24), k2_mcart_1(A_24))=A_24 | ~r2_hidden(A_24, B_25) | ~v1_relat_1(B_25))), inference(cnfTransformation, [status(thm)], [f_75])).
% 14.94/7.48  tff(c_49455, plain, (k4_tarski(k1_mcart_1(k1_mcart_1('#skF_6')), k2_mcart_1(k1_mcart_1('#skF_6')))=k1_mcart_1('#skF_6') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_49448, c_30])).
% 14.94/7.48  tff(c_49468, plain, (k4_tarski(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'))=k1_mcart_1('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_512, c_589, c_49455])).
% 14.94/7.48  tff(c_20, plain, (![A_11, B_12, C_13]: (k4_tarski(k4_tarski(A_11, B_12), C_13)=k3_mcart_1(A_11, B_12, C_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 14.94/7.48  tff(c_57726, plain, (![C_1170]: (k3_mcart_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), C_1170)=k4_tarski(k1_mcart_1('#skF_6'), C_1170))), inference(superposition, [status(thm), theory('equality')], [c_49468, c_20])).
% 14.94/7.48  tff(c_54, plain, (![F_41, G_45, H_47]: (F_41='#skF_5' | k3_mcart_1(F_41, G_45, H_47)!='#skF_6' | ~m1_subset_1(H_47, '#skF_4') | ~m1_subset_1(G_45, '#skF_3') | ~m1_subset_1(F_41, '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 14.94/7.48  tff(c_57733, plain, (![C_1170]: (k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5' | k4_tarski(k1_mcart_1('#skF_6'), C_1170)!='#skF_6' | ~m1_subset_1(C_1170, '#skF_4') | ~m1_subset_1(k6_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_3') | ~m1_subset_1(k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6'), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_57726, c_54])).
% 14.94/7.48  tff(c_57740, plain, (![C_1170]: (k5_mcart_1('#skF_2', '#skF_3', '#skF_4', '#skF_6')='#skF_5' | k4_tarski(k1_mcart_1('#skF_6'), C_1170)!='#skF_6' | ~m1_subset_1(C_1170, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_49508, c_49521, c_57733])).
% 14.94/7.48  tff(c_57743, plain, (![C_1171]: (k4_tarski(k1_mcart_1('#skF_6'), C_1171)!='#skF_6' | ~m1_subset_1(C_1171, '#skF_4'))), inference(negUnitSimplification, [status(thm)], [c_46, c_57740])).
% 14.94/7.48  tff(c_57746, plain, (~m1_subset_1(k2_mcart_1('#skF_6'), '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3621, c_57743])).
% 14.94/7.48  tff(c_57750, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_475, c_57746])).
% 14.94/7.48  tff(c_57751, plain, (v1_xboole_0('#skF_6')), inference(splitRight, [status(thm)], [c_123])).
% 14.94/7.48  tff(c_6, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_32])).
% 14.94/7.48  tff(c_104, plain, (![B_58, A_59]: (~v1_xboole_0(B_58) | B_58=A_59 | ~v1_xboole_0(A_59))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.94/7.48  tff(c_107, plain, (![A_59]: (k1_xboole_0=A_59 | ~v1_xboole_0(A_59))), inference(resolution, [status(thm)], [c_6, c_104])).
% 14.94/7.48  tff(c_57758, plain, (k1_xboole_0='#skF_6'), inference(resolution, [status(thm)], [c_57751, c_107])).
% 14.94/7.48  tff(c_57767, plain, ('#skF_6'!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_57758, c_52])).
% 14.94/7.48  tff(c_57766, plain, ('#skF_6'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_57758, c_50])).
% 14.94/7.48  tff(c_57765, plain, ('#skF_6'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_57758, c_48])).
% 14.94/7.48  tff(c_57752, plain, (v1_xboole_0(k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4'))), inference(splitRight, [status(thm)], [c_123])).
% 14.94/7.48  tff(c_8, plain, (![B_6, A_5]: (~v1_xboole_0(B_6) | B_6=A_5 | ~v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_40])).
% 14.94/7.48  tff(c_57759, plain, (![A_5]: (A_5='#skF_6' | ~v1_xboole_0(A_5))), inference(resolution, [status(thm)], [c_57751, c_8])).
% 14.94/7.48  tff(c_57790, plain, (k3_zfmisc_1('#skF_2', '#skF_3', '#skF_4')='#skF_6'), inference(resolution, [status(thm)], [c_57752, c_57759])).
% 14.94/7.48  tff(c_32, plain, (![A_26, B_27, C_28]: (k3_zfmisc_1(A_26, B_27, C_28)!=k1_xboole_0 | k1_xboole_0=C_28 | k1_xboole_0=B_27 | k1_xboole_0=A_26)), inference(cnfTransformation, [status(thm)], [f_87])).
% 14.94/7.48  tff(c_57993, plain, (![A_1211, B_1212, C_1213]: (k3_zfmisc_1(A_1211, B_1212, C_1213)!='#skF_6' | C_1213='#skF_6' | B_1212='#skF_6' | A_1211='#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_57758, c_57758, c_57758, c_57758, c_32])).
% 14.94/7.48  tff(c_57996, plain, ('#skF_6'='#skF_4' | '#skF_6'='#skF_3' | '#skF_6'='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_57790, c_57993])).
% 14.94/7.48  tff(c_58009, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57767, c_57766, c_57765, c_57996])).
% 14.94/7.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.94/7.48  
% 14.94/7.48  Inference rules
% 14.94/7.48  ----------------------
% 14.94/7.48  #Ref     : 0
% 14.94/7.48  #Sup     : 15308
% 14.94/7.48  #Fact    : 0
% 14.94/7.48  #Define  : 0
% 14.94/7.48  #Split   : 8
% 14.94/7.48  #Chain   : 0
% 14.94/7.48  #Close   : 0
% 14.94/7.48  
% 14.94/7.48  Ordering : KBO
% 14.94/7.48  
% 14.94/7.48  Simplification rules
% 14.94/7.48  ----------------------
% 14.94/7.48  #Subsume      : 1304
% 14.94/7.48  #Demod        : 12726
% 14.94/7.48  #Tautology    : 10002
% 14.94/7.48  #SimpNegUnit  : 85
% 14.94/7.48  #BackRed      : 11
% 14.94/7.48  
% 14.94/7.48  #Partial instantiations: 0
% 14.94/7.48  #Strategies tried      : 1
% 14.94/7.48  
% 14.94/7.48  Timing (in seconds)
% 14.94/7.48  ----------------------
% 14.94/7.49  Preprocessing        : 0.32
% 14.94/7.49  Parsing              : 0.17
% 14.94/7.49  CNF conversion       : 0.02
% 14.94/7.49  Main loop            : 6.37
% 14.94/7.49  Inferencing          : 1.30
% 14.94/7.49  Reduction            : 1.64
% 14.94/7.49  Demodulation         : 1.20
% 14.94/7.49  BG Simplification    : 0.15
% 14.94/7.49  Subsumption          : 2.94
% 14.94/7.49  Abstraction          : 0.26
% 14.94/7.49  MUC search           : 0.00
% 14.94/7.49  Cooper               : 0.00
% 14.94/7.49  Total                : 6.75
% 14.94/7.49  Index Insertion      : 0.00
% 14.94/7.49  Index Deletion       : 0.00
% 14.94/7.49  Index Matching       : 0.00
% 14.94/7.49  BG Taut test         : 0.00
%------------------------------------------------------------------------------
