%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:53 EST 2020

% Result     : Theorem 4.85s
% Output     : CNFRefutation 5.14s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 569 expanded)
%              Number of leaves         :   32 ( 202 expanded)
%              Depth                    :   16
%              Number of atoms          :  215 (1407 expanded)
%              Number of equality atoms :   55 ( 320 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_118,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_relat_1(B)
          & v1_funct_1(B) )
       => ( r1_tarski(k2_relat_1(B),A)
         => ( v1_funct_1(B)
            & v1_funct_2(B,k1_relat_1(B),A)
            & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_37,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_63,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_60,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ( r1_tarski(A,B)
           => ( r1_tarski(k1_relat_1(A),k1_relat_1(B))
              & r1_tarski(k2_relat_1(A),k2_relat_1(B)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(c_58,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    r1_tarski(k2_relat_1('#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_2938,plain,(
    ! [C_276,A_277,B_278] :
      ( m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_277,B_278)))
      | ~ r1_tarski(k2_relat_1(C_276),B_278)
      | ~ r1_tarski(k1_relat_1(C_276),A_277)
      | ~ v1_relat_1(C_276) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_56,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_52,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_118])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_52])).

tff(c_85,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_517,plain,(
    ! [C_99,A_100,B_101] :
      ( m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1(A_100,B_101)))
      | ~ r1_tarski(k2_relat_1(C_99),B_101)
      | ~ r1_tarski(k1_relat_1(C_99),A_100)
      | ~ v1_relat_1(C_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_14,plain,(
    ! [A_5,B_6] :
      ( r1_tarski(A_5,B_6)
      | ~ m1_subset_1(A_5,k1_zfmisc_1(B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1646,plain,(
    ! [C_181,A_182,B_183] :
      ( r1_tarski(C_181,k2_zfmisc_1(A_182,B_183))
      | ~ r1_tarski(k2_relat_1(C_181),B_183)
      | ~ r1_tarski(k1_relat_1(C_181),A_182)
      | ~ v1_relat_1(C_181) ) ),
    inference(resolution,[status(thm)],[c_517,c_14])).

tff(c_1652,plain,(
    ! [A_182] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_182,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_182)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_1646])).

tff(c_1667,plain,(
    ! [A_184] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(A_184,'#skF_1'))
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_184) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1652])).

tff(c_1687,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1667])).

tff(c_16,plain,(
    ! [A_5,B_6] :
      ( m1_subset_1(A_5,k1_zfmisc_1(B_6))
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_388,plain,(
    ! [A_85,B_86,C_87] :
      ( k1_relset_1(A_85,B_86,C_87) = k1_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_399,plain,(
    ! [A_85,B_86,A_5] :
      ( k1_relset_1(A_85,B_86,A_5) = k1_relat_1(A_5)
      | ~ r1_tarski(A_5,k2_zfmisc_1(A_85,B_86)) ) ),
    inference(resolution,[status(thm)],[c_16,c_388])).

tff(c_1699,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') = k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1687,c_399])).

tff(c_666,plain,(
    ! [B_117,C_118,A_119] :
      ( k1_xboole_0 = B_117
      | v1_funct_2(C_118,A_119,B_117)
      | k1_relset_1(A_119,B_117,C_118) != A_119
      | ~ m1_subset_1(C_118,k1_zfmisc_1(k2_zfmisc_1(A_119,B_117))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1709,plain,(
    ! [B_185,A_186,A_187] :
      ( k1_xboole_0 = B_185
      | v1_funct_2(A_186,A_187,B_185)
      | k1_relset_1(A_187,B_185,A_186) != A_187
      | ~ r1_tarski(A_186,k2_zfmisc_1(A_187,B_185)) ) ),
    inference(resolution,[status(thm)],[c_16,c_666])).

tff(c_1712,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1')
    | k1_relset_1(k1_relat_1('#skF_2'),'#skF_1','#skF_2') != k1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_1687,c_1709])).

tff(c_1725,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2('#skF_2',k1_relat_1('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1699,c_1712])).

tff(c_1726,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_1725])).

tff(c_76,plain,(
    ! [A_31] : k2_zfmisc_1(A_31,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_7,B_8] : v1_relat_1(k2_zfmisc_1(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_80,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_18])).

tff(c_28,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_24,plain,(
    ! [A_11,B_13] :
      ( r1_tarski(k1_relat_1(A_11),k1_relat_1(B_13))
      | ~ r1_tarski(A_11,B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_34,plain,(
    ! [C_18,A_16,B_17] :
      ( v4_relat_1(C_18,A_16)
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_754,plain,(
    ! [C_129,A_130,B_131] :
      ( v4_relat_1(C_129,A_130)
      | ~ r1_tarski(k2_relat_1(C_129),B_131)
      | ~ r1_tarski(k1_relat_1(C_129),A_130)
      | ~ v1_relat_1(C_129) ) ),
    inference(resolution,[status(thm)],[c_517,c_34])).

tff(c_760,plain,(
    ! [A_130] :
      ( v4_relat_1('#skF_2',A_130)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_130)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_54,c_754])).

tff(c_773,plain,(
    ! [A_132] :
      ( v4_relat_1('#skF_2',A_132)
      | ~ r1_tarski(k1_relat_1('#skF_2'),A_132) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_760])).

tff(c_781,plain,(
    ! [B_13] :
      ( v4_relat_1('#skF_2',k1_relat_1(B_13))
      | ~ r1_tarski('#skF_2',B_13)
      | ~ v1_relat_1(B_13)
      | ~ v1_relat_1('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_24,c_773])).

tff(c_917,plain,(
    ! [B_140] :
      ( v4_relat_1('#skF_2',k1_relat_1(B_140))
      | ~ r1_tarski('#skF_2',B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_781])).

tff(c_20,plain,(
    ! [B_10,A_9] :
      ( k7_relat_1(B_10,A_9) = B_10
      | ~ v4_relat_1(B_10,A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_920,plain,(
    ! [B_140] :
      ( k7_relat_1('#skF_2',k1_relat_1(B_140)) = '#skF_2'
      | ~ v1_relat_1('#skF_2')
      | ~ r1_tarski('#skF_2',B_140)
      | ~ v1_relat_1(B_140) ) ),
    inference(resolution,[status(thm)],[c_917,c_20])).

tff(c_935,plain,(
    ! [B_141] :
      ( k7_relat_1('#skF_2',k1_relat_1(B_141)) = '#skF_2'
      | ~ r1_tarski('#skF_2',B_141)
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_920])).

tff(c_968,plain,
    ( k7_relat_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0)
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_935])).

tff(c_987,plain,
    ( k7_relat_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_968])).

tff(c_988,plain,(
    ~ r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_987])).

tff(c_1742,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_988])).

tff(c_10,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1781,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1726,c_1726,c_10])).

tff(c_2036,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1781,c_1687])).

tff(c_2039,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1742,c_2036])).

tff(c_2041,plain,(
    r1_tarski('#skF_2',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_987])).

tff(c_132,plain,(
    ! [C_41,A_42,B_43] :
      ( v4_relat_1(C_41,A_42)
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_42,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_166,plain,(
    ! [A_52,A_53,B_54] :
      ( v4_relat_1(A_52,A_53)
      | ~ r1_tarski(A_52,k2_zfmisc_1(A_53,B_54)) ) ),
    inference(resolution,[status(thm)],[c_16,c_132])).

tff(c_190,plain,(
    ! [A_58,B_59] : v4_relat_1(k2_zfmisc_1(A_58,B_59),A_58) ),
    inference(resolution,[status(thm)],[c_6,c_166])).

tff(c_210,plain,(
    ! [A_60] : v4_relat_1(k1_xboole_0,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_190])).

tff(c_213,plain,(
    ! [A_60] :
      ( k7_relat_1(k1_xboole_0,A_60) = k1_xboole_0
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_210,c_20])).

tff(c_216,plain,(
    ! [A_60] : k7_relat_1(k1_xboole_0,A_60) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_213])).

tff(c_217,plain,(
    ! [B_61,A_62] :
      ( k1_relat_1(k7_relat_1(B_61,A_62)) = A_62
      | ~ r1_tarski(A_62,k1_relat_1(B_61))
      | ~ v1_relat_1(B_61) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_224,plain,(
    ! [A_62] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_62)) = A_62
      | ~ r1_tarski(A_62,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_217])).

tff(c_227,plain,(
    ! [A_62] :
      ( k1_relat_1(k7_relat_1(k1_xboole_0,A_62)) = A_62
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_224])).

tff(c_305,plain,(
    ! [A_62] :
      ( k1_xboole_0 = A_62
      | ~ r1_tarski(A_62,k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_216,c_227])).

tff(c_2102,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_2041,c_305])).

tff(c_40,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_25,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_64,plain,(
    ! [A_25] :
      ( v1_funct_2(k1_xboole_0,A_25,k1_xboole_0)
      | k1_xboole_0 = A_25
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_246,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_249,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_16,c_246])).

tff(c_253,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_249])).

tff(c_255,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_12,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_422,plain,(
    ! [B_91,C_92] :
      ( k1_relset_1(k1_xboole_0,B_91,C_92) = k1_relat_1(C_92)
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_388])).

tff(c_424,plain,(
    ! [B_91] : k1_relset_1(k1_xboole_0,B_91,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_255,c_422])).

tff(c_429,plain,(
    ! [B_91] : k1_relset_1(k1_xboole_0,B_91,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_424])).

tff(c_44,plain,(
    ! [C_27,B_26] :
      ( v1_funct_2(C_27,k1_xboole_0,B_26)
      | k1_relset_1(k1_xboole_0,B_26,C_27) != k1_xboole_0
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_723,plain,(
    ! [C_124,B_125] :
      ( v1_funct_2(C_124,k1_xboole_0,B_125)
      | k1_relset_1(k1_xboole_0,B_125,C_124) != k1_xboole_0
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_44])).

tff(c_725,plain,(
    ! [B_125] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_125)
      | k1_relset_1(k1_xboole_0,B_125,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_255,c_723])).

tff(c_731,plain,(
    ! [B_125] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_429,c_725])).

tff(c_2107,plain,(
    ! [B_125] : v1_funct_2('#skF_2','#skF_2',B_125) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_2102,c_731])).

tff(c_438,plain,(
    ! [A_94,B_95] :
      ( r1_tarski(k1_relat_1(A_94),k1_relat_1(B_95))
      | ~ r1_tarski(A_94,B_95)
      | ~ v1_relat_1(B_95)
      | ~ v1_relat_1(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_455,plain,(
    ! [A_94] :
      ( r1_tarski(k1_relat_1(A_94),k1_xboole_0)
      | ~ r1_tarski(A_94,k1_xboole_0)
      | ~ v1_relat_1(k1_xboole_0)
      | ~ v1_relat_1(A_94) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_438])).

tff(c_478,plain,(
    ! [A_97] :
      ( r1_tarski(k1_relat_1(A_97),k1_xboole_0)
      | ~ r1_tarski(A_97,k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_455])).

tff(c_497,plain,(
    ! [A_97] :
      ( k1_relat_1(A_97) = k1_xboole_0
      | ~ r1_tarski(A_97,k1_xboole_0)
      | ~ v1_relat_1(A_97) ) ),
    inference(resolution,[status(thm)],[c_478,c_305])).

tff(c_2080,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2041,c_497])).

tff(c_2095,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2080])).

tff(c_2152,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2102,c_2095])).

tff(c_2156,plain,(
    ~ v1_funct_2('#skF_2','#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_85])).

tff(c_2490,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2107,c_2156])).

tff(c_2491,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),'#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_2953,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_2'),'#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_2938,c_2491])).

tff(c_2967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6,c_54,c_2953])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:48:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.85/1.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.98  
% 5.14/1.98  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/1.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.14/1.99  
% 5.14/1.99  %Foreground sorts:
% 5.14/1.99  
% 5.14/1.99  
% 5.14/1.99  %Background operators:
% 5.14/1.99  
% 5.14/1.99  
% 5.14/1.99  %Foreground operators:
% 5.14/1.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 5.14/1.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.14/1.99  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 5.14/1.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.14/1.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.14/1.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 5.14/1.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 5.14/1.99  tff('#skF_2', type, '#skF_2': $i).
% 5.14/1.99  tff('#skF_1', type, '#skF_1': $i).
% 5.14/1.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 5.14/1.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 5.14/1.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.14/1.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.14/1.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 5.14/1.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.14/1.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.14/1.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 5.14/1.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 5.14/1.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.14/1.99  
% 5.14/2.00  tff(f_118, negated_conjecture, ~(![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 5.14/2.00  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.14/2.00  tff(f_87, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 5.14/2.00  tff(f_41, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 5.14/2.00  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 5.14/2.00  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 5.14/2.00  tff(f_37, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 5.14/2.00  tff(f_43, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 5.14/2.00  tff(f_63, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 5.14/2.00  tff(f_60, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (r1_tarski(A, B) => (r1_tarski(k1_relat_1(A), k1_relat_1(B)) & r1_tarski(k2_relat_1(A), k2_relat_1(B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_relat_1)).
% 5.14/2.00  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 5.14/2.00  tff(f_49, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 5.14/2.00  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 5.14/2.00  tff(c_58, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.14/2.00  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.14/2.00  tff(c_54, plain, (r1_tarski(k2_relat_1('#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.14/2.00  tff(c_2938, plain, (![C_276, A_277, B_278]: (m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_277, B_278))) | ~r1_tarski(k2_relat_1(C_276), B_278) | ~r1_tarski(k1_relat_1(C_276), A_277) | ~v1_relat_1(C_276))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.14/2.00  tff(c_56, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.14/2.00  tff(c_52, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_118])).
% 5.14/2.00  tff(c_60, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_52])).
% 5.14/2.00  tff(c_85, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(splitLeft, [status(thm)], [c_60])).
% 5.14/2.00  tff(c_517, plain, (![C_99, A_100, B_101]: (m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1(A_100, B_101))) | ~r1_tarski(k2_relat_1(C_99), B_101) | ~r1_tarski(k1_relat_1(C_99), A_100) | ~v1_relat_1(C_99))), inference(cnfTransformation, [status(thm)], [f_87])).
% 5.14/2.00  tff(c_14, plain, (![A_5, B_6]: (r1_tarski(A_5, B_6) | ~m1_subset_1(A_5, k1_zfmisc_1(B_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/2.00  tff(c_1646, plain, (![C_181, A_182, B_183]: (r1_tarski(C_181, k2_zfmisc_1(A_182, B_183)) | ~r1_tarski(k2_relat_1(C_181), B_183) | ~r1_tarski(k1_relat_1(C_181), A_182) | ~v1_relat_1(C_181))), inference(resolution, [status(thm)], [c_517, c_14])).
% 5.14/2.00  tff(c_1652, plain, (![A_182]: (r1_tarski('#skF_2', k2_zfmisc_1(A_182, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_182) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_1646])).
% 5.14/2.00  tff(c_1667, plain, (![A_184]: (r1_tarski('#skF_2', k2_zfmisc_1(A_184, '#skF_1')) | ~r1_tarski(k1_relat_1('#skF_2'), A_184))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1652])).
% 5.14/2.00  tff(c_1687, plain, (r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1667])).
% 5.14/2.00  tff(c_16, plain, (![A_5, B_6]: (m1_subset_1(A_5, k1_zfmisc_1(B_6)) | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.14/2.00  tff(c_388, plain, (![A_85, B_86, C_87]: (k1_relset_1(A_85, B_86, C_87)=k1_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 5.14/2.00  tff(c_399, plain, (![A_85, B_86, A_5]: (k1_relset_1(A_85, B_86, A_5)=k1_relat_1(A_5) | ~r1_tarski(A_5, k2_zfmisc_1(A_85, B_86)))), inference(resolution, [status(thm)], [c_16, c_388])).
% 5.14/2.00  tff(c_1699, plain, (k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1687, c_399])).
% 5.14/2.00  tff(c_666, plain, (![B_117, C_118, A_119]: (k1_xboole_0=B_117 | v1_funct_2(C_118, A_119, B_117) | k1_relset_1(A_119, B_117, C_118)!=A_119 | ~m1_subset_1(C_118, k1_zfmisc_1(k2_zfmisc_1(A_119, B_117))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.14/2.00  tff(c_1709, plain, (![B_185, A_186, A_187]: (k1_xboole_0=B_185 | v1_funct_2(A_186, A_187, B_185) | k1_relset_1(A_187, B_185, A_186)!=A_187 | ~r1_tarski(A_186, k2_zfmisc_1(A_187, B_185)))), inference(resolution, [status(thm)], [c_16, c_666])).
% 5.14/2.00  tff(c_1712, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1') | k1_relset_1(k1_relat_1('#skF_2'), '#skF_1', '#skF_2')!=k1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_1687, c_1709])).
% 5.14/2.00  tff(c_1725, plain, (k1_xboole_0='#skF_1' | v1_funct_2('#skF_2', k1_relat_1('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1699, c_1712])).
% 5.14/2.00  tff(c_1726, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_85, c_1725])).
% 5.14/2.00  tff(c_76, plain, (![A_31]: (k2_zfmisc_1(A_31, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.14/2.00  tff(c_18, plain, (![A_7, B_8]: (v1_relat_1(k2_zfmisc_1(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.14/2.00  tff(c_80, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_76, c_18])).
% 5.14/2.00  tff(c_28, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.14/2.00  tff(c_24, plain, (![A_11, B_13]: (r1_tarski(k1_relat_1(A_11), k1_relat_1(B_13)) | ~r1_tarski(A_11, B_13) | ~v1_relat_1(B_13) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.14/2.00  tff(c_34, plain, (![C_18, A_16, B_17]: (v4_relat_1(C_18, A_16) | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.14/2.00  tff(c_754, plain, (![C_129, A_130, B_131]: (v4_relat_1(C_129, A_130) | ~r1_tarski(k2_relat_1(C_129), B_131) | ~r1_tarski(k1_relat_1(C_129), A_130) | ~v1_relat_1(C_129))), inference(resolution, [status(thm)], [c_517, c_34])).
% 5.14/2.00  tff(c_760, plain, (![A_130]: (v4_relat_1('#skF_2', A_130) | ~r1_tarski(k1_relat_1('#skF_2'), A_130) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_54, c_754])).
% 5.14/2.00  tff(c_773, plain, (![A_132]: (v4_relat_1('#skF_2', A_132) | ~r1_tarski(k1_relat_1('#skF_2'), A_132))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_760])).
% 5.14/2.00  tff(c_781, plain, (![B_13]: (v4_relat_1('#skF_2', k1_relat_1(B_13)) | ~r1_tarski('#skF_2', B_13) | ~v1_relat_1(B_13) | ~v1_relat_1('#skF_2'))), inference(resolution, [status(thm)], [c_24, c_773])).
% 5.14/2.00  tff(c_917, plain, (![B_140]: (v4_relat_1('#skF_2', k1_relat_1(B_140)) | ~r1_tarski('#skF_2', B_140) | ~v1_relat_1(B_140))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_781])).
% 5.14/2.00  tff(c_20, plain, (![B_10, A_9]: (k7_relat_1(B_10, A_9)=B_10 | ~v4_relat_1(B_10, A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.14/2.00  tff(c_920, plain, (![B_140]: (k7_relat_1('#skF_2', k1_relat_1(B_140))='#skF_2' | ~v1_relat_1('#skF_2') | ~r1_tarski('#skF_2', B_140) | ~v1_relat_1(B_140))), inference(resolution, [status(thm)], [c_917, c_20])).
% 5.14/2.00  tff(c_935, plain, (![B_141]: (k7_relat_1('#skF_2', k1_relat_1(B_141))='#skF_2' | ~r1_tarski('#skF_2', B_141) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_920])).
% 5.14/2.00  tff(c_968, plain, (k7_relat_1('#skF_2', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0) | ~v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_28, c_935])).
% 5.14/2.00  tff(c_987, plain, (k7_relat_1('#skF_2', k1_xboole_0)='#skF_2' | ~r1_tarski('#skF_2', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_968])).
% 5.14/2.00  tff(c_988, plain, (~r1_tarski('#skF_2', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_987])).
% 5.14/2.00  tff(c_1742, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_988])).
% 5.14/2.00  tff(c_10, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.14/2.00  tff(c_1781, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1726, c_1726, c_10])).
% 5.14/2.00  tff(c_2036, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1781, c_1687])).
% 5.14/2.00  tff(c_2039, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1742, c_2036])).
% 5.14/2.00  tff(c_2041, plain, (r1_tarski('#skF_2', k1_xboole_0)), inference(splitRight, [status(thm)], [c_987])).
% 5.14/2.00  tff(c_132, plain, (![C_41, A_42, B_43]: (v4_relat_1(C_41, A_42) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_42, B_43))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.14/2.00  tff(c_166, plain, (![A_52, A_53, B_54]: (v4_relat_1(A_52, A_53) | ~r1_tarski(A_52, k2_zfmisc_1(A_53, B_54)))), inference(resolution, [status(thm)], [c_16, c_132])).
% 5.14/2.00  tff(c_190, plain, (![A_58, B_59]: (v4_relat_1(k2_zfmisc_1(A_58, B_59), A_58))), inference(resolution, [status(thm)], [c_6, c_166])).
% 5.14/2.00  tff(c_210, plain, (![A_60]: (v4_relat_1(k1_xboole_0, A_60))), inference(superposition, [status(thm), theory('equality')], [c_10, c_190])).
% 5.14/2.00  tff(c_213, plain, (![A_60]: (k7_relat_1(k1_xboole_0, A_60)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_210, c_20])).
% 5.14/2.00  tff(c_216, plain, (![A_60]: (k7_relat_1(k1_xboole_0, A_60)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_80, c_213])).
% 5.14/2.00  tff(c_217, plain, (![B_61, A_62]: (k1_relat_1(k7_relat_1(B_61, A_62))=A_62 | ~r1_tarski(A_62, k1_relat_1(B_61)) | ~v1_relat_1(B_61))), inference(cnfTransformation, [status(thm)], [f_69])).
% 5.14/2.00  tff(c_224, plain, (![A_62]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_62))=A_62 | ~r1_tarski(A_62, k1_xboole_0) | ~v1_relat_1(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_28, c_217])).
% 5.14/2.00  tff(c_227, plain, (![A_62]: (k1_relat_1(k7_relat_1(k1_xboole_0, A_62))=A_62 | ~r1_tarski(A_62, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_224])).
% 5.14/2.00  tff(c_305, plain, (![A_62]: (k1_xboole_0=A_62 | ~r1_tarski(A_62, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_216, c_227])).
% 5.14/2.00  tff(c_2102, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_2041, c_305])).
% 5.14/2.00  tff(c_40, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_25, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.14/2.00  tff(c_64, plain, (![A_25]: (v1_funct_2(k1_xboole_0, A_25, k1_xboole_0) | k1_xboole_0=A_25 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_40])).
% 5.14/2.00  tff(c_246, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_64])).
% 5.14/2.00  tff(c_249, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_16, c_246])).
% 5.14/2.00  tff(c_253, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_249])).
% 5.14/2.00  tff(c_255, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_64])).
% 5.14/2.00  tff(c_12, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.14/2.00  tff(c_422, plain, (![B_91, C_92]: (k1_relset_1(k1_xboole_0, B_91, C_92)=k1_relat_1(C_92) | ~m1_subset_1(C_92, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_388])).
% 5.14/2.00  tff(c_424, plain, (![B_91]: (k1_relset_1(k1_xboole_0, B_91, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_255, c_422])).
% 5.14/2.00  tff(c_429, plain, (![B_91]: (k1_relset_1(k1_xboole_0, B_91, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_28, c_424])).
% 5.14/2.00  tff(c_44, plain, (![C_27, B_26]: (v1_funct_2(C_27, k1_xboole_0, B_26) | k1_relset_1(k1_xboole_0, B_26, C_27)!=k1_xboole_0 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_26))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 5.14/2.00  tff(c_723, plain, (![C_124, B_125]: (v1_funct_2(C_124, k1_xboole_0, B_125) | k1_relset_1(k1_xboole_0, B_125, C_124)!=k1_xboole_0 | ~m1_subset_1(C_124, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_44])).
% 5.14/2.01  tff(c_725, plain, (![B_125]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_125) | k1_relset_1(k1_xboole_0, B_125, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_255, c_723])).
% 5.14/2.01  tff(c_731, plain, (![B_125]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_125))), inference(demodulation, [status(thm), theory('equality')], [c_429, c_725])).
% 5.14/2.01  tff(c_2107, plain, (![B_125]: (v1_funct_2('#skF_2', '#skF_2', B_125))), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_2102, c_731])).
% 5.14/2.01  tff(c_438, plain, (![A_94, B_95]: (r1_tarski(k1_relat_1(A_94), k1_relat_1(B_95)) | ~r1_tarski(A_94, B_95) | ~v1_relat_1(B_95) | ~v1_relat_1(A_94))), inference(cnfTransformation, [status(thm)], [f_60])).
% 5.14/2.01  tff(c_455, plain, (![A_94]: (r1_tarski(k1_relat_1(A_94), k1_xboole_0) | ~r1_tarski(A_94, k1_xboole_0) | ~v1_relat_1(k1_xboole_0) | ~v1_relat_1(A_94))), inference(superposition, [status(thm), theory('equality')], [c_28, c_438])).
% 5.14/2.01  tff(c_478, plain, (![A_97]: (r1_tarski(k1_relat_1(A_97), k1_xboole_0) | ~r1_tarski(A_97, k1_xboole_0) | ~v1_relat_1(A_97))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_455])).
% 5.14/2.01  tff(c_497, plain, (![A_97]: (k1_relat_1(A_97)=k1_xboole_0 | ~r1_tarski(A_97, k1_xboole_0) | ~v1_relat_1(A_97))), inference(resolution, [status(thm)], [c_478, c_305])).
% 5.14/2.01  tff(c_2080, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2041, c_497])).
% 5.14/2.01  tff(c_2095, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2080])).
% 5.14/2.01  tff(c_2152, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2102, c_2095])).
% 5.14/2.01  tff(c_2156, plain, (~v1_funct_2('#skF_2', '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_85])).
% 5.14/2.01  tff(c_2490, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2107, c_2156])).
% 5.14/2.01  tff(c_2491, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), '#skF_1')))), inference(splitRight, [status(thm)], [c_60])).
% 5.14/2.01  tff(c_2953, plain, (~r1_tarski(k2_relat_1('#skF_2'), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_2938, c_2491])).
% 5.14/2.01  tff(c_2967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_6, c_54, c_2953])).
% 5.14/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.14/2.01  
% 5.14/2.01  Inference rules
% 5.14/2.01  ----------------------
% 5.14/2.01  #Ref     : 0
% 5.14/2.01  #Sup     : 627
% 5.14/2.01  #Fact    : 0
% 5.14/2.01  #Define  : 0
% 5.14/2.01  #Split   : 9
% 5.14/2.01  #Chain   : 0
% 5.14/2.01  #Close   : 0
% 5.14/2.01  
% 5.14/2.01  Ordering : KBO
% 5.14/2.01  
% 5.14/2.01  Simplification rules
% 5.14/2.01  ----------------------
% 5.14/2.01  #Subsume      : 70
% 5.14/2.01  #Demod        : 753
% 5.14/2.01  #Tautology    : 265
% 5.14/2.01  #SimpNegUnit  : 3
% 5.14/2.01  #BackRed      : 105
% 5.14/2.01  
% 5.14/2.01  #Partial instantiations: 0
% 5.14/2.01  #Strategies tried      : 1
% 5.14/2.01  
% 5.14/2.01  Timing (in seconds)
% 5.14/2.01  ----------------------
% 5.14/2.01  Preprocessing        : 0.30
% 5.14/2.01  Parsing              : 0.16
% 5.14/2.01  CNF conversion       : 0.02
% 5.14/2.01  Main loop            : 0.85
% 5.14/2.01  Inferencing          : 0.28
% 5.14/2.01  Reduction            : 0.29
% 5.14/2.01  Demodulation         : 0.21
% 5.14/2.01  BG Simplification    : 0.04
% 5.14/2.01  Subsumption          : 0.18
% 5.14/2.01  Abstraction          : 0.04
% 5.14/2.01  MUC search           : 0.00
% 5.14/2.01  Cooper               : 0.00
% 5.14/2.01  Total                : 1.20
% 5.14/2.01  Index Insertion      : 0.00
% 5.14/2.01  Index Deletion       : 0.00
% 5.14/2.01  Index Matching       : 0.00
% 5.14/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------
