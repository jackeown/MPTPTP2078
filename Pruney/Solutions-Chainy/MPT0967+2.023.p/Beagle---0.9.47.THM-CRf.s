%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:16 EST 2020

% Result     : Theorem 20.99s
% Output     : CNFRefutation 21.24s
% Verified   : 
% Statistics : Number of formulae       :  205 (1757 expanded)
%              Number of leaves         :   39 ( 584 expanded)
%              Depth                    :   15
%              Number of atoms          :  375 (5173 expanded)
%              Number of equality atoms :   77 (1558 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_144,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(B,C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_funct_2)).

tff(f_67,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_124,axiom,(
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

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_94,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(B,A)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc4_relset_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_42,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_36,plain,(
    ! [A_22,B_23] : v1_relat_1(k2_zfmisc_1(A_22,B_23)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_66,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_79597,plain,(
    ! [B_2161,A_2162] :
      ( v1_relat_1(B_2161)
      | ~ m1_subset_1(B_2161,k1_zfmisc_1(A_2162))
      | ~ v1_relat_1(A_2162) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_79603,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_79597])).

tff(c_79610,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_79603])).

tff(c_79678,plain,(
    ! [C_2177,B_2178,A_2179] :
      ( v5_relat_1(C_2177,B_2178)
      | ~ m1_subset_1(C_2177,k1_zfmisc_1(k2_zfmisc_1(A_2179,B_2178))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79697,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_79678])).

tff(c_34,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v5_relat_1(B_21,A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_64,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_79711,plain,(
    ! [A_2185,C_2186,B_2187] :
      ( r1_tarski(A_2185,C_2186)
      | ~ r1_tarski(B_2187,C_2186)
      | ~ r1_tarski(A_2185,B_2187) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_79734,plain,(
    ! [A_2190] :
      ( r1_tarski(A_2190,'#skF_3')
      | ~ r1_tarski(A_2190,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_79711])).

tff(c_79743,plain,(
    ! [B_21] :
      ( r1_tarski(k2_relat_1(B_21),'#skF_3')
      | ~ v5_relat_1(B_21,'#skF_2')
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_34,c_79734])).

tff(c_79631,plain,(
    ! [C_2167,A_2168,B_2169] :
      ( v4_relat_1(C_2167,A_2168)
      | ~ m1_subset_1(C_2167,k1_zfmisc_1(k2_zfmisc_1(A_2168,B_2169))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_79650,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_79631])).

tff(c_30,plain,(
    ! [B_19,A_18] :
      ( r1_tarski(k1_relat_1(B_19),A_18)
      | ~ v4_relat_1(B_19,A_18)
      | ~ v1_relat_1(B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80728,plain,(
    ! [C_2285,A_2286,B_2287] :
      ( m1_subset_1(C_2285,k1_zfmisc_1(k2_zfmisc_1(A_2286,B_2287)))
      | ~ r1_tarski(k2_relat_1(C_2285),B_2287)
      | ~ r1_tarski(k1_relat_1(C_2285),A_2286)
      | ~ v1_relat_1(C_2285) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_22,plain,(
    ! [A_10,B_11] :
      ( m1_subset_1(A_10,k1_zfmisc_1(B_11))
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_14,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_199,plain,(
    ! [C_64,A_65,B_66] :
      ( v4_relat_1(C_64,A_65)
      | ~ m1_subset_1(C_64,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_244,plain,(
    ! [C_72,A_73] :
      ( v4_relat_1(C_72,A_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_199])).

tff(c_251,plain,(
    ! [A_10,A_73] :
      ( v4_relat_1(A_10,A_73)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_244])).

tff(c_150,plain,(
    ! [B_55,A_56] :
      ( v1_relat_1(B_55)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_56))
      | ~ v1_relat_1(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_156,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_150])).

tff(c_163,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_156])).

tff(c_62,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_108,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_62])).

tff(c_68,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_665,plain,(
    ! [A_122,B_123,C_124] :
      ( k1_relset_1(A_122,B_123,C_124) = k1_relat_1(C_124)
      | ~ m1_subset_1(C_124,k1_zfmisc_1(k2_zfmisc_1(A_122,B_123))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_684,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_66,c_665])).

tff(c_60072,plain,(
    ! [B_1610,A_1611,C_1612] :
      ( k1_xboole_0 = B_1610
      | k1_relset_1(A_1611,B_1610,C_1612) = A_1611
      | ~ v1_funct_2(C_1612,A_1611,B_1610)
      | ~ m1_subset_1(C_1612,k1_zfmisc_1(k2_zfmisc_1(A_1611,B_1610))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_60082,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_60072])).

tff(c_60097,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_684,c_60082])).

tff(c_60098,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_60097])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_561,plain,(
    ! [C_113,B_114,A_115] :
      ( v1_xboole_0(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k2_zfmisc_1(B_114,A_115)))
      | ~ v1_xboole_0(A_115) ) ),
    inference(cnfTransformation,[status(thm)],[f_94])).

tff(c_578,plain,(
    ! [C_113] :
      ( v1_xboole_0(C_113)
      | ~ m1_subset_1(C_113,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_561])).

tff(c_586,plain,(
    ! [C_116] :
      ( v1_xboole_0(C_116)
      | ~ m1_subset_1(C_116,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_578])).

tff(c_615,plain,(
    ! [A_118] :
      ( v1_xboole_0(A_118)
      | ~ r1_tarski(A_118,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_586])).

tff(c_628,plain,(
    ! [B_19] :
      ( v1_xboole_0(k1_relat_1(B_19))
      | ~ v4_relat_1(B_19,k1_xboole_0)
      | ~ v1_relat_1(B_19) ) ),
    inference(resolution,[status(thm)],[c_30,c_615])).

tff(c_60126,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v4_relat_1('#skF_4',k1_xboole_0)
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_60098,c_628])).

tff(c_60151,plain,
    ( v1_xboole_0('#skF_1')
    | ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_60126])).

tff(c_60163,plain,(
    ~ v4_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_60151])).

tff(c_60204,plain,(
    ~ r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_251,c_60163])).

tff(c_349,plain,(
    ! [C_86,B_87,A_88] :
      ( v5_relat_1(C_86,B_87)
      | ~ m1_subset_1(C_86,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_368,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_66,c_349])).

tff(c_333,plain,(
    ! [A_83,C_84,B_85] :
      ( r1_tarski(A_83,C_84)
      | ~ r1_tarski(B_85,C_84)
      | ~ r1_tarski(A_83,B_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_392,plain,(
    ! [A_90] :
      ( r1_tarski(A_90,'#skF_3')
      | ~ r1_tarski(A_90,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_64,c_333])).

tff(c_704,plain,(
    ! [B_128] :
      ( r1_tarski(k2_relat_1(B_128),'#skF_3')
      | ~ v5_relat_1(B_128,'#skF_2')
      | ~ v1_relat_1(B_128) ) ),
    inference(resolution,[status(thm)],[c_34,c_392])).

tff(c_32,plain,(
    ! [B_21,A_20] :
      ( v5_relat_1(B_21,A_20)
      | ~ r1_tarski(k2_relat_1(B_21),A_20)
      | ~ v1_relat_1(B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_721,plain,(
    ! [B_129] :
      ( v5_relat_1(B_129,'#skF_3')
      | ~ v5_relat_1(B_129,'#skF_2')
      | ~ v1_relat_1(B_129) ) ),
    inference(resolution,[status(thm)],[c_704,c_32])).

tff(c_735,plain,
    ( v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_368,c_721])).

tff(c_743,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_735])).

tff(c_218,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_66,c_199])).

tff(c_60135,plain,(
    ! [A_18] :
      ( r1_tarski('#skF_1',A_18)
      | ~ v4_relat_1('#skF_4',A_18)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60098,c_30])).

tff(c_60205,plain,(
    ! [A_1615] :
      ( r1_tarski('#skF_1',A_1615)
      | ~ v4_relat_1('#skF_4',A_1615) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_60135])).

tff(c_60226,plain,(
    r1_tarski('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_218,c_60205])).

tff(c_406,plain,(
    ! [B_21] :
      ( r1_tarski(k2_relat_1(B_21),'#skF_3')
      | ~ v5_relat_1(B_21,'#skF_2')
      | ~ v1_relat_1(B_21) ) ),
    inference(resolution,[status(thm)],[c_34,c_392])).

tff(c_59956,plain,(
    ! [C_1603,A_1604,B_1605] :
      ( m1_subset_1(C_1603,k1_zfmisc_1(k2_zfmisc_1(A_1604,B_1605)))
      | ~ r1_tarski(k2_relat_1(C_1603),B_1605)
      | ~ r1_tarski(k1_relat_1(C_1603),A_1604)
      | ~ v1_relat_1(C_1603) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_20,plain,(
    ! [A_10,B_11] :
      ( r1_tarski(A_10,B_11)
      | ~ m1_subset_1(A_10,k1_zfmisc_1(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61884,plain,(
    ! [C_1706,A_1707,B_1708] :
      ( r1_tarski(C_1706,k2_zfmisc_1(A_1707,B_1708))
      | ~ r1_tarski(k2_relat_1(C_1706),B_1708)
      | ~ r1_tarski(k1_relat_1(C_1706),A_1707)
      | ~ v1_relat_1(C_1706) ) ),
    inference(resolution,[status(thm)],[c_59956,c_20])).

tff(c_62141,plain,(
    ! [B_1712,A_1713] :
      ( r1_tarski(B_1712,k2_zfmisc_1(A_1713,'#skF_3'))
      | ~ r1_tarski(k1_relat_1(B_1712),A_1713)
      | ~ v5_relat_1(B_1712,'#skF_2')
      | ~ v1_relat_1(B_1712) ) ),
    inference(resolution,[status(thm)],[c_406,c_61884])).

tff(c_62150,plain,(
    ! [A_1713] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1713,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_1713)
      | ~ v5_relat_1('#skF_4','#skF_2')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60098,c_62141])).

tff(c_62178,plain,(
    ! [A_1714] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_1714,'#skF_3'))
      | ~ r1_tarski('#skF_1',A_1714) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_368,c_62150])).

tff(c_683,plain,(
    ! [A_122,B_123,A_10] :
      ( k1_relset_1(A_122,B_123,A_10) = k1_relat_1(A_10)
      | ~ r1_tarski(A_10,k2_zfmisc_1(A_122,B_123)) ) ),
    inference(resolution,[status(thm)],[c_22,c_665])).

tff(c_62181,plain,(
    ! [A_1714] :
      ( k1_relset_1(A_1714,'#skF_3','#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_1',A_1714) ) ),
    inference(resolution,[status(thm)],[c_62178,c_683])).

tff(c_62215,plain,(
    ! [A_1715] :
      ( k1_relset_1(A_1715,'#skF_3','#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_1',A_1715) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60098,c_62181])).

tff(c_62223,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_60226,c_62215])).

tff(c_46,plain,(
    ! [C_36,A_34,B_35] :
      ( m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_34,B_35)))
      | ~ r1_tarski(k2_relat_1(C_36),B_35)
      | ~ r1_tarski(k1_relat_1(C_36),A_34)
      | ~ v1_relat_1(C_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_60273,plain,(
    ! [B_1617,C_1618,A_1619] :
      ( k1_xboole_0 = B_1617
      | v1_funct_2(C_1618,A_1619,B_1617)
      | k1_relset_1(A_1619,B_1617,C_1618) != A_1619
      | ~ m1_subset_1(C_1618,k1_zfmisc_1(k2_zfmisc_1(A_1619,B_1617))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_64170,plain,(
    ! [B_1769,C_1770,A_1771] :
      ( k1_xboole_0 = B_1769
      | v1_funct_2(C_1770,A_1771,B_1769)
      | k1_relset_1(A_1771,B_1769,C_1770) != A_1771
      | ~ r1_tarski(k2_relat_1(C_1770),B_1769)
      | ~ r1_tarski(k1_relat_1(C_1770),A_1771)
      | ~ v1_relat_1(C_1770) ) ),
    inference(resolution,[status(thm)],[c_46,c_60273])).

tff(c_70840,plain,(
    ! [A_1943,B_1944,A_1945] :
      ( k1_xboole_0 = A_1943
      | v1_funct_2(B_1944,A_1945,A_1943)
      | k1_relset_1(A_1945,A_1943,B_1944) != A_1945
      | ~ r1_tarski(k1_relat_1(B_1944),A_1945)
      | ~ v5_relat_1(B_1944,A_1943)
      | ~ v1_relat_1(B_1944) ) ),
    inference(resolution,[status(thm)],[c_34,c_64170])).

tff(c_70892,plain,(
    ! [A_1943,A_1945] :
      ( k1_xboole_0 = A_1943
      | v1_funct_2('#skF_4',A_1945,A_1943)
      | k1_relset_1(A_1945,A_1943,'#skF_4') != A_1945
      | ~ r1_tarski('#skF_1',A_1945)
      | ~ v5_relat_1('#skF_4',A_1943)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60098,c_70840])).

tff(c_78061,plain,(
    ! [A_2116,A_2117] :
      ( k1_xboole_0 = A_2116
      | v1_funct_2('#skF_4',A_2117,A_2116)
      | k1_relset_1(A_2117,A_2116,'#skF_4') != A_2117
      | ~ r1_tarski('#skF_1',A_2117)
      | ~ v5_relat_1('#skF_4',A_2116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_70892])).

tff(c_70,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_60,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_72,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_60])).

tff(c_133,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_78080,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_1')
    | ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_78061,c_133])).

tff(c_78093,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_60226,c_62223,c_78080])).

tff(c_61191,plain,(
    ! [C_1680,A_1681] :
      ( m1_subset_1(C_1680,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(C_1680),k1_xboole_0)
      | ~ r1_tarski(k1_relat_1(C_1680),A_1681)
      | ~ v1_relat_1(C_1680) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_59956])).

tff(c_64097,plain,(
    ! [B_1767,A_1768] :
      ( m1_subset_1(B_1767,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k1_relat_1(B_1767),A_1768)
      | ~ v5_relat_1(B_1767,k1_xboole_0)
      | ~ v1_relat_1(B_1767) ) ),
    inference(resolution,[status(thm)],[c_34,c_61191])).

tff(c_64131,plain,(
    ! [A_1768] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',A_1768)
      | ~ v5_relat_1('#skF_4',k1_xboole_0)
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60098,c_64097])).

tff(c_64162,plain,(
    ! [A_1768] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski('#skF_1',A_1768)
      | ~ v5_relat_1('#skF_4',k1_xboole_0) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_64131])).

tff(c_64169,plain,(
    ~ v5_relat_1('#skF_4',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_64162])).

tff(c_78209,plain,(
    ~ v5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78093,c_64169])).

tff(c_78301,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_78209])).

tff(c_78302,plain,(
    ! [A_1768] :
      ( ~ r1_tarski('#skF_1',A_1768)
      | m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(splitRight,[status(thm)],[c_64162])).

tff(c_78637,plain,(
    ! [A_1768] : ~ r1_tarski('#skF_1',A_1768) ),
    inference(splitLeft,[status(thm)],[c_78302])).

tff(c_78640,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78637,c_60226])).

tff(c_78641,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_78302])).

tff(c_78708,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_78641,c_20])).

tff(c_78725,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60204,c_78708])).

tff(c_78726,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_60151])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_78731,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_78726,c_4])).

tff(c_16,plain,(
    ! [B_8] : k2_zfmisc_1(k1_xboole_0,B_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_78778,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78731,c_78731,c_16])).

tff(c_123,plain,(
    ! [A_49,B_50] :
      ( r1_tarski(A_49,B_50)
      | ~ m1_subset_1(A_49,k1_zfmisc_1(B_50)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_130,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_79027,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78778,c_130])).

tff(c_595,plain,(
    ! [A_10] :
      ( v1_xboole_0(A_10)
      | ~ r1_tarski(A_10,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_22,c_586])).

tff(c_79152,plain,(
    ! [A_2140] :
      ( v1_xboole_0(A_2140)
      | ~ r1_tarski(A_2140,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78731,c_595])).

tff(c_79168,plain,(
    v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_79027,c_79152])).

tff(c_78780,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78731,c_4])).

tff(c_79176,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_79168,c_78780])).

tff(c_109,plain,(
    ! [A_45,B_46] : v1_relat_1(k2_zfmisc_1(A_45,B_46)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_111,plain,(
    v1_relat_1(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_109])).

tff(c_18,plain,(
    ! [A_9] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_219,plain,(
    ! [A_65] : v4_relat_1(k1_xboole_0,A_65) ),
    inference(resolution,[status(thm)],[c_18,c_199])).

tff(c_233,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(k1_relat_1(B_69),A_70)
      | ~ v4_relat_1(B_69,A_70)
      | ~ v1_relat_1(B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_10,plain,(
    ! [A_6] :
      ( k1_xboole_0 = A_6
      | ~ r1_tarski(A_6,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_260,plain,(
    ! [B_78] :
      ( k1_relat_1(B_78) = k1_xboole_0
      | ~ v4_relat_1(B_78,k1_xboole_0)
      | ~ v1_relat_1(B_78) ) ),
    inference(resolution,[status(thm)],[c_233,c_10])).

tff(c_268,plain,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    | ~ v1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_219,c_260])).

tff(c_272,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_268])).

tff(c_676,plain,(
    ! [A_122,B_123] : k1_relset_1(A_122,B_123,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_665])).

tff(c_686,plain,(
    ! [A_122,B_123] : k1_relset_1(A_122,B_123,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_676])).

tff(c_52,plain,(
    ! [C_39,B_38] :
      ( v1_funct_2(C_39,k1_xboole_0,B_38)
      | k1_relset_1(k1_xboole_0,B_38,C_39) != k1_xboole_0
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_1140,plain,(
    ! [C_172,B_173] :
      ( v1_funct_2(C_172,k1_xboole_0,B_173)
      | k1_relset_1(k1_xboole_0,B_173,C_172) != k1_xboole_0
      | ~ m1_subset_1(C_172,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_1146,plain,(
    ! [B_173] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_173)
      | k1_relset_1(k1_xboole_0,B_173,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_18,c_1140])).

tff(c_1150,plain,(
    ! [B_173] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_686,c_1146])).

tff(c_78735,plain,(
    ! [B_173] : v1_funct_2('#skF_1','#skF_1',B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78731,c_78731,c_1150])).

tff(c_79200,plain,(
    ! [B_173] : v1_funct_2('#skF_4','#skF_4',B_173) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79176,c_79176,c_78735])).

tff(c_79221,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79176,c_133])).

tff(c_79574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79200,c_79221])).

tff(c_79575,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_80748,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80728,c_79575])).

tff(c_80768,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79610,c_80748])).

tff(c_80770,plain,(
    ~ r1_tarski(k1_relat_1('#skF_4'),'#skF_1') ),
    inference(splitLeft,[status(thm)],[c_80768])).

tff(c_80776,plain,
    ( ~ v4_relat_1('#skF_4','#skF_1')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_80770])).

tff(c_80783,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79610,c_79650,c_80776])).

tff(c_80784,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_80768])).

tff(c_80839,plain,
    ( ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_79743,c_80784])).

tff(c_80849,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_79610,c_79697,c_80839])).

tff(c_80850,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_80853,plain,(
    ! [B_8] : k2_zfmisc_1('#skF_1',B_8) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80850,c_80850,c_16])).

tff(c_80851,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_62])).

tff(c_80862,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80850,c_80851])).

tff(c_80898,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80853,c_80862,c_66])).

tff(c_80917,plain,(
    ! [A_2299,B_2300] :
      ( r1_tarski(A_2299,B_2300)
      | ~ m1_subset_1(A_2299,k1_zfmisc_1(B_2300)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_80926,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_80898,c_80917])).

tff(c_80907,plain,(
    ! [A_6] :
      ( A_6 = '#skF_1'
      | ~ r1_tarski(A_6,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80850,c_80850,c_10])).

tff(c_80930,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_80926,c_80907])).

tff(c_80854,plain,(
    ! [A_7] : k2_zfmisc_1(A_7,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80850,c_80850,c_14])).

tff(c_80893,plain,(
    ! [A_2293,B_2294] : v1_relat_1(k2_zfmisc_1(A_2293,B_2294)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_80895,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_80854,c_80893])).

tff(c_80940,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80930,c_80895])).

tff(c_80852,plain,(
    ! [A_9] : m1_subset_1('#skF_1',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80850,c_18])).

tff(c_80939,plain,(
    ! [A_9] : m1_subset_1('#skF_4',k1_zfmisc_1(A_9)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80930,c_80852])).

tff(c_81050,plain,(
    ! [C_2318,A_2319,B_2320] :
      ( v4_relat_1(C_2318,A_2319)
      | ~ m1_subset_1(C_2318,k1_zfmisc_1(k2_zfmisc_1(A_2319,B_2320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_81065,plain,(
    ! [A_2319] : v4_relat_1('#skF_4',A_2319) ),
    inference(resolution,[status(thm)],[c_80939,c_81050])).

tff(c_81079,plain,(
    ! [B_2326,A_2327] :
      ( r1_tarski(k1_relat_1(B_2326),A_2327)
      | ~ v4_relat_1(B_2326,A_2327)
      | ~ v1_relat_1(B_2326) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_80936,plain,(
    ! [A_6] :
      ( A_6 = '#skF_4'
      | ~ r1_tarski(A_6,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80930,c_80930,c_80907])).

tff(c_81111,plain,(
    ! [B_2331] :
      ( k1_relat_1(B_2331) = '#skF_4'
      | ~ v4_relat_1(B_2331,'#skF_4')
      | ~ v1_relat_1(B_2331) ) ),
    inference(resolution,[status(thm)],[c_81079,c_80936])).

tff(c_81119,plain,
    ( k1_relat_1('#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_81065,c_81111])).

tff(c_81123,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80940,c_81119])).

tff(c_81353,plain,(
    ! [A_2366,B_2367,C_2368] :
      ( k1_relset_1(A_2366,B_2367,C_2368) = k1_relat_1(C_2368)
      | ~ m1_subset_1(C_2368,k1_zfmisc_1(k2_zfmisc_1(A_2366,B_2367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_81357,plain,(
    ! [A_2366,B_2367] : k1_relset_1(A_2366,B_2367,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_80939,c_81353])).

tff(c_81369,plain,(
    ! [A_2366,B_2367] : k1_relset_1(A_2366,B_2367,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_81123,c_81357])).

tff(c_80947,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_80930,c_80850])).

tff(c_76,plain,(
    ! [C_39,B_38] :
      ( v1_funct_2(C_39,k1_xboole_0,B_38)
      | k1_relset_1(k1_xboole_0,B_38,C_39) != k1_xboole_0
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_81798,plain,(
    ! [C_2416,B_2417] :
      ( v1_funct_2(C_2416,'#skF_4',B_2417)
      | k1_relset_1('#skF_4',B_2417,C_2416) != '#skF_4'
      | ~ m1_subset_1(C_2416,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80947,c_80947,c_80947,c_80947,c_76])).

tff(c_81801,plain,(
    ! [B_2417] :
      ( v1_funct_2('#skF_4','#skF_4',B_2417)
      | k1_relset_1('#skF_4',B_2417,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_80939,c_81798])).

tff(c_81807,plain,(
    ! [B_2417] : v1_funct_2('#skF_4','#skF_4',B_2417) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81369,c_81801])).

tff(c_80932,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80898,c_80853,c_72])).

tff(c_80933,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80930,c_80932])).

tff(c_81812,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_81807,c_80933])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:11:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 20.99/11.97  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 20.99/11.99  
% 20.99/11.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.18/11.99  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 21.18/11.99  
% 21.18/11.99  %Foreground sorts:
% 21.18/11.99  
% 21.18/11.99  
% 21.18/11.99  %Background operators:
% 21.18/11.99  
% 21.18/11.99  
% 21.18/11.99  %Foreground operators:
% 21.18/11.99  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 21.18/11.99  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 21.18/11.99  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 21.18/11.99  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 21.18/11.99  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 21.18/11.99  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 21.18/11.99  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 21.18/11.99  tff('#skF_2', type, '#skF_2': $i).
% 21.18/11.99  tff('#skF_3', type, '#skF_3': $i).
% 21.18/11.99  tff('#skF_1', type, '#skF_1': $i).
% 21.18/11.99  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 21.18/11.99  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 21.18/11.99  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 21.18/11.99  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 21.18/11.99  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 21.18/11.99  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 21.18/11.99  tff('#skF_4', type, '#skF_4': $i).
% 21.18/11.99  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 21.18/11.99  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 21.18/11.99  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 21.18/11.99  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 21.18/11.99  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 21.18/11.99  
% 21.24/12.02  tff(f_81, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 21.24/12.02  tff(f_144, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(B, C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_funct_2)).
% 21.24/12.02  tff(f_67, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 21.24/12.02  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 21.24/12.02  tff(f_79, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 21.24/12.02  tff(f_36, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 21.24/12.02  tff(f_73, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 21.24/12.02  tff(f_106, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 21.24/12.02  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 21.24/12.02  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 21.24/12.02  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 21.24/12.02  tff(f_124, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 21.24/12.02  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 21.24/12.02  tff(f_94, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(B, A))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc4_relset_1)).
% 21.24/12.02  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 21.24/12.02  tff(f_50, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 21.24/12.02  tff(f_42, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 21.24/12.02  tff(c_36, plain, (![A_22, B_23]: (v1_relat_1(k2_zfmisc_1(A_22, B_23)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.24/12.02  tff(c_66, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_144])).
% 21.24/12.02  tff(c_79597, plain, (![B_2161, A_2162]: (v1_relat_1(B_2161) | ~m1_subset_1(B_2161, k1_zfmisc_1(A_2162)) | ~v1_relat_1(A_2162))), inference(cnfTransformation, [status(thm)], [f_67])).
% 21.24/12.02  tff(c_79603, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_79597])).
% 21.24/12.02  tff(c_79610, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_79603])).
% 21.24/12.02  tff(c_79678, plain, (![C_2177, B_2178, A_2179]: (v5_relat_1(C_2177, B_2178) | ~m1_subset_1(C_2177, k1_zfmisc_1(k2_zfmisc_1(A_2179, B_2178))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.24/12.02  tff(c_79697, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_79678])).
% 21.24/12.02  tff(c_34, plain, (![B_21, A_20]: (r1_tarski(k2_relat_1(B_21), A_20) | ~v5_relat_1(B_21, A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 21.24/12.02  tff(c_64, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_144])).
% 21.24/12.02  tff(c_79711, plain, (![A_2185, C_2186, B_2187]: (r1_tarski(A_2185, C_2186) | ~r1_tarski(B_2187, C_2186) | ~r1_tarski(A_2185, B_2187))), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.24/12.02  tff(c_79734, plain, (![A_2190]: (r1_tarski(A_2190, '#skF_3') | ~r1_tarski(A_2190, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_79711])).
% 21.24/12.02  tff(c_79743, plain, (![B_21]: (r1_tarski(k2_relat_1(B_21), '#skF_3') | ~v5_relat_1(B_21, '#skF_2') | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_34, c_79734])).
% 21.24/12.02  tff(c_79631, plain, (![C_2167, A_2168, B_2169]: (v4_relat_1(C_2167, A_2168) | ~m1_subset_1(C_2167, k1_zfmisc_1(k2_zfmisc_1(A_2168, B_2169))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.24/12.02  tff(c_79650, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_79631])).
% 21.24/12.02  tff(c_30, plain, (![B_19, A_18]: (r1_tarski(k1_relat_1(B_19), A_18) | ~v4_relat_1(B_19, A_18) | ~v1_relat_1(B_19))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.24/12.02  tff(c_80728, plain, (![C_2285, A_2286, B_2287]: (m1_subset_1(C_2285, k1_zfmisc_1(k2_zfmisc_1(A_2286, B_2287))) | ~r1_tarski(k2_relat_1(C_2285), B_2287) | ~r1_tarski(k1_relat_1(C_2285), A_2286) | ~v1_relat_1(C_2285))), inference(cnfTransformation, [status(thm)], [f_106])).
% 21.24/12.02  tff(c_22, plain, (![A_10, B_11]: (m1_subset_1(A_10, k1_zfmisc_1(B_11)) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.24/12.02  tff(c_14, plain, (![A_7]: (k2_zfmisc_1(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.24/12.02  tff(c_199, plain, (![C_64, A_65, B_66]: (v4_relat_1(C_64, A_65) | ~m1_subset_1(C_64, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.24/12.02  tff(c_244, plain, (![C_72, A_73]: (v4_relat_1(C_72, A_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_199])).
% 21.24/12.02  tff(c_251, plain, (![A_10, A_73]: (v4_relat_1(A_10, A_73) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_244])).
% 21.24/12.02  tff(c_150, plain, (![B_55, A_56]: (v1_relat_1(B_55) | ~m1_subset_1(B_55, k1_zfmisc_1(A_56)) | ~v1_relat_1(A_56))), inference(cnfTransformation, [status(thm)], [f_67])).
% 21.24/12.02  tff(c_156, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_150])).
% 21.24/12.02  tff(c_163, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_156])).
% 21.24/12.02  tff(c_62, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_144])).
% 21.24/12.02  tff(c_108, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_62])).
% 21.24/12.02  tff(c_68, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_144])).
% 21.24/12.02  tff(c_665, plain, (![A_122, B_123, C_124]: (k1_relset_1(A_122, B_123, C_124)=k1_relat_1(C_124) | ~m1_subset_1(C_124, k1_zfmisc_1(k2_zfmisc_1(A_122, B_123))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 21.24/12.02  tff(c_684, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_66, c_665])).
% 21.24/12.02  tff(c_60072, plain, (![B_1610, A_1611, C_1612]: (k1_xboole_0=B_1610 | k1_relset_1(A_1611, B_1610, C_1612)=A_1611 | ~v1_funct_2(C_1612, A_1611, B_1610) | ~m1_subset_1(C_1612, k1_zfmisc_1(k2_zfmisc_1(A_1611, B_1610))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.24/12.02  tff(c_60082, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_60072])).
% 21.24/12.02  tff(c_60097, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_68, c_684, c_60082])).
% 21.24/12.02  tff(c_60098, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_108, c_60097])).
% 21.24/12.02  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 21.24/12.02  tff(c_561, plain, (![C_113, B_114, A_115]: (v1_xboole_0(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k2_zfmisc_1(B_114, A_115))) | ~v1_xboole_0(A_115))), inference(cnfTransformation, [status(thm)], [f_94])).
% 21.24/12.02  tff(c_578, plain, (![C_113]: (v1_xboole_0(C_113) | ~m1_subset_1(C_113, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_561])).
% 21.24/12.02  tff(c_586, plain, (![C_116]: (v1_xboole_0(C_116) | ~m1_subset_1(C_116, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_578])).
% 21.24/12.02  tff(c_615, plain, (![A_118]: (v1_xboole_0(A_118) | ~r1_tarski(A_118, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_586])).
% 21.24/12.02  tff(c_628, plain, (![B_19]: (v1_xboole_0(k1_relat_1(B_19)) | ~v4_relat_1(B_19, k1_xboole_0) | ~v1_relat_1(B_19))), inference(resolution, [status(thm)], [c_30, c_615])).
% 21.24/12.02  tff(c_60126, plain, (v1_xboole_0('#skF_1') | ~v4_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_60098, c_628])).
% 21.24/12.02  tff(c_60151, plain, (v1_xboole_0('#skF_1') | ~v4_relat_1('#skF_4', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_163, c_60126])).
% 21.24/12.02  tff(c_60163, plain, (~v4_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_60151])).
% 21.24/12.02  tff(c_60204, plain, (~r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_251, c_60163])).
% 21.24/12.02  tff(c_349, plain, (![C_86, B_87, A_88]: (v5_relat_1(C_86, B_87) | ~m1_subset_1(C_86, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.24/12.02  tff(c_368, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_66, c_349])).
% 21.24/12.02  tff(c_333, plain, (![A_83, C_84, B_85]: (r1_tarski(A_83, C_84) | ~r1_tarski(B_85, C_84) | ~r1_tarski(A_83, B_85))), inference(cnfTransformation, [status(thm)], [f_36])).
% 21.24/12.02  tff(c_392, plain, (![A_90]: (r1_tarski(A_90, '#skF_3') | ~r1_tarski(A_90, '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_333])).
% 21.24/12.02  tff(c_704, plain, (![B_128]: (r1_tarski(k2_relat_1(B_128), '#skF_3') | ~v5_relat_1(B_128, '#skF_2') | ~v1_relat_1(B_128))), inference(resolution, [status(thm)], [c_34, c_392])).
% 21.24/12.02  tff(c_32, plain, (![B_21, A_20]: (v5_relat_1(B_21, A_20) | ~r1_tarski(k2_relat_1(B_21), A_20) | ~v1_relat_1(B_21))), inference(cnfTransformation, [status(thm)], [f_79])).
% 21.24/12.02  tff(c_721, plain, (![B_129]: (v5_relat_1(B_129, '#skF_3') | ~v5_relat_1(B_129, '#skF_2') | ~v1_relat_1(B_129))), inference(resolution, [status(thm)], [c_704, c_32])).
% 21.24/12.02  tff(c_735, plain, (v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_368, c_721])).
% 21.24/12.02  tff(c_743, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_163, c_735])).
% 21.24/12.02  tff(c_218, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_66, c_199])).
% 21.24/12.02  tff(c_60135, plain, (![A_18]: (r1_tarski('#skF_1', A_18) | ~v4_relat_1('#skF_4', A_18) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_60098, c_30])).
% 21.24/12.02  tff(c_60205, plain, (![A_1615]: (r1_tarski('#skF_1', A_1615) | ~v4_relat_1('#skF_4', A_1615))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_60135])).
% 21.24/12.02  tff(c_60226, plain, (r1_tarski('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_218, c_60205])).
% 21.24/12.02  tff(c_406, plain, (![B_21]: (r1_tarski(k2_relat_1(B_21), '#skF_3') | ~v5_relat_1(B_21, '#skF_2') | ~v1_relat_1(B_21))), inference(resolution, [status(thm)], [c_34, c_392])).
% 21.24/12.02  tff(c_59956, plain, (![C_1603, A_1604, B_1605]: (m1_subset_1(C_1603, k1_zfmisc_1(k2_zfmisc_1(A_1604, B_1605))) | ~r1_tarski(k2_relat_1(C_1603), B_1605) | ~r1_tarski(k1_relat_1(C_1603), A_1604) | ~v1_relat_1(C_1603))), inference(cnfTransformation, [status(thm)], [f_106])).
% 21.24/12.02  tff(c_20, plain, (![A_10, B_11]: (r1_tarski(A_10, B_11) | ~m1_subset_1(A_10, k1_zfmisc_1(B_11)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.24/12.02  tff(c_61884, plain, (![C_1706, A_1707, B_1708]: (r1_tarski(C_1706, k2_zfmisc_1(A_1707, B_1708)) | ~r1_tarski(k2_relat_1(C_1706), B_1708) | ~r1_tarski(k1_relat_1(C_1706), A_1707) | ~v1_relat_1(C_1706))), inference(resolution, [status(thm)], [c_59956, c_20])).
% 21.24/12.02  tff(c_62141, plain, (![B_1712, A_1713]: (r1_tarski(B_1712, k2_zfmisc_1(A_1713, '#skF_3')) | ~r1_tarski(k1_relat_1(B_1712), A_1713) | ~v5_relat_1(B_1712, '#skF_2') | ~v1_relat_1(B_1712))), inference(resolution, [status(thm)], [c_406, c_61884])).
% 21.24/12.02  tff(c_62150, plain, (![A_1713]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1713, '#skF_3')) | ~r1_tarski('#skF_1', A_1713) | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_60098, c_62141])).
% 21.24/12.02  tff(c_62178, plain, (![A_1714]: (r1_tarski('#skF_4', k2_zfmisc_1(A_1714, '#skF_3')) | ~r1_tarski('#skF_1', A_1714))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_368, c_62150])).
% 21.24/12.02  tff(c_683, plain, (![A_122, B_123, A_10]: (k1_relset_1(A_122, B_123, A_10)=k1_relat_1(A_10) | ~r1_tarski(A_10, k2_zfmisc_1(A_122, B_123)))), inference(resolution, [status(thm)], [c_22, c_665])).
% 21.24/12.02  tff(c_62181, plain, (![A_1714]: (k1_relset_1(A_1714, '#skF_3', '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_1', A_1714))), inference(resolution, [status(thm)], [c_62178, c_683])).
% 21.24/12.02  tff(c_62215, plain, (![A_1715]: (k1_relset_1(A_1715, '#skF_3', '#skF_4')='#skF_1' | ~r1_tarski('#skF_1', A_1715))), inference(demodulation, [status(thm), theory('equality')], [c_60098, c_62181])).
% 21.24/12.02  tff(c_62223, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_60226, c_62215])).
% 21.24/12.02  tff(c_46, plain, (![C_36, A_34, B_35]: (m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_34, B_35))) | ~r1_tarski(k2_relat_1(C_36), B_35) | ~r1_tarski(k1_relat_1(C_36), A_34) | ~v1_relat_1(C_36))), inference(cnfTransformation, [status(thm)], [f_106])).
% 21.24/12.02  tff(c_60273, plain, (![B_1617, C_1618, A_1619]: (k1_xboole_0=B_1617 | v1_funct_2(C_1618, A_1619, B_1617) | k1_relset_1(A_1619, B_1617, C_1618)!=A_1619 | ~m1_subset_1(C_1618, k1_zfmisc_1(k2_zfmisc_1(A_1619, B_1617))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.24/12.02  tff(c_64170, plain, (![B_1769, C_1770, A_1771]: (k1_xboole_0=B_1769 | v1_funct_2(C_1770, A_1771, B_1769) | k1_relset_1(A_1771, B_1769, C_1770)!=A_1771 | ~r1_tarski(k2_relat_1(C_1770), B_1769) | ~r1_tarski(k1_relat_1(C_1770), A_1771) | ~v1_relat_1(C_1770))), inference(resolution, [status(thm)], [c_46, c_60273])).
% 21.24/12.02  tff(c_70840, plain, (![A_1943, B_1944, A_1945]: (k1_xboole_0=A_1943 | v1_funct_2(B_1944, A_1945, A_1943) | k1_relset_1(A_1945, A_1943, B_1944)!=A_1945 | ~r1_tarski(k1_relat_1(B_1944), A_1945) | ~v5_relat_1(B_1944, A_1943) | ~v1_relat_1(B_1944))), inference(resolution, [status(thm)], [c_34, c_64170])).
% 21.24/12.02  tff(c_70892, plain, (![A_1943, A_1945]: (k1_xboole_0=A_1943 | v1_funct_2('#skF_4', A_1945, A_1943) | k1_relset_1(A_1945, A_1943, '#skF_4')!=A_1945 | ~r1_tarski('#skF_1', A_1945) | ~v5_relat_1('#skF_4', A_1943) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_60098, c_70840])).
% 21.24/12.02  tff(c_78061, plain, (![A_2116, A_2117]: (k1_xboole_0=A_2116 | v1_funct_2('#skF_4', A_2117, A_2116) | k1_relset_1(A_2117, A_2116, '#skF_4')!=A_2117 | ~r1_tarski('#skF_1', A_2117) | ~v5_relat_1('#skF_4', A_2116))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_70892])).
% 21.24/12.02  tff(c_70, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 21.24/12.02  tff(c_60, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_144])).
% 21.24/12.02  tff(c_72, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_60])).
% 21.24/12.02  tff(c_133, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_72])).
% 21.24/12.02  tff(c_78080, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_1', '#skF_1') | ~v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_78061, c_133])).
% 21.24/12.02  tff(c_78093, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_743, c_60226, c_62223, c_78080])).
% 21.24/12.02  tff(c_61191, plain, (![C_1680, A_1681]: (m1_subset_1(C_1680, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(C_1680), k1_xboole_0) | ~r1_tarski(k1_relat_1(C_1680), A_1681) | ~v1_relat_1(C_1680))), inference(superposition, [status(thm), theory('equality')], [c_14, c_59956])).
% 21.24/12.02  tff(c_64097, plain, (![B_1767, A_1768]: (m1_subset_1(B_1767, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k1_relat_1(B_1767), A_1768) | ~v5_relat_1(B_1767, k1_xboole_0) | ~v1_relat_1(B_1767))), inference(resolution, [status(thm)], [c_34, c_61191])).
% 21.24/12.02  tff(c_64131, plain, (![A_1768]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', A_1768) | ~v5_relat_1('#skF_4', k1_xboole_0) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_60098, c_64097])).
% 21.24/12.02  tff(c_64162, plain, (![A_1768]: (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_1', A_1768) | ~v5_relat_1('#skF_4', k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_64131])).
% 21.24/12.02  tff(c_64169, plain, (~v5_relat_1('#skF_4', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_64162])).
% 21.24/12.02  tff(c_78209, plain, (~v5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_78093, c_64169])).
% 21.24/12.02  tff(c_78301, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_743, c_78209])).
% 21.24/12.02  tff(c_78302, plain, (![A_1768]: (~r1_tarski('#skF_1', A_1768) | m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(splitRight, [status(thm)], [c_64162])).
% 21.24/12.02  tff(c_78637, plain, (![A_1768]: (~r1_tarski('#skF_1', A_1768))), inference(splitLeft, [status(thm)], [c_78302])).
% 21.24/12.02  tff(c_78640, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78637, c_60226])).
% 21.24/12.02  tff(c_78641, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_78302])).
% 21.24/12.02  tff(c_78708, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_78641, c_20])).
% 21.24/12.02  tff(c_78725, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60204, c_78708])).
% 21.24/12.02  tff(c_78726, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_60151])).
% 21.24/12.02  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 21.24/12.02  tff(c_78731, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_78726, c_4])).
% 21.24/12.02  tff(c_16, plain, (![B_8]: (k2_zfmisc_1(k1_xboole_0, B_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 21.24/12.02  tff(c_78778, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78731, c_78731, c_16])).
% 21.24/12.02  tff(c_123, plain, (![A_49, B_50]: (r1_tarski(A_49, B_50) | ~m1_subset_1(A_49, k1_zfmisc_1(B_50)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.24/12.02  tff(c_130, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_66, c_123])).
% 21.24/12.02  tff(c_79027, plain, (r1_tarski('#skF_4', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_78778, c_130])).
% 21.24/12.02  tff(c_595, plain, (![A_10]: (v1_xboole_0(A_10) | ~r1_tarski(A_10, k1_xboole_0))), inference(resolution, [status(thm)], [c_22, c_586])).
% 21.24/12.02  tff(c_79152, plain, (![A_2140]: (v1_xboole_0(A_2140) | ~r1_tarski(A_2140, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_78731, c_595])).
% 21.24/12.02  tff(c_79168, plain, (v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_79027, c_79152])).
% 21.24/12.02  tff(c_78780, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_78731, c_4])).
% 21.24/12.02  tff(c_79176, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_79168, c_78780])).
% 21.24/12.02  tff(c_109, plain, (![A_45, B_46]: (v1_relat_1(k2_zfmisc_1(A_45, B_46)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.24/12.02  tff(c_111, plain, (v1_relat_1(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_16, c_109])).
% 21.24/12.02  tff(c_18, plain, (![A_9]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 21.24/12.02  tff(c_219, plain, (![A_65]: (v4_relat_1(k1_xboole_0, A_65))), inference(resolution, [status(thm)], [c_18, c_199])).
% 21.24/12.02  tff(c_233, plain, (![B_69, A_70]: (r1_tarski(k1_relat_1(B_69), A_70) | ~v4_relat_1(B_69, A_70) | ~v1_relat_1(B_69))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.24/12.02  tff(c_10, plain, (![A_6]: (k1_xboole_0=A_6 | ~r1_tarski(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_42])).
% 21.24/12.02  tff(c_260, plain, (![B_78]: (k1_relat_1(B_78)=k1_xboole_0 | ~v4_relat_1(B_78, k1_xboole_0) | ~v1_relat_1(B_78))), inference(resolution, [status(thm)], [c_233, c_10])).
% 21.24/12.02  tff(c_268, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(k1_xboole_0)), inference(resolution, [status(thm)], [c_219, c_260])).
% 21.24/12.02  tff(c_272, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_111, c_268])).
% 21.24/12.02  tff(c_676, plain, (![A_122, B_123]: (k1_relset_1(A_122, B_123, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_18, c_665])).
% 21.24/12.02  tff(c_686, plain, (![A_122, B_123]: (k1_relset_1(A_122, B_123, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_272, c_676])).
% 21.24/12.02  tff(c_52, plain, (![C_39, B_38]: (v1_funct_2(C_39, k1_xboole_0, B_38) | k1_relset_1(k1_xboole_0, B_38, C_39)!=k1_xboole_0 | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_38))))), inference(cnfTransformation, [status(thm)], [f_124])).
% 21.24/12.02  tff(c_1140, plain, (![C_172, B_173]: (v1_funct_2(C_172, k1_xboole_0, B_173) | k1_relset_1(k1_xboole_0, B_173, C_172)!=k1_xboole_0 | ~m1_subset_1(C_172, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 21.24/12.02  tff(c_1146, plain, (![B_173]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_173) | k1_relset_1(k1_xboole_0, B_173, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_1140])).
% 21.24/12.02  tff(c_1150, plain, (![B_173]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_173))), inference(demodulation, [status(thm), theory('equality')], [c_686, c_1146])).
% 21.24/12.02  tff(c_78735, plain, (![B_173]: (v1_funct_2('#skF_1', '#skF_1', B_173))), inference(demodulation, [status(thm), theory('equality')], [c_78731, c_78731, c_1150])).
% 21.24/12.02  tff(c_79200, plain, (![B_173]: (v1_funct_2('#skF_4', '#skF_4', B_173))), inference(demodulation, [status(thm), theory('equality')], [c_79176, c_79176, c_78735])).
% 21.24/12.02  tff(c_79221, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_79176, c_133])).
% 21.24/12.02  tff(c_79574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79200, c_79221])).
% 21.24/12.02  tff(c_79575, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_72])).
% 21.24/12.02  tff(c_80748, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_80728, c_79575])).
% 21.24/12.02  tff(c_80768, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_79610, c_80748])).
% 21.24/12.02  tff(c_80770, plain, (~r1_tarski(k1_relat_1('#skF_4'), '#skF_1')), inference(splitLeft, [status(thm)], [c_80768])).
% 21.24/12.02  tff(c_80776, plain, (~v4_relat_1('#skF_4', '#skF_1') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_30, c_80770])).
% 21.24/12.02  tff(c_80783, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79610, c_79650, c_80776])).
% 21.24/12.02  tff(c_80784, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(splitRight, [status(thm)], [c_80768])).
% 21.24/12.02  tff(c_80839, plain, (~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_79743, c_80784])).
% 21.24/12.02  tff(c_80849, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_79610, c_79697, c_80839])).
% 21.24/12.02  tff(c_80850, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_62])).
% 21.24/12.02  tff(c_80853, plain, (![B_8]: (k2_zfmisc_1('#skF_1', B_8)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80850, c_80850, c_16])).
% 21.24/12.02  tff(c_80851, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_62])).
% 21.24/12.02  tff(c_80862, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_80850, c_80851])).
% 21.24/12.02  tff(c_80898, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80853, c_80862, c_66])).
% 21.24/12.02  tff(c_80917, plain, (![A_2299, B_2300]: (r1_tarski(A_2299, B_2300) | ~m1_subset_1(A_2299, k1_zfmisc_1(B_2300)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 21.24/12.02  tff(c_80926, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_80898, c_80917])).
% 21.24/12.02  tff(c_80907, plain, (![A_6]: (A_6='#skF_1' | ~r1_tarski(A_6, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_80850, c_80850, c_10])).
% 21.24/12.02  tff(c_80930, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_80926, c_80907])).
% 21.24/12.02  tff(c_80854, plain, (![A_7]: (k2_zfmisc_1(A_7, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_80850, c_80850, c_14])).
% 21.24/12.02  tff(c_80893, plain, (![A_2293, B_2294]: (v1_relat_1(k2_zfmisc_1(A_2293, B_2294)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 21.24/12.02  tff(c_80895, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_80854, c_80893])).
% 21.24/12.02  tff(c_80940, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_80930, c_80895])).
% 21.24/12.02  tff(c_80852, plain, (![A_9]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_80850, c_18])).
% 21.24/12.02  tff(c_80939, plain, (![A_9]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_9)))), inference(demodulation, [status(thm), theory('equality')], [c_80930, c_80852])).
% 21.24/12.02  tff(c_81050, plain, (![C_2318, A_2319, B_2320]: (v4_relat_1(C_2318, A_2319) | ~m1_subset_1(C_2318, k1_zfmisc_1(k2_zfmisc_1(A_2319, B_2320))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 21.24/12.02  tff(c_81065, plain, (![A_2319]: (v4_relat_1('#skF_4', A_2319))), inference(resolution, [status(thm)], [c_80939, c_81050])).
% 21.24/12.02  tff(c_81079, plain, (![B_2326, A_2327]: (r1_tarski(k1_relat_1(B_2326), A_2327) | ~v4_relat_1(B_2326, A_2327) | ~v1_relat_1(B_2326))), inference(cnfTransformation, [status(thm)], [f_73])).
% 21.24/12.02  tff(c_80936, plain, (![A_6]: (A_6='#skF_4' | ~r1_tarski(A_6, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80930, c_80930, c_80907])).
% 21.24/12.02  tff(c_81111, plain, (![B_2331]: (k1_relat_1(B_2331)='#skF_4' | ~v4_relat_1(B_2331, '#skF_4') | ~v1_relat_1(B_2331))), inference(resolution, [status(thm)], [c_81079, c_80936])).
% 21.24/12.02  tff(c_81119, plain, (k1_relat_1('#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_81065, c_81111])).
% 21.24/12.02  tff(c_81123, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80940, c_81119])).
% 21.24/12.02  tff(c_81353, plain, (![A_2366, B_2367, C_2368]: (k1_relset_1(A_2366, B_2367, C_2368)=k1_relat_1(C_2368) | ~m1_subset_1(C_2368, k1_zfmisc_1(k2_zfmisc_1(A_2366, B_2367))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 21.24/12.02  tff(c_81357, plain, (![A_2366, B_2367]: (k1_relset_1(A_2366, B_2367, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_80939, c_81353])).
% 21.24/12.02  tff(c_81369, plain, (![A_2366, B_2367]: (k1_relset_1(A_2366, B_2367, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_81123, c_81357])).
% 21.24/12.02  tff(c_80947, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_80930, c_80850])).
% 21.24/12.02  tff(c_76, plain, (![C_39, B_38]: (v1_funct_2(C_39, k1_xboole_0, B_38) | k1_relset_1(k1_xboole_0, B_38, C_39)!=k1_xboole_0 | ~m1_subset_1(C_39, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 21.24/12.02  tff(c_81798, plain, (![C_2416, B_2417]: (v1_funct_2(C_2416, '#skF_4', B_2417) | k1_relset_1('#skF_4', B_2417, C_2416)!='#skF_4' | ~m1_subset_1(C_2416, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_80947, c_80947, c_80947, c_80947, c_76])).
% 21.24/12.02  tff(c_81801, plain, (![B_2417]: (v1_funct_2('#skF_4', '#skF_4', B_2417) | k1_relset_1('#skF_4', B_2417, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_80939, c_81798])).
% 21.24/12.02  tff(c_81807, plain, (![B_2417]: (v1_funct_2('#skF_4', '#skF_4', B_2417))), inference(demodulation, [status(thm), theory('equality')], [c_81369, c_81801])).
% 21.24/12.02  tff(c_80932, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80898, c_80853, c_72])).
% 21.24/12.02  tff(c_80933, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_80930, c_80932])).
% 21.24/12.02  tff(c_81812, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_81807, c_80933])).
% 21.24/12.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 21.24/12.02  
% 21.24/12.02  Inference rules
% 21.24/12.02  ----------------------
% 21.24/12.02  #Ref     : 0
% 21.24/12.02  #Sup     : 18163
% 21.24/12.02  #Fact    : 0
% 21.24/12.02  #Define  : 0
% 21.24/12.02  #Split   : 139
% 21.24/12.02  #Chain   : 0
% 21.24/12.02  #Close   : 0
% 21.24/12.02  
% 21.24/12.02  Ordering : KBO
% 21.24/12.02  
% 21.24/12.02  Simplification rules
% 21.24/12.02  ----------------------
% 21.24/12.02  #Subsume      : 12423
% 21.24/12.02  #Demod        : 11387
% 21.24/12.02  #Tautology    : 3813
% 21.24/12.02  #SimpNegUnit  : 1501
% 21.24/12.02  #BackRed      : 1783
% 21.24/12.02  
% 21.24/12.02  #Partial instantiations: 0
% 21.24/12.02  #Strategies tried      : 1
% 21.24/12.02  
% 21.24/12.02  Timing (in seconds)
% 21.24/12.02  ----------------------
% 21.24/12.02  Preprocessing        : 0.36
% 21.24/12.02  Parsing              : 0.20
% 21.24/12.02  CNF conversion       : 0.02
% 21.24/12.02  Main loop            : 10.79
% 21.24/12.02  Inferencing          : 2.11
% 21.24/12.02  Reduction            : 3.25
% 21.24/12.02  Demodulation         : 2.21
% 21.24/12.02  BG Simplification    : 0.23
% 21.24/12.02  Subsumption          : 4.43
% 21.24/12.02  Abstraction          : 0.35
% 21.24/12.02  MUC search           : 0.00
% 21.24/12.02  Cooper               : 0.00
% 21.24/12.02  Total                : 11.22
% 21.24/12.02  Index Insertion      : 0.00
% 21.24/12.02  Index Deletion       : 0.00
% 21.24/12.02  Index Matching       : 0.00
% 21.24/12.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
