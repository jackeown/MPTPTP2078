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
% DateTime   : Thu Dec  3 09:56:09 EST 2020

% Result     : Theorem 4.33s
% Output     : CNFRefutation 4.33s
% Verified   : 
% Statistics : Number of formulae       :  113 ( 307 expanded)
%              Number of leaves         :   36 ( 115 expanded)
%              Depth                    :   16
%              Number of atoms          :  126 ( 407 expanded)
%              Number of equality atoms :   74 ( 233 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_45,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_82,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_18,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_233,plain,(
    ! [A_48,B_49] :
      ( k3_xboole_0(A_48,B_49) = A_48
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_255,plain,(
    ! [A_51] : k3_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_233])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_264,plain,(
    ! [A_51] : k3_xboole_0(A_51,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_4])).

tff(c_14,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [A_17] : k4_xboole_0(k1_xboole_0,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_415,plain,(
    ! [A_61,B_62] : k5_xboole_0(A_61,k4_xboole_0(B_62,A_61)) = k2_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_424,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k2_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_415])).

tff(c_427,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_424])).

tff(c_342,plain,(
    ! [A_57,B_58] : k5_xboole_0(A_57,k3_xboole_0(A_57,B_58)) = k4_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_351,plain,(
    ! [A_51] : k5_xboole_0(A_51,k1_xboole_0) = k4_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_342])).

tff(c_428,plain,(
    ! [A_51] : k4_xboole_0(A_51,k1_xboole_0) = A_51 ),
    inference(demodulation,[status(thm),theory(equality)],[c_427,c_351])).

tff(c_596,plain,(
    ! [A_77,B_78] : k4_xboole_0(A_77,k4_xboole_0(A_77,B_78)) = k3_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_621,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k3_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_428,c_596])).

tff(c_633,plain,(
    ! [A_51] : k4_xboole_0(A_51,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_621])).

tff(c_48,plain,(
    ! [A_27] : k2_subset_1(A_27) = A_27 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_62,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_63,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_62])).

tff(c_146,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_63])).

tff(c_54,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_147,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_54])).

tff(c_674,plain,(
    ! [A_80,B_81] :
      ( k4_xboole_0(A_80,B_81) = k3_subset_1(A_80,B_81)
      | ~ m1_subset_1(B_81,k1_zfmisc_1(A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_684,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_147,c_674])).

tff(c_688,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_633,c_684])).

tff(c_56,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_56])).

tff(c_226,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_146,c_64])).

tff(c_716,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_688,c_226])).

tff(c_719,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_716])).

tff(c_721,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_52,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1348,plain,(
    ! [B_123,A_124] :
      ( r2_hidden(B_123,A_124)
      | ~ m1_subset_1(B_123,A_124)
      | v1_xboole_0(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_28,plain,(
    ! [C_24,A_20] :
      ( r1_tarski(C_24,A_20)
      | ~ r2_hidden(C_24,k1_zfmisc_1(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1355,plain,(
    ! [B_123,A_20] :
      ( r1_tarski(B_123,A_20)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_20))
      | v1_xboole_0(k1_zfmisc_1(A_20)) ) ),
    inference(resolution,[status(thm)],[c_1348,c_28])).

tff(c_1360,plain,(
    ! [B_125,A_126] :
      ( r1_tarski(B_125,A_126)
      | ~ m1_subset_1(B_125,k1_zfmisc_1(A_126)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1355])).

tff(c_1373,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_54,c_1360])).

tff(c_930,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k4_xboole_0(B_100,A_99)) = k2_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_939,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k2_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_930])).

tff(c_942,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_939])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_795,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_821,plain,(
    ! [A_89] : k3_xboole_0(k1_xboole_0,A_89) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_795])).

tff(c_830,plain,(
    ! [A_89] : k3_xboole_0(A_89,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_821,c_4])).

tff(c_956,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_968,plain,(
    ! [A_89] : k5_xboole_0(A_89,k1_xboole_0) = k4_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_830,c_956])).

tff(c_986,plain,(
    ! [A_89] : k4_xboole_0(A_89,k1_xboole_0) = A_89 ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_968])).

tff(c_1083,plain,(
    ! [A_107,B_108] : k4_xboole_0(A_107,k4_xboole_0(A_107,B_108)) = k3_xboole_0(A_107,B_108) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1108,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k3_xboole_0(A_89,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_986,c_1083])).

tff(c_1120,plain,(
    ! [A_89] : k4_xboole_0(A_89,A_89) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_830,c_1108])).

tff(c_10,plain,(
    ! [B_6] : r1_tarski(B_6,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_810,plain,(
    ! [B_6] : k3_xboole_0(B_6,B_6) = B_6 ),
    inference(resolution,[status(thm)],[c_10,c_795])).

tff(c_977,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k4_xboole_0(B_6,B_6) ),
    inference(superposition,[status(thm),theory(equality)],[c_810,c_956])).

tff(c_1123,plain,(
    ! [B_6] : k5_xboole_0(B_6,B_6) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1120,c_977])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1382,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1373,c_16])).

tff(c_12,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1392,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1382,c_12])).

tff(c_1397,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1123,c_1392])).

tff(c_26,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1405,plain,(
    k5_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1397,c_26])).

tff(c_1412,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_942,c_2,c_1405])).

tff(c_1478,plain,(
    ! [A_129,B_130] :
      ( k4_xboole_0(A_129,B_130) = k3_subset_1(A_129,B_130)
      | ~ m1_subset_1(B_130,k1_zfmisc_1(A_129)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1491,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_1478])).

tff(c_1498,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1491,c_26])).

tff(c_1505,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1412,c_1498])).

tff(c_720,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_63])).

tff(c_808,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_720,c_795])).

tff(c_1419,plain,(
    ! [A_127,B_128] : k5_xboole_0(A_127,k3_xboole_0(B_128,A_127)) = k4_xboole_0(A_127,B_128) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_956])).

tff(c_1453,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_808,c_1419])).

tff(c_4217,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1505,c_1453])).

tff(c_20,plain,(
    ! [A_13,B_14] : r1_tarski(k4_xboole_0(A_13,B_14),A_13) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1283,plain,(
    ! [B_116,A_117] :
      ( B_116 = A_117
      | ~ r1_tarski(B_116,A_117)
      | ~ r1_tarski(A_117,B_116) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1299,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = A_13
      | ~ r1_tarski(A_13,k4_xboole_0(A_13,B_14)) ) ),
    inference(resolution,[status(thm)],[c_20,c_1283])).

tff(c_4224,plain,
    ( k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_4217,c_1299])).

tff(c_4253,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1373,c_4217,c_4224])).

tff(c_4255,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_721,c_4253])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:36:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.33/1.79  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.80  
% 4.33/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.80  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.33/1.80  
% 4.33/1.80  %Foreground sorts:
% 4.33/1.80  
% 4.33/1.80  
% 4.33/1.80  %Background operators:
% 4.33/1.80  
% 4.33/1.80  
% 4.33/1.80  %Foreground operators:
% 4.33/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.33/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.33/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.33/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.33/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.33/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.33/1.80  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.33/1.80  tff('#skF_3', type, '#skF_3': $i).
% 4.33/1.80  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.33/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.33/1.80  tff('#skF_4', type, '#skF_4': $i).
% 4.33/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.33/1.80  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.33/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.33/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.33/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.33/1.80  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.33/1.80  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.33/1.80  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.33/1.80  
% 4.33/1.82  tff(f_45, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 4.33/1.82  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.33/1.82  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.33/1.82  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 4.33/1.82  tff(f_51, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 4.33/1.82  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.33/1.82  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.33/1.82  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.33/1.82  tff(f_75, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 4.33/1.82  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 4.33/1.82  tff(f_79, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.33/1.82  tff(f_82, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.33/1.82  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 4.33/1.82  tff(f_60, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.33/1.82  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.33/1.82  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.33/1.82  tff(f_47, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.33/1.82  tff(c_18, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.33/1.82  tff(c_233, plain, (![A_48, B_49]: (k3_xboole_0(A_48, B_49)=A_48 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/1.82  tff(c_255, plain, (![A_51]: (k3_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_233])).
% 4.33/1.82  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.33/1.82  tff(c_264, plain, (![A_51]: (k3_xboole_0(A_51, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_255, c_4])).
% 4.33/1.82  tff(c_14, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.33/1.82  tff(c_24, plain, (![A_17]: (k4_xboole_0(k1_xboole_0, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.33/1.82  tff(c_415, plain, (![A_61, B_62]: (k5_xboole_0(A_61, k4_xboole_0(B_62, A_61))=k2_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.33/1.82  tff(c_424, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k2_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_415])).
% 4.33/1.82  tff(c_427, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_424])).
% 4.33/1.82  tff(c_342, plain, (![A_57, B_58]: (k5_xboole_0(A_57, k3_xboole_0(A_57, B_58))=k4_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/1.82  tff(c_351, plain, (![A_51]: (k5_xboole_0(A_51, k1_xboole_0)=k4_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_264, c_342])).
% 4.33/1.82  tff(c_428, plain, (![A_51]: (k4_xboole_0(A_51, k1_xboole_0)=A_51)), inference(demodulation, [status(thm), theory('equality')], [c_427, c_351])).
% 4.33/1.82  tff(c_596, plain, (![A_77, B_78]: (k4_xboole_0(A_77, k4_xboole_0(A_77, B_78))=k3_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.33/1.82  tff(c_621, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k3_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_428, c_596])).
% 4.33/1.82  tff(c_633, plain, (![A_51]: (k4_xboole_0(A_51, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_264, c_621])).
% 4.33/1.82  tff(c_48, plain, (![A_27]: (k2_subset_1(A_27)=A_27)), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.33/1.82  tff(c_62, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.33/1.82  tff(c_63, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_48, c_62])).
% 4.33/1.82  tff(c_146, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_63])).
% 4.33/1.82  tff(c_54, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.33/1.82  tff(c_147, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_146, c_54])).
% 4.33/1.82  tff(c_674, plain, (![A_80, B_81]: (k4_xboole_0(A_80, B_81)=k3_subset_1(A_80, B_81) | ~m1_subset_1(B_81, k1_zfmisc_1(A_80)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.33/1.82  tff(c_684, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_147, c_674])).
% 4.33/1.82  tff(c_688, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_633, c_684])).
% 4.33/1.82  tff(c_56, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.33/1.82  tff(c_64, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_56])).
% 4.33/1.82  tff(c_226, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_146, c_146, c_64])).
% 4.33/1.82  tff(c_716, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_688, c_226])).
% 4.33/1.82  tff(c_719, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_18, c_716])).
% 4.33/1.82  tff(c_721, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_63])).
% 4.33/1.82  tff(c_52, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.33/1.82  tff(c_1348, plain, (![B_123, A_124]: (r2_hidden(B_123, A_124) | ~m1_subset_1(B_123, A_124) | v1_xboole_0(A_124))), inference(cnfTransformation, [status(thm)], [f_73])).
% 4.33/1.82  tff(c_28, plain, (![C_24, A_20]: (r1_tarski(C_24, A_20) | ~r2_hidden(C_24, k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.33/1.82  tff(c_1355, plain, (![B_123, A_20]: (r1_tarski(B_123, A_20) | ~m1_subset_1(B_123, k1_zfmisc_1(A_20)) | v1_xboole_0(k1_zfmisc_1(A_20)))), inference(resolution, [status(thm)], [c_1348, c_28])).
% 4.33/1.82  tff(c_1360, plain, (![B_125, A_126]: (r1_tarski(B_125, A_126) | ~m1_subset_1(B_125, k1_zfmisc_1(A_126)))), inference(negUnitSimplification, [status(thm)], [c_52, c_1355])).
% 4.33/1.82  tff(c_1373, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_54, c_1360])).
% 4.33/1.82  tff(c_930, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k4_xboole_0(B_100, A_99))=k2_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.33/1.82  tff(c_939, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k2_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_930])).
% 4.33/1.82  tff(c_942, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_939])).
% 4.33/1.82  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.33/1.82  tff(c_795, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/1.82  tff(c_821, plain, (![A_89]: (k3_xboole_0(k1_xboole_0, A_89)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_795])).
% 4.33/1.82  tff(c_830, plain, (![A_89]: (k3_xboole_0(A_89, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_821, c_4])).
% 4.33/1.82  tff(c_956, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/1.82  tff(c_968, plain, (![A_89]: (k5_xboole_0(A_89, k1_xboole_0)=k4_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_830, c_956])).
% 4.33/1.82  tff(c_986, plain, (![A_89]: (k4_xboole_0(A_89, k1_xboole_0)=A_89)), inference(demodulation, [status(thm), theory('equality')], [c_942, c_968])).
% 4.33/1.82  tff(c_1083, plain, (![A_107, B_108]: (k4_xboole_0(A_107, k4_xboole_0(A_107, B_108))=k3_xboole_0(A_107, B_108))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.33/1.82  tff(c_1108, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k3_xboole_0(A_89, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_986, c_1083])).
% 4.33/1.82  tff(c_1120, plain, (![A_89]: (k4_xboole_0(A_89, A_89)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_830, c_1108])).
% 4.33/1.82  tff(c_10, plain, (![B_6]: (r1_tarski(B_6, B_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.33/1.82  tff(c_810, plain, (![B_6]: (k3_xboole_0(B_6, B_6)=B_6)), inference(resolution, [status(thm)], [c_10, c_795])).
% 4.33/1.82  tff(c_977, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k4_xboole_0(B_6, B_6))), inference(superposition, [status(thm), theory('equality')], [c_810, c_956])).
% 4.33/1.82  tff(c_1123, plain, (![B_6]: (k5_xboole_0(B_6, B_6)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1120, c_977])).
% 4.33/1.82  tff(c_16, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.33/1.82  tff(c_1382, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_1373, c_16])).
% 4.33/1.82  tff(c_12, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.33/1.82  tff(c_1392, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1382, c_12])).
% 4.33/1.82  tff(c_1397, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_1123, c_1392])).
% 4.33/1.82  tff(c_26, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.33/1.82  tff(c_1405, plain, (k5_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1397, c_26])).
% 4.33/1.82  tff(c_1412, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_942, c_2, c_1405])).
% 4.33/1.82  tff(c_1478, plain, (![A_129, B_130]: (k4_xboole_0(A_129, B_130)=k3_subset_1(A_129, B_130) | ~m1_subset_1(B_130, k1_zfmisc_1(A_129)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 4.33/1.82  tff(c_1491, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_1478])).
% 4.33/1.82  tff(c_1498, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1491, c_26])).
% 4.33/1.82  tff(c_1505, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1412, c_1498])).
% 4.33/1.82  tff(c_720, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_63])).
% 4.33/1.82  tff(c_808, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_720, c_795])).
% 4.33/1.82  tff(c_1419, plain, (![A_127, B_128]: (k5_xboole_0(A_127, k3_xboole_0(B_128, A_127))=k4_xboole_0(A_127, B_128))), inference(superposition, [status(thm), theory('equality')], [c_4, c_956])).
% 4.33/1.82  tff(c_1453, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_808, c_1419])).
% 4.33/1.82  tff(c_4217, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1505, c_1453])).
% 4.33/1.82  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(k4_xboole_0(A_13, B_14), A_13))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.33/1.82  tff(c_1283, plain, (![B_116, A_117]: (B_116=A_117 | ~r1_tarski(B_116, A_117) | ~r1_tarski(A_117, B_116))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.33/1.82  tff(c_1299, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=A_13 | ~r1_tarski(A_13, k4_xboole_0(A_13, B_14)))), inference(resolution, [status(thm)], [c_20, c_1283])).
% 4.33/1.82  tff(c_4224, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_4217, c_1299])).
% 4.33/1.82  tff(c_4253, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1373, c_4217, c_4224])).
% 4.33/1.82  tff(c_4255, plain, $false, inference(negUnitSimplification, [status(thm)], [c_721, c_4253])).
% 4.33/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.33/1.82  
% 4.33/1.82  Inference rules
% 4.33/1.82  ----------------------
% 4.33/1.82  #Ref     : 0
% 4.33/1.82  #Sup     : 1013
% 4.33/1.82  #Fact    : 0
% 4.33/1.82  #Define  : 0
% 4.33/1.82  #Split   : 3
% 4.33/1.82  #Chain   : 0
% 4.33/1.82  #Close   : 0
% 4.33/1.82  
% 4.33/1.82  Ordering : KBO
% 4.33/1.82  
% 4.33/1.82  Simplification rules
% 4.33/1.82  ----------------------
% 4.33/1.82  #Subsume      : 36
% 4.33/1.82  #Demod        : 1051
% 4.33/1.82  #Tautology    : 828
% 4.33/1.82  #SimpNegUnit  : 7
% 4.33/1.82  #BackRed      : 5
% 4.33/1.82  
% 4.33/1.82  #Partial instantiations: 0
% 4.33/1.82  #Strategies tried      : 1
% 4.33/1.82  
% 4.33/1.82  Timing (in seconds)
% 4.33/1.82  ----------------------
% 4.33/1.82  Preprocessing        : 0.32
% 4.33/1.82  Parsing              : 0.17
% 4.33/1.82  CNF conversion       : 0.02
% 4.33/1.82  Main loop            : 0.73
% 4.33/1.82  Inferencing          : 0.24
% 4.33/1.82  Reduction            : 0.32
% 4.33/1.82  Demodulation         : 0.26
% 4.33/1.82  BG Simplification    : 0.02
% 4.33/1.82  Subsumption          : 0.10
% 4.33/1.82  Abstraction          : 0.04
% 4.33/1.82  MUC search           : 0.00
% 4.33/1.82  Cooper               : 0.00
% 4.33/1.82  Total                : 1.09
% 4.33/1.82  Index Insertion      : 0.00
% 4.33/1.82  Index Deletion       : 0.00
% 4.33/1.82  Index Matching       : 0.00
% 4.33/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------
