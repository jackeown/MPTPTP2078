%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:57 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 455 expanded)
%              Number of leaves         :   29 ( 155 expanded)
%              Depth                    :   11
%              Number of atoms          :  131 ( 923 expanded)
%              Number of equality atoms :   41 ( 256 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_101,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_91,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_73,plain,(
    ! [B_41,A_42] :
      ( v1_xboole_0(B_41)
      | ~ m1_subset_1(B_41,k1_zfmisc_1(A_42))
      | ~ v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_180,plain,(
    ! [A_60,B_61] :
      ( v1_xboole_0(A_60)
      | ~ v1_xboole_0(B_61)
      | ~ r1_tarski(A_60,B_61) ) ),
    inference(resolution,[status(thm)],[c_26,c_73])).

tff(c_213,plain,
    ( v1_xboole_0('#skF_2')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_180])).

tff(c_214,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_213])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_363,plain,(
    ! [A_88,B_89] :
      ( k6_setfam_1(A_88,B_89) = k1_setfam_1(B_89)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(k1_zfmisc_1(A_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_379,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_363])).

tff(c_713,plain,(
    ! [A_114,B_115] :
      ( k8_setfam_1(A_114,B_115) = k6_setfam_1(A_114,B_115)
      | k1_xboole_0 = B_115
      | ~ m1_subset_1(B_115,k1_zfmisc_1(k1_zfmisc_1(A_114))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_728,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_713])).

tff(c_741,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_379,c_728])).

tff(c_842,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_741])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_380,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_363])).

tff(c_731,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_713])).

tff(c_743,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_380,c_731])).

tff(c_1158,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_743])).

tff(c_1159,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1158])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_10,plain,(
    ! [A_9,B_10] : r1_xboole_0(k4_xboole_0(A_9,B_10),B_10) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_89,plain,(
    ! [A_11] :
      ( v1_xboole_0(k1_xboole_0)
      | ~ v1_xboole_0(A_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_73])).

tff(c_95,plain,(
    ! [A_11] : ~ v1_xboole_0(A_11) ),
    inference(splitLeft,[status(thm)],[c_89])).

tff(c_8,plain,(
    ! [B_8,A_7] :
      ( ~ r1_xboole_0(B_8,A_7)
      | ~ r1_tarski(B_8,A_7)
      | v1_xboole_0(B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,(
    ! [B_46,A_47] :
      ( ~ r1_xboole_0(B_46,A_47)
      | ~ r1_tarski(B_46,A_47) ) ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_8])).

tff(c_106,plain,(
    ! [A_48,B_49] : ~ r1_tarski(k4_xboole_0(A_48,B_49),B_49) ),
    inference(resolution,[status(thm)],[c_10,c_101])).

tff(c_111,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_106])).

tff(c_112,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_89])).

tff(c_854,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_112])).

tff(c_1170,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1159,c_854])).

tff(c_1175,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1170])).

tff(c_1176,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_1158])).

tff(c_16,plain,(
    ! [A_15] :
      ( k8_setfam_1(A_15,k1_xboole_0) = A_15
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_40,plain,(
    ! [A_15] : k8_setfam_1(A_15,k1_xboole_0) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_856,plain,(
    ! [A_15] : k8_setfam_1(A_15,'#skF_2') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_842,c_40])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_921,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_856,c_32])).

tff(c_1178,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1176,c_921])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( m1_subset_1(k8_setfam_1(A_17,B_18),k1_zfmisc_1(A_17))
      | ~ m1_subset_1(B_18,k1_zfmisc_1(k1_zfmisc_1(A_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1182,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1176,c_20])).

tff(c_1186,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_1182])).

tff(c_24,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1195,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_1186,c_24])).

tff(c_1201,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1178,c_1195])).

tff(c_1203,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_30,plain,(
    ! [B_27,A_26] :
      ( r1_tarski(k1_setfam_1(B_27),k1_setfam_1(A_26))
      | k1_xboole_0 = A_26
      | ~ r1_tarski(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_1392,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_743])).

tff(c_1407,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1392,c_112])).

tff(c_1413,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_214,c_1407])).

tff(c_1414,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_743])).

tff(c_1202,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_741])).

tff(c_1204,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1202,c_32])).

tff(c_1416,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1414,c_1204])).

tff(c_1428,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1416])).

tff(c_1431,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1428])).

tff(c_1433,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1203,c_1431])).

tff(c_1435,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1443,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1435,c_2])).

tff(c_1434,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_213])).

tff(c_1439,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1434,c_2])).

tff(c_1456,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1443,c_1439])).

tff(c_1449,plain,(
    ! [A_11] : m1_subset_1('#skF_2',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_12])).

tff(c_1506,plain,(
    ! [A_11] : m1_subset_1('#skF_3',k1_zfmisc_1(A_11)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1449])).

tff(c_1448,plain,(
    ! [A_15] : k8_setfam_1(A_15,'#skF_2') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1439,c_40])).

tff(c_1496,plain,(
    ! [A_15] : k8_setfam_1(A_15,'#skF_3') = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_1448])).

tff(c_1701,plain,(
    ! [A_170,B_171] :
      ( m1_subset_1(k8_setfam_1(A_170,B_171),k1_zfmisc_1(A_170))
      | ~ m1_subset_1(B_171,k1_zfmisc_1(k1_zfmisc_1(A_170))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_1716,plain,(
    ! [A_15] :
      ( m1_subset_1(A_15,k1_zfmisc_1(A_15))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1(A_15))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1496,c_1701])).

tff(c_1723,plain,(
    ! [A_172] : m1_subset_1(A_172,k1_zfmisc_1(A_172)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1506,c_1716])).

tff(c_1739,plain,(
    ! [A_172] : r1_tarski(A_172,A_172) ),
    inference(resolution,[status(thm)],[c_1723,c_24])).

tff(c_1466,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1456,c_32])).

tff(c_1621,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1496,c_1496,c_1466])).

tff(c_1742,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1739,c_1621])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:01:17 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.59  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.60  
% 3.24/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.60  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.60  
% 3.24/1.60  %Foreground sorts:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Background operators:
% 3.24/1.60  
% 3.24/1.60  
% 3.24/1.60  %Foreground operators:
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.24/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.60  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.24/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.60  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.60  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.60  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.60  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.60  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.60  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.24/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.24/1.60  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.60  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.24/1.60  
% 3.24/1.62  tff(f_101, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.24/1.62  tff(f_79, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.24/1.62  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.24/1.62  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.24/1.62  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.24/1.62  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.24/1.62  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.24/1.62  tff(f_49, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.24/1.62  tff(f_45, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.24/1.62  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.24/1.62  tff(f_91, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.24/1.62  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.24/1.62  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.24/1.62  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.62  tff(c_73, plain, (![B_41, A_42]: (v1_xboole_0(B_41) | ~m1_subset_1(B_41, k1_zfmisc_1(A_42)) | ~v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.24/1.62  tff(c_180, plain, (![A_60, B_61]: (v1_xboole_0(A_60) | ~v1_xboole_0(B_61) | ~r1_tarski(A_60, B_61))), inference(resolution, [status(thm)], [c_26, c_73])).
% 3.24/1.62  tff(c_213, plain, (v1_xboole_0('#skF_2') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_34, c_180])).
% 3.24/1.62  tff(c_214, plain, (~v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_213])).
% 3.24/1.62  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.24/1.62  tff(c_363, plain, (![A_88, B_89]: (k6_setfam_1(A_88, B_89)=k1_setfam_1(B_89) | ~m1_subset_1(B_89, k1_zfmisc_1(k1_zfmisc_1(A_88))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.24/1.62  tff(c_379, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_363])).
% 3.24/1.62  tff(c_713, plain, (![A_114, B_115]: (k8_setfam_1(A_114, B_115)=k6_setfam_1(A_114, B_115) | k1_xboole_0=B_115 | ~m1_subset_1(B_115, k1_zfmisc_1(k1_zfmisc_1(A_114))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.62  tff(c_728, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_713])).
% 3.24/1.62  tff(c_741, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_379, c_728])).
% 3.24/1.62  tff(c_842, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_741])).
% 3.24/1.62  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.24/1.62  tff(c_380, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_363])).
% 3.24/1.62  tff(c_731, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_713])).
% 3.24/1.62  tff(c_743, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_380, c_731])).
% 3.24/1.62  tff(c_1158, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_842, c_743])).
% 3.24/1.62  tff(c_1159, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1158])).
% 3.24/1.62  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.62  tff(c_10, plain, (![A_9, B_10]: (r1_xboole_0(k4_xboole_0(A_9, B_10), B_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.24/1.62  tff(c_12, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.62  tff(c_89, plain, (![A_11]: (v1_xboole_0(k1_xboole_0) | ~v1_xboole_0(A_11))), inference(resolution, [status(thm)], [c_12, c_73])).
% 3.24/1.62  tff(c_95, plain, (![A_11]: (~v1_xboole_0(A_11))), inference(splitLeft, [status(thm)], [c_89])).
% 3.24/1.62  tff(c_8, plain, (![B_8, A_7]: (~r1_xboole_0(B_8, A_7) | ~r1_tarski(B_8, A_7) | v1_xboole_0(B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.24/1.62  tff(c_101, plain, (![B_46, A_47]: (~r1_xboole_0(B_46, A_47) | ~r1_tarski(B_46, A_47))), inference(negUnitSimplification, [status(thm)], [c_95, c_8])).
% 3.24/1.62  tff(c_106, plain, (![A_48, B_49]: (~r1_tarski(k4_xboole_0(A_48, B_49), B_49))), inference(resolution, [status(thm)], [c_10, c_101])).
% 3.24/1.62  tff(c_111, plain, $false, inference(resolution, [status(thm)], [c_6, c_106])).
% 3.24/1.62  tff(c_112, plain, (v1_xboole_0(k1_xboole_0)), inference(splitRight, [status(thm)], [c_89])).
% 3.24/1.62  tff(c_854, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_842, c_112])).
% 3.24/1.62  tff(c_1170, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1159, c_854])).
% 3.24/1.62  tff(c_1175, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_1170])).
% 3.24/1.62  tff(c_1176, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_1158])).
% 3.24/1.62  tff(c_16, plain, (![A_15]: (k8_setfam_1(A_15, k1_xboole_0)=A_15 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.24/1.62  tff(c_40, plain, (![A_15]: (k8_setfam_1(A_15, k1_xboole_0)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 3.24/1.62  tff(c_856, plain, (![A_15]: (k8_setfam_1(A_15, '#skF_2')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_842, c_40])).
% 3.24/1.62  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.24/1.62  tff(c_921, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_856, c_32])).
% 3.24/1.62  tff(c_1178, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1176, c_921])).
% 3.24/1.62  tff(c_20, plain, (![A_17, B_18]: (m1_subset_1(k8_setfam_1(A_17, B_18), k1_zfmisc_1(A_17)) | ~m1_subset_1(B_18, k1_zfmisc_1(k1_zfmisc_1(A_17))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.24/1.62  tff(c_1182, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_1176, c_20])).
% 3.24/1.62  tff(c_1186, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_1182])).
% 3.24/1.62  tff(c_24, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.24/1.62  tff(c_1195, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_1186, c_24])).
% 3.24/1.62  tff(c_1201, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1178, c_1195])).
% 3.24/1.62  tff(c_1203, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_741])).
% 3.24/1.62  tff(c_30, plain, (![B_27, A_26]: (r1_tarski(k1_setfam_1(B_27), k1_setfam_1(A_26)) | k1_xboole_0=A_26 | ~r1_tarski(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.24/1.62  tff(c_1392, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_743])).
% 3.24/1.62  tff(c_1407, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1392, c_112])).
% 3.24/1.62  tff(c_1413, plain, $false, inference(negUnitSimplification, [status(thm)], [c_214, c_1407])).
% 3.24/1.62  tff(c_1414, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_743])).
% 3.24/1.62  tff(c_1202, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_741])).
% 3.24/1.62  tff(c_1204, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1202, c_32])).
% 3.24/1.62  tff(c_1416, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1414, c_1204])).
% 3.24/1.62  tff(c_1428, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_1416])).
% 3.24/1.62  tff(c_1431, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1428])).
% 3.24/1.62  tff(c_1433, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1203, c_1431])).
% 3.24/1.62  tff(c_1435, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_213])).
% 3.24/1.62  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.24/1.62  tff(c_1443, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1435, c_2])).
% 3.24/1.62  tff(c_1434, plain, (v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_213])).
% 3.24/1.62  tff(c_1439, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_1434, c_2])).
% 3.24/1.62  tff(c_1456, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1443, c_1439])).
% 3.24/1.62  tff(c_1449, plain, (![A_11]: (m1_subset_1('#skF_2', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_12])).
% 3.24/1.62  tff(c_1506, plain, (![A_11]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_11)))), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1449])).
% 3.24/1.62  tff(c_1448, plain, (![A_15]: (k8_setfam_1(A_15, '#skF_2')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_1439, c_40])).
% 3.24/1.62  tff(c_1496, plain, (![A_15]: (k8_setfam_1(A_15, '#skF_3')=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_1448])).
% 3.24/1.62  tff(c_1701, plain, (![A_170, B_171]: (m1_subset_1(k8_setfam_1(A_170, B_171), k1_zfmisc_1(A_170)) | ~m1_subset_1(B_171, k1_zfmisc_1(k1_zfmisc_1(A_170))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.24/1.62  tff(c_1716, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1(A_15))))), inference(superposition, [status(thm), theory('equality')], [c_1496, c_1701])).
% 3.24/1.62  tff(c_1723, plain, (![A_172]: (m1_subset_1(A_172, k1_zfmisc_1(A_172)))), inference(demodulation, [status(thm), theory('equality')], [c_1506, c_1716])).
% 3.24/1.62  tff(c_1739, plain, (![A_172]: (r1_tarski(A_172, A_172))), inference(resolution, [status(thm)], [c_1723, c_24])).
% 3.24/1.62  tff(c_1466, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1456, c_32])).
% 3.24/1.62  tff(c_1621, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1496, c_1496, c_1466])).
% 3.24/1.62  tff(c_1742, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1739, c_1621])).
% 3.24/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.24/1.62  
% 3.24/1.62  Inference rules
% 3.24/1.62  ----------------------
% 3.24/1.62  #Ref     : 0
% 3.24/1.62  #Sup     : 370
% 3.24/1.62  #Fact    : 0
% 3.24/1.62  #Define  : 0
% 3.24/1.62  #Split   : 8
% 3.24/1.62  #Chain   : 0
% 3.24/1.62  #Close   : 0
% 3.24/1.62  
% 3.24/1.62  Ordering : KBO
% 3.24/1.62  
% 3.24/1.62  Simplification rules
% 3.24/1.62  ----------------------
% 3.24/1.62  #Subsume      : 38
% 3.24/1.62  #Demod        : 360
% 3.24/1.62  #Tautology    : 248
% 3.24/1.62  #SimpNegUnit  : 8
% 3.24/1.62  #BackRed      : 81
% 3.24/1.62  
% 3.24/1.62  #Partial instantiations: 0
% 3.24/1.62  #Strategies tried      : 1
% 3.24/1.62  
% 3.24/1.62  Timing (in seconds)
% 3.24/1.62  ----------------------
% 3.24/1.62  Preprocessing        : 0.32
% 3.24/1.62  Parsing              : 0.17
% 3.24/1.62  CNF conversion       : 0.02
% 3.24/1.62  Main loop            : 0.45
% 3.24/1.62  Inferencing          : 0.16
% 3.24/1.62  Reduction            : 0.15
% 3.24/1.62  Demodulation         : 0.11
% 3.24/1.62  BG Simplification    : 0.02
% 3.24/1.62  Subsumption          : 0.08
% 3.24/1.62  Abstraction          : 0.02
% 3.24/1.62  MUC search           : 0.00
% 3.24/1.62  Cooper               : 0.00
% 3.24/1.62  Total                : 0.81
% 3.24/1.62  Index Insertion      : 0.00
% 3.24/1.62  Index Deletion       : 0.00
% 3.24/1.62  Index Matching       : 0.00
% 3.24/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------
