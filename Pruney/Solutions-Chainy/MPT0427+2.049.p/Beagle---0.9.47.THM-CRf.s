%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:03 EST 2020

% Result     : Theorem 3.48s
% Output     : CNFRefutation 3.48s
% Verified   : 
% Statistics : Number of formulae       :   94 ( 360 expanded)
%              Number of leaves         :   27 ( 126 expanded)
%              Depth                    :   12
%              Number of atoms          :  127 ( 739 expanded)
%              Number of equality atoms :   50 ( 321 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_47,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_82,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_setfam_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_14,plain,(
    ! [A_11] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_11)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_16,plain,(
    ! [A_12] :
      ( k8_setfam_1(A_12,k1_xboole_0) = A_12
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_40,plain,(
    ! [A_12] : k8_setfam_1(A_12,k1_xboole_0) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_386,plain,(
    ! [A_78,B_79] :
      ( m1_subset_1(k8_setfam_1(A_78,B_79),k1_zfmisc_1(A_78))
      | ~ m1_subset_1(B_79,k1_zfmisc_1(k1_zfmisc_1(A_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_398,plain,(
    ! [A_12] :
      ( m1_subset_1(A_12,k1_zfmisc_1(A_12))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_12))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_386])).

tff(c_404,plain,(
    ! [A_80] : m1_subset_1(A_80,k1_zfmisc_1(A_80)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_398])).

tff(c_24,plain,(
    ! [A_18,B_19] :
      ( r1_tarski(A_18,B_19)
      | ~ m1_subset_1(A_18,k1_zfmisc_1(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_416,plain,(
    ! [A_80] : r1_tarski(A_80,A_80) ),
    inference(resolution,[status(thm)],[c_404,c_24])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_332,plain,(
    ! [A_66,B_67] :
      ( k6_setfam_1(A_66,B_67) = k1_setfam_1(B_67)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(k1_zfmisc_1(A_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_348,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_332])).

tff(c_589,plain,(
    ! [A_92,B_93] :
      ( k8_setfam_1(A_92,B_93) = k6_setfam_1(A_92,B_93)
      | k1_xboole_0 = B_93
      | ~ m1_subset_1(B_93,k1_zfmisc_1(k1_zfmisc_1(A_92))) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_604,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_589])).

tff(c_617,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_604])).

tff(c_623,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_617])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_349,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_332])).

tff(c_607,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_589])).

tff(c_619,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_349,c_607])).

tff(c_764,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_619])).

tff(c_765,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_764])).

tff(c_645,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_2') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_623,c_40])).

tff(c_773,plain,(
    ! [A_12] : k8_setfam_1(A_12,'#skF_3') = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_765,c_645])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_699,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_645,c_32])).

tff(c_821,plain,(
    ~ r1_tarski('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_699])).

tff(c_824,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_416,c_821])).

tff(c_825,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_764])).

tff(c_828,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_699])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k8_setfam_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(k1_zfmisc_1(A_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_832,plain,
    ( m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_825,c_20])).

tff(c_836,plain,(
    m1_subset_1(k1_setfam_1('#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_832])).

tff(c_862,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_836,c_24])).

tff(c_867,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_828,c_862])).

tff(c_869,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_30,plain,(
    ! [B_24,A_23] :
      ( r1_tarski(k1_setfam_1(B_24),k1_setfam_1(A_23))
      | k1_xboole_0 = A_23
      | ~ r1_tarski(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_907,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_619])).

tff(c_910,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_869])).

tff(c_52,plain,(
    ! [A_30,B_31] :
      ( r1_tarski(A_30,B_31)
      | ~ m1_subset_1(A_30,k1_zfmisc_1(B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_64,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(resolution,[status(thm)],[c_14,c_52])).

tff(c_938,plain,(
    ! [A_108] : r1_tarski('#skF_3',A_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_64])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1043,plain,(
    ! [A_116,A_117] :
      ( r1_tarski(A_116,A_117)
      | ~ r1_tarski(A_116,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_938,c_6])).

tff(c_1056,plain,(
    ! [A_117] : r1_tarski('#skF_2',A_117) ),
    inference(resolution,[status(thm)],[c_34,c_1043])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( k4_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1116,plain,(
    ! [A_122,B_123] :
      ( k4_xboole_0(A_122,B_123) = '#skF_3'
      | ~ r1_tarski(A_122,B_123) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_4])).

tff(c_1129,plain,(
    ! [A_117] : k4_xboole_0('#skF_2',A_117) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1056,c_1116])).

tff(c_76,plain,(
    ! [A_37,B_38] :
      ( k4_xboole_0(A_37,B_38) = k1_xboole_0
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_95,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_64,c_76])).

tff(c_926,plain,(
    ! [A_11] : k4_xboole_0('#skF_3',A_11) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_907,c_95])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(A_9,B_10)
      | k4_xboole_0(A_9,B_10) != A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_121,plain,(
    ! [A_42,C_43,B_44] :
      ( r1_xboole_0(A_42,C_43)
      | ~ r1_xboole_0(B_44,C_43)
      | ~ r1_tarski(A_42,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1709,plain,(
    ! [A_150,B_151,A_152] :
      ( r1_xboole_0(A_150,B_151)
      | ~ r1_tarski(A_150,A_152)
      | k4_xboole_0(A_152,B_151) != A_152 ) ),
    inference(resolution,[status(thm)],[c_12,c_121])).

tff(c_1769,plain,(
    ! [B_156,A_157] :
      ( r1_xboole_0('#skF_2',B_156)
      | k4_xboole_0(A_157,B_156) != A_157 ) ),
    inference(resolution,[status(thm)],[c_1056,c_1709])).

tff(c_1788,plain,(
    ! [A_158] : r1_xboole_0('#skF_2',A_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_926,c_1769])).

tff(c_10,plain,(
    ! [A_9,B_10] :
      ( k4_xboole_0(A_9,B_10) = A_9
      | ~ r1_xboole_0(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1793,plain,(
    ! [A_158] : k4_xboole_0('#skF_2',A_158) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1788,c_10])).

tff(c_1796,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1129,c_1793])).

tff(c_1798,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_910,c_1796])).

tff(c_1799,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_619])).

tff(c_868,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_617])).

tff(c_871,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_868,c_32])).

tff(c_1802,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1799,c_871])).

tff(c_1818,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1802])).

tff(c_1825,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1818])).

tff(c_1827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_869,c_1825])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:43:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.48/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.58  
% 3.48/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.48/1.58  
% 3.48/1.58  %Foreground sorts:
% 3.48/1.58  
% 3.48/1.58  
% 3.48/1.58  %Background operators:
% 3.48/1.58  
% 3.48/1.58  
% 3.48/1.58  %Foreground operators:
% 3.48/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.48/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.48/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.48/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.48/1.58  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.48/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.48/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.48/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.48/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.48/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.48/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.48/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.48/1.58  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.48/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.48/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.48/1.58  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.48/1.59  
% 3.48/1.60  tff(f_47, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.48/1.60  tff(f_58, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.48/1.60  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.48/1.60  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.48/1.60  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.48/1.60  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.48/1.60  tff(f_82, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.48/1.60  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.48/1.60  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.48/1.60  tff(f_45, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.48/1.60  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.48/1.60  tff(c_14, plain, (![A_11]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.48/1.60  tff(c_16, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.60  tff(c_40, plain, (![A_12]: (k8_setfam_1(A_12, k1_xboole_0)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.48/1.60  tff(c_386, plain, (![A_78, B_79]: (m1_subset_1(k8_setfam_1(A_78, B_79), k1_zfmisc_1(A_78)) | ~m1_subset_1(B_79, k1_zfmisc_1(k1_zfmisc_1(A_78))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.48/1.60  tff(c_398, plain, (![A_12]: (m1_subset_1(A_12, k1_zfmisc_1(A_12)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_12))))), inference(superposition, [status(thm), theory('equality')], [c_40, c_386])).
% 3.48/1.60  tff(c_404, plain, (![A_80]: (m1_subset_1(A_80, k1_zfmisc_1(A_80)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_398])).
% 3.48/1.60  tff(c_24, plain, (![A_18, B_19]: (r1_tarski(A_18, B_19) | ~m1_subset_1(A_18, k1_zfmisc_1(B_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.60  tff(c_416, plain, (![A_80]: (r1_tarski(A_80, A_80))), inference(resolution, [status(thm)], [c_404, c_24])).
% 3.48/1.60  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.48/1.60  tff(c_332, plain, (![A_66, B_67]: (k6_setfam_1(A_66, B_67)=k1_setfam_1(B_67) | ~m1_subset_1(B_67, k1_zfmisc_1(k1_zfmisc_1(A_66))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.48/1.60  tff(c_348, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_332])).
% 3.48/1.60  tff(c_589, plain, (![A_92, B_93]: (k8_setfam_1(A_92, B_93)=k6_setfam_1(A_92, B_93) | k1_xboole_0=B_93 | ~m1_subset_1(B_93, k1_zfmisc_1(k1_zfmisc_1(A_92))))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.48/1.60  tff(c_604, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_589])).
% 3.48/1.60  tff(c_617, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_604])).
% 3.48/1.60  tff(c_623, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_617])).
% 3.48/1.60  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.48/1.60  tff(c_349, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_332])).
% 3.48/1.60  tff(c_607, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_589])).
% 3.48/1.60  tff(c_619, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_349, c_607])).
% 3.48/1.60  tff(c_764, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_623, c_619])).
% 3.48/1.60  tff(c_765, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_764])).
% 3.48/1.60  tff(c_645, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_2')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_623, c_40])).
% 3.48/1.60  tff(c_773, plain, (![A_12]: (k8_setfam_1(A_12, '#skF_3')=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_765, c_645])).
% 3.48/1.60  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.48/1.60  tff(c_699, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_645, c_32])).
% 3.48/1.60  tff(c_821, plain, (~r1_tarski('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_773, c_699])).
% 3.48/1.60  tff(c_824, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_416, c_821])).
% 3.48/1.60  tff(c_825, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_764])).
% 3.48/1.60  tff(c_828, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_825, c_699])).
% 3.48/1.60  tff(c_20, plain, (![A_14, B_15]: (m1_subset_1(k8_setfam_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(k1_zfmisc_1(A_14))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.48/1.60  tff(c_832, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_825, c_20])).
% 3.48/1.60  tff(c_836, plain, (m1_subset_1(k1_setfam_1('#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_832])).
% 3.48/1.60  tff(c_862, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_836, c_24])).
% 3.48/1.60  tff(c_867, plain, $false, inference(negUnitSimplification, [status(thm)], [c_828, c_862])).
% 3.48/1.60  tff(c_869, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_617])).
% 3.48/1.60  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.48/1.60  tff(c_30, plain, (![B_24, A_23]: (r1_tarski(k1_setfam_1(B_24), k1_setfam_1(A_23)) | k1_xboole_0=A_23 | ~r1_tarski(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.48/1.60  tff(c_907, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_619])).
% 3.48/1.60  tff(c_910, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_907, c_869])).
% 3.48/1.60  tff(c_52, plain, (![A_30, B_31]: (r1_tarski(A_30, B_31) | ~m1_subset_1(A_30, k1_zfmisc_1(B_31)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.48/1.60  tff(c_64, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(resolution, [status(thm)], [c_14, c_52])).
% 3.48/1.60  tff(c_938, plain, (![A_108]: (r1_tarski('#skF_3', A_108))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_64])).
% 3.48/1.60  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.48/1.60  tff(c_1043, plain, (![A_116, A_117]: (r1_tarski(A_116, A_117) | ~r1_tarski(A_116, '#skF_3'))), inference(resolution, [status(thm)], [c_938, c_6])).
% 3.48/1.60  tff(c_1056, plain, (![A_117]: (r1_tarski('#skF_2', A_117))), inference(resolution, [status(thm)], [c_34, c_1043])).
% 3.48/1.60  tff(c_4, plain, (![A_1, B_2]: (k4_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.60  tff(c_1116, plain, (![A_122, B_123]: (k4_xboole_0(A_122, B_123)='#skF_3' | ~r1_tarski(A_122, B_123))), inference(demodulation, [status(thm), theory('equality')], [c_907, c_4])).
% 3.48/1.60  tff(c_1129, plain, (![A_117]: (k4_xboole_0('#skF_2', A_117)='#skF_3')), inference(resolution, [status(thm)], [c_1056, c_1116])).
% 3.48/1.60  tff(c_76, plain, (![A_37, B_38]: (k4_xboole_0(A_37, B_38)=k1_xboole_0 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.48/1.60  tff(c_95, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_76])).
% 3.48/1.60  tff(c_926, plain, (![A_11]: (k4_xboole_0('#skF_3', A_11)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_907, c_907, c_95])).
% 3.48/1.60  tff(c_12, plain, (![A_9, B_10]: (r1_xboole_0(A_9, B_10) | k4_xboole_0(A_9, B_10)!=A_9)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.60  tff(c_121, plain, (![A_42, C_43, B_44]: (r1_xboole_0(A_42, C_43) | ~r1_xboole_0(B_44, C_43) | ~r1_tarski(A_42, B_44))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.48/1.60  tff(c_1709, plain, (![A_150, B_151, A_152]: (r1_xboole_0(A_150, B_151) | ~r1_tarski(A_150, A_152) | k4_xboole_0(A_152, B_151)!=A_152)), inference(resolution, [status(thm)], [c_12, c_121])).
% 3.48/1.60  tff(c_1769, plain, (![B_156, A_157]: (r1_xboole_0('#skF_2', B_156) | k4_xboole_0(A_157, B_156)!=A_157)), inference(resolution, [status(thm)], [c_1056, c_1709])).
% 3.48/1.60  tff(c_1788, plain, (![A_158]: (r1_xboole_0('#skF_2', A_158))), inference(superposition, [status(thm), theory('equality')], [c_926, c_1769])).
% 3.48/1.60  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, B_10)=A_9 | ~r1_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.48/1.60  tff(c_1793, plain, (![A_158]: (k4_xboole_0('#skF_2', A_158)='#skF_2')), inference(resolution, [status(thm)], [c_1788, c_10])).
% 3.48/1.60  tff(c_1796, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1129, c_1793])).
% 3.48/1.60  tff(c_1798, plain, $false, inference(negUnitSimplification, [status(thm)], [c_910, c_1796])).
% 3.48/1.60  tff(c_1799, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_619])).
% 3.48/1.60  tff(c_868, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_617])).
% 3.48/1.60  tff(c_871, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_868, c_32])).
% 3.48/1.60  tff(c_1802, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1799, c_871])).
% 3.48/1.60  tff(c_1818, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_1802])).
% 3.48/1.60  tff(c_1825, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1818])).
% 3.48/1.60  tff(c_1827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_869, c_1825])).
% 3.48/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.48/1.60  
% 3.48/1.60  Inference rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Ref     : 0
% 3.48/1.60  #Sup     : 387
% 3.48/1.60  #Fact    : 0
% 3.48/1.60  #Define  : 0
% 3.48/1.60  #Split   : 3
% 3.48/1.60  #Chain   : 0
% 3.48/1.60  #Close   : 0
% 3.48/1.60  
% 3.48/1.60  Ordering : KBO
% 3.48/1.60  
% 3.48/1.60  Simplification rules
% 3.48/1.60  ----------------------
% 3.48/1.60  #Subsume      : 35
% 3.48/1.60  #Demod        : 228
% 3.48/1.60  #Tautology    : 230
% 3.48/1.60  #SimpNegUnit  : 3
% 3.48/1.60  #BackRed      : 74
% 3.48/1.60  
% 3.48/1.60  #Partial instantiations: 0
% 3.48/1.60  #Strategies tried      : 1
% 3.48/1.60  
% 3.48/1.60  Timing (in seconds)
% 3.48/1.60  ----------------------
% 3.48/1.60  Preprocessing        : 0.30
% 3.48/1.60  Parsing              : 0.15
% 3.48/1.60  CNF conversion       : 0.02
% 3.48/1.61  Main loop            : 0.48
% 3.48/1.61  Inferencing          : 0.17
% 3.48/1.61  Reduction            : 0.15
% 3.48/1.61  Demodulation         : 0.11
% 3.48/1.61  BG Simplification    : 0.02
% 3.48/1.61  Subsumption          : 0.09
% 3.48/1.61  Abstraction          : 0.03
% 3.48/1.61  MUC search           : 0.00
% 3.48/1.61  Cooper               : 0.00
% 3.48/1.61  Total                : 0.82
% 3.48/1.61  Index Insertion      : 0.00
% 3.48/1.61  Index Deletion       : 0.00
% 3.48/1.61  Index Matching       : 0.00
% 3.48/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
