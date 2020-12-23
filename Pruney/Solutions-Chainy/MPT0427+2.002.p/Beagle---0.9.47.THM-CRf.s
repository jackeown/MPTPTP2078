%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:56 EST 2020

% Result     : Theorem 2.72s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   98 ( 225 expanded)
%              Number of leaves         :   35 (  88 expanded)
%              Depth                    :   11
%              Number of atoms          :  130 ( 435 expanded)
%              Number of equality atoms :   47 ( 131 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k8_setfam_1,type,(
    k8_setfam_1: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_setfam_1,type,(
    k6_setfam_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_35,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k6_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_setfam_1)).

tff(f_87,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_49,axiom,(
    ! [A] :
    ? [B] : m1_subset_1(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_subset_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l22_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_56,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_93,axiom,(
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

tff(c_8,plain,(
    ! [B_3] : r1_tarski(B_3,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_539,plain,(
    ! [A_96,B_97] :
      ( k6_setfam_1(A_96,B_97) = k1_setfam_1(B_97)
      | ~ m1_subset_1(B_97,k1_zfmisc_1(k1_zfmisc_1(A_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_566,plain,(
    k6_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_539])).

tff(c_616,plain,(
    ! [A_102,B_103] :
      ( m1_subset_1(k6_setfam_1(A_102,B_103),k1_zfmisc_1(A_102))
      | ~ m1_subset_1(B_103,k1_zfmisc_1(k1_zfmisc_1(A_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_632,plain,
    ( m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_566,c_616])).

tff(c_640,plain,(
    m1_subset_1(k1_setfam_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_632])).

tff(c_34,plain,(
    ! [A_27,B_28] :
      ( r1_tarski(A_27,B_28)
      | ~ m1_subset_1(A_27,k1_zfmisc_1(B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_650,plain,(
    r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_640,c_34])).

tff(c_46,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_63,plain,(
    r1_tarski('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(resolution,[status(thm)],[c_46,c_52])).

tff(c_565,plain,(
    k6_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_539])).

tff(c_678,plain,(
    ! [A_104,B_105] :
      ( k8_setfam_1(A_104,B_105) = k6_setfam_1(A_104,B_105)
      | k1_xboole_0 = B_105
      | ~ m1_subset_1(B_105,k1_zfmisc_1(k1_zfmisc_1(A_104))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_697,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k6_setfam_1('#skF_2','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_46,c_678])).

tff(c_711,plain,
    ( k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_565,c_697])).

tff(c_721,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_711])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(A_27,k1_zfmisc_1(B_28))
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_448,plain,(
    ! [A_87] :
      ( k8_setfam_1(A_87,k1_xboole_0) = A_87
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_456,plain,(
    ! [A_87] :
      ( k8_setfam_1(A_87,k1_xboole_0) = A_87
      | ~ r1_tarski(k1_xboole_0,k1_zfmisc_1(A_87)) ) ),
    inference(resolution,[status(thm)],[c_36,c_448])).

tff(c_835,plain,(
    ! [A_115] :
      ( k8_setfam_1(A_115,'#skF_3') = A_115
      | ~ r1_tarski('#skF_3',k1_zfmisc_1(A_115)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_721,c_721,c_456])).

tff(c_843,plain,(
    k8_setfam_1('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_63,c_835])).

tff(c_18,plain,(
    ! [A_12] : m1_subset_1('#skF_1'(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_32,plain,(
    ! [A_25,B_26] :
      ( r2_hidden(A_25,B_26)
      | v1_xboole_0(B_26)
      | ~ m1_subset_1(A_25,B_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_394,plain,(
    ! [A_80,B_81] :
      ( k2_xboole_0(k1_tarski(A_80),B_81) = B_81
      | ~ r2_hidden(A_80,B_81) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),B_11) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_406,plain,(
    ! [B_82,A_83] :
      ( k1_xboole_0 != B_82
      | ~ r2_hidden(A_83,B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_16])).

tff(c_412,plain,(
    ! [B_84,A_85] :
      ( k1_xboole_0 != B_84
      | v1_xboole_0(B_84)
      | ~ m1_subset_1(A_85,B_84) ) ),
    inference(resolution,[status(thm)],[c_32,c_406])).

tff(c_435,plain,(
    ! [A_86] :
      ( k1_xboole_0 != A_86
      | v1_xboole_0(A_86) ) ),
    inference(resolution,[status(thm)],[c_18,c_412])).

tff(c_42,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_99,plain,(
    ! [B_48,A_49] :
      ( v1_xboole_0(B_48)
      | ~ m1_subset_1(B_48,k1_zfmisc_1(A_49))
      | ~ v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_364,plain,(
    ! [A_76,B_77] :
      ( v1_xboole_0(A_76)
      | ~ v1_xboole_0(B_77)
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(resolution,[status(thm)],[c_36,c_99])).

tff(c_389,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_4') ),
    inference(resolution,[status(thm)],[c_42,c_364])).

tff(c_390,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_389])).

tff(c_445,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(resolution,[status(thm)],[c_435,c_390])).

tff(c_700,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k6_setfam_1('#skF_2','#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_678])).

tff(c_713,plain,
    ( k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4')
    | k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_700])).

tff(c_714,plain,(
    k8_setfam_1('#skF_2','#skF_4') = k1_setfam_1('#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_445,c_713])).

tff(c_40,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_716,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k8_setfam_1('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_714,c_40])).

tff(c_844,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_716])).

tff(c_847,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_844])).

tff(c_849,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_38,plain,(
    ! [B_30,A_29] :
      ( r1_tarski(k1_setfam_1(B_30),k1_setfam_1(A_29))
      | k1_xboole_0 = A_29
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_848,plain,(
    k8_setfam_1('#skF_2','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_711])).

tff(c_850,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_4'),k1_setfam_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_848,c_716])).

tff(c_857,plain,
    ( k1_xboole_0 = '#skF_3'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_38,c_850])).

tff(c_860,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_857])).

tff(c_862,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_849,c_860])).

tff(c_864,plain,(
    v1_xboole_0('#skF_4') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_872,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_864,c_2])).

tff(c_863,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_389])).

tff(c_868,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_863,c_2])).

tff(c_884,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_868])).

tff(c_331,plain,(
    ! [B_73,A_74] :
      ( B_73 = A_74
      | ~ r1_tarski(B_73,A_74)
      | ~ r1_tarski(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_352,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_331])).

tff(c_353,plain,(
    ~ r1_tarski('#skF_4','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_352])).

tff(c_890,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_884,c_353])).

tff(c_898,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_890])).

tff(c_899,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_352])).

tff(c_902,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_2','#skF_4'),k8_setfam_1('#skF_2','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_899,c_40])).

tff(c_908,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_902])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.16/0.36  % Computer   : n006.cluster.edu
% 0.16/0.36  % Model      : x86_64 x86_64
% 0.16/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.16/0.36  % Memory     : 8042.1875MB
% 0.16/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.16/0.36  % CPULimit   : 60
% 0.16/0.36  % DateTime   : Tue Dec  1 11:12:52 EST 2020
% 0.16/0.36  % CPUTime    : 
% 0.16/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.72/1.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.43  
% 2.72/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.44  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k8_setfam_1 > k6_setfam_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3 > #skF_4
% 2.72/1.44  
% 2.72/1.44  %Foreground sorts:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Background operators:
% 2.72/1.44  
% 2.72/1.44  
% 2.72/1.44  %Foreground operators:
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.72/1.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.72/1.44  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.72/1.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.72/1.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.72/1.44  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 2.72/1.44  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.72/1.44  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.72/1.44  tff('#skF_2', type, '#skF_2': $i).
% 2.72/1.44  tff('#skF_3', type, '#skF_3': $i).
% 2.72/1.44  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.72/1.44  tff('#skF_4', type, '#skF_4': $i).
% 2.72/1.44  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 2.72/1.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.72/1.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.72/1.44  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.72/1.44  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.72/1.44  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.72/1.44  
% 3.06/1.45  tff(f_35, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.45  tff(f_103, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.06/1.45  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.06/1.45  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k6_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_setfam_1)).
% 3.06/1.45  tff(f_87, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.06/1.45  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.06/1.45  tff(f_49, axiom, (![A]: (?[B]: m1_subset_1(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', existence_m1_subset_1)).
% 3.06/1.45  tff(f_83, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 3.06/1.45  tff(f_43, axiom, (![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l22_zfmisc_1)).
% 3.06/1.45  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.06/1.45  tff(f_56, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.06/1.45  tff(f_93, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.06/1.45  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.06/1.45  tff(c_8, plain, (![B_3]: (r1_tarski(B_3, B_3))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.45  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.45  tff(c_539, plain, (![A_96, B_97]: (k6_setfam_1(A_96, B_97)=k1_setfam_1(B_97) | ~m1_subset_1(B_97, k1_zfmisc_1(k1_zfmisc_1(A_96))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.06/1.45  tff(c_566, plain, (k6_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_539])).
% 3.06/1.45  tff(c_616, plain, (![A_102, B_103]: (m1_subset_1(k6_setfam_1(A_102, B_103), k1_zfmisc_1(A_102)) | ~m1_subset_1(B_103, k1_zfmisc_1(k1_zfmisc_1(A_102))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.06/1.45  tff(c_632, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_566, c_616])).
% 3.06/1.45  tff(c_640, plain, (m1_subset_1(k1_setfam_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_632])).
% 3.06/1.45  tff(c_34, plain, (![A_27, B_28]: (r1_tarski(A_27, B_28) | ~m1_subset_1(A_27, k1_zfmisc_1(B_28)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.45  tff(c_650, plain, (r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_640, c_34])).
% 3.06/1.45  tff(c_46, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.45  tff(c_52, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.45  tff(c_63, plain, (r1_tarski('#skF_3', k1_zfmisc_1('#skF_2'))), inference(resolution, [status(thm)], [c_46, c_52])).
% 3.06/1.45  tff(c_565, plain, (k6_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_46, c_539])).
% 3.06/1.45  tff(c_678, plain, (![A_104, B_105]: (k8_setfam_1(A_104, B_105)=k6_setfam_1(A_104, B_105) | k1_xboole_0=B_105 | ~m1_subset_1(B_105, k1_zfmisc_1(k1_zfmisc_1(A_104))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.45  tff(c_697, plain, (k8_setfam_1('#skF_2', '#skF_3')=k6_setfam_1('#skF_2', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_46, c_678])).
% 3.06/1.45  tff(c_711, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_565, c_697])).
% 3.06/1.45  tff(c_721, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_711])).
% 3.06/1.45  tff(c_36, plain, (![A_27, B_28]: (m1_subset_1(A_27, k1_zfmisc_1(B_28)) | ~r1_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_87])).
% 3.06/1.45  tff(c_448, plain, (![A_87]: (k8_setfam_1(A_87, k1_xboole_0)=A_87 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_87))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.45  tff(c_456, plain, (![A_87]: (k8_setfam_1(A_87, k1_xboole_0)=A_87 | ~r1_tarski(k1_xboole_0, k1_zfmisc_1(A_87)))), inference(resolution, [status(thm)], [c_36, c_448])).
% 3.06/1.45  tff(c_835, plain, (![A_115]: (k8_setfam_1(A_115, '#skF_3')=A_115 | ~r1_tarski('#skF_3', k1_zfmisc_1(A_115)))), inference(demodulation, [status(thm), theory('equality')], [c_721, c_721, c_456])).
% 3.06/1.45  tff(c_843, plain, (k8_setfam_1('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_63, c_835])).
% 3.06/1.45  tff(c_18, plain, (![A_12]: (m1_subset_1('#skF_1'(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.06/1.45  tff(c_32, plain, (![A_25, B_26]: (r2_hidden(A_25, B_26) | v1_xboole_0(B_26) | ~m1_subset_1(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.06/1.45  tff(c_394, plain, (![A_80, B_81]: (k2_xboole_0(k1_tarski(A_80), B_81)=B_81 | ~r2_hidden(A_80, B_81))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.06/1.45  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.06/1.45  tff(c_406, plain, (![B_82, A_83]: (k1_xboole_0!=B_82 | ~r2_hidden(A_83, B_82))), inference(superposition, [status(thm), theory('equality')], [c_394, c_16])).
% 3.06/1.45  tff(c_412, plain, (![B_84, A_85]: (k1_xboole_0!=B_84 | v1_xboole_0(B_84) | ~m1_subset_1(A_85, B_84))), inference(resolution, [status(thm)], [c_32, c_406])).
% 3.06/1.45  tff(c_435, plain, (![A_86]: (k1_xboole_0!=A_86 | v1_xboole_0(A_86))), inference(resolution, [status(thm)], [c_18, c_412])).
% 3.06/1.45  tff(c_42, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.45  tff(c_99, plain, (![B_48, A_49]: (v1_xboole_0(B_48) | ~m1_subset_1(B_48, k1_zfmisc_1(A_49)) | ~v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_56])).
% 3.06/1.45  tff(c_364, plain, (![A_76, B_77]: (v1_xboole_0(A_76) | ~v1_xboole_0(B_77) | ~r1_tarski(A_76, B_77))), inference(resolution, [status(thm)], [c_36, c_99])).
% 3.06/1.45  tff(c_389, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_4')), inference(resolution, [status(thm)], [c_42, c_364])).
% 3.06/1.45  tff(c_390, plain, (~v1_xboole_0('#skF_4')), inference(splitLeft, [status(thm)], [c_389])).
% 3.06/1.45  tff(c_445, plain, (k1_xboole_0!='#skF_4'), inference(resolution, [status(thm)], [c_435, c_390])).
% 3.06/1.45  tff(c_700, plain, (k8_setfam_1('#skF_2', '#skF_4')=k6_setfam_1('#skF_2', '#skF_4') | k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_44, c_678])).
% 3.06/1.45  tff(c_713, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4') | k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_566, c_700])).
% 3.06/1.45  tff(c_714, plain, (k8_setfam_1('#skF_2', '#skF_4')=k1_setfam_1('#skF_4')), inference(negUnitSimplification, [status(thm)], [c_445, c_713])).
% 3.06/1.45  tff(c_40, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.06/1.45  tff(c_716, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k8_setfam_1('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_714, c_40])).
% 3.06/1.45  tff(c_844, plain, (~r1_tarski(k1_setfam_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_843, c_716])).
% 3.06/1.45  tff(c_847, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_650, c_844])).
% 3.06/1.45  tff(c_849, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_711])).
% 3.06/1.45  tff(c_38, plain, (![B_30, A_29]: (r1_tarski(k1_setfam_1(B_30), k1_setfam_1(A_29)) | k1_xboole_0=A_29 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.06/1.45  tff(c_848, plain, (k8_setfam_1('#skF_2', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_711])).
% 3.06/1.45  tff(c_850, plain, (~r1_tarski(k1_setfam_1('#skF_4'), k1_setfam_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_848, c_716])).
% 3.06/1.45  tff(c_857, plain, (k1_xboole_0='#skF_3' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_38, c_850])).
% 3.06/1.45  tff(c_860, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_857])).
% 3.06/1.45  tff(c_862, plain, $false, inference(negUnitSimplification, [status(thm)], [c_849, c_860])).
% 3.06/1.45  tff(c_864, plain, (v1_xboole_0('#skF_4')), inference(splitRight, [status(thm)], [c_389])).
% 3.06/1.45  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.06/1.45  tff(c_872, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_864, c_2])).
% 3.06/1.45  tff(c_863, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_389])).
% 3.06/1.45  tff(c_868, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_863, c_2])).
% 3.06/1.45  tff(c_884, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_872, c_868])).
% 3.06/1.45  tff(c_331, plain, (![B_73, A_74]: (B_73=A_74 | ~r1_tarski(B_73, A_74) | ~r1_tarski(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.45  tff(c_352, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_331])).
% 3.06/1.45  tff(c_353, plain, (~r1_tarski('#skF_4', '#skF_3')), inference(splitLeft, [status(thm)], [c_352])).
% 3.06/1.45  tff(c_890, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_884, c_353])).
% 3.06/1.45  tff(c_898, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_890])).
% 3.06/1.45  tff(c_899, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_352])).
% 3.06/1.45  tff(c_902, plain, (~r1_tarski(k8_setfam_1('#skF_2', '#skF_4'), k8_setfam_1('#skF_2', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_899, c_40])).
% 3.06/1.45  tff(c_908, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_902])).
% 3.06/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.06/1.45  
% 3.06/1.45  Inference rules
% 3.06/1.45  ----------------------
% 3.06/1.45  #Ref     : 1
% 3.06/1.45  #Sup     : 184
% 3.06/1.45  #Fact    : 0
% 3.06/1.45  #Define  : 0
% 3.06/1.45  #Split   : 13
% 3.06/1.45  #Chain   : 0
% 3.06/1.45  #Close   : 0
% 3.06/1.45  
% 3.06/1.45  Ordering : KBO
% 3.06/1.45  
% 3.06/1.45  Simplification rules
% 3.06/1.45  ----------------------
% 3.06/1.45  #Subsume      : 47
% 3.06/1.45  #Demod        : 70
% 3.06/1.45  #Tautology    : 59
% 3.06/1.45  #SimpNegUnit  : 4
% 3.06/1.45  #BackRed      : 42
% 3.06/1.45  
% 3.06/1.45  #Partial instantiations: 0
% 3.06/1.45  #Strategies tried      : 1
% 3.06/1.45  
% 3.06/1.45  Timing (in seconds)
% 3.06/1.45  ----------------------
% 3.06/1.46  Preprocessing        : 0.31
% 3.06/1.46  Parsing              : 0.17
% 3.06/1.46  CNF conversion       : 0.02
% 3.06/1.46  Main loop            : 0.36
% 3.06/1.46  Inferencing          : 0.13
% 3.06/1.46  Reduction            : 0.11
% 3.06/1.46  Demodulation         : 0.07
% 3.06/1.46  BG Simplification    : 0.02
% 3.06/1.46  Subsumption          : 0.07
% 3.06/1.46  Abstraction          : 0.02
% 3.06/1.46  MUC search           : 0.00
% 3.06/1.46  Cooper               : 0.00
% 3.06/1.46  Total                : 0.71
% 3.06/1.46  Index Insertion      : 0.00
% 3.06/1.46  Index Deletion       : 0.00
% 3.06/1.46  Index Matching       : 0.00
% 3.06/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------
