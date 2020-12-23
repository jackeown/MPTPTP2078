%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:13 EST 2020

% Result     : Theorem 2.67s
% Output     : CNFRefutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 159 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :   12
%              Number of atoms          :  103 ( 235 expanded)
%              Number of equality atoms :   44 (  95 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

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

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_74,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_38,plain,(
    ! [A_22] : k2_subset_1(A_22) = A_22 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_46,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_46])).

tff(c_112,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_10,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_52,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_52])).

tff(c_113,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_114,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_44])).

tff(c_42,plain,(
    ! [A_25] : ~ v1_xboole_0(k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_284,plain,(
    ! [B_55,A_56] :
      ( r2_hidden(B_55,A_56)
      | ~ m1_subset_1(B_55,A_56)
      | v1_xboole_0(A_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_18,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_288,plain,(
    ! [B_55,A_15] :
      ( r1_tarski(B_55,A_15)
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_284,c_18])).

tff(c_442,plain,(
    ! [B_66,A_67] :
      ( r1_tarski(B_66,A_67)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_67)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_288])).

tff(c_451,plain,(
    r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_442])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_459,plain,(
    k3_xboole_0('#skF_4','#skF_4') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_451,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_467,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_4])).

tff(c_470,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_467])).

tff(c_514,plain,(
    ! [A_68,B_69] :
      ( k4_xboole_0(A_68,B_69) = k3_subset_1(A_68,B_69)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_521,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_114,c_514])).

tff(c_524,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_470,c_521])).

tff(c_123,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_113,c_112])).

tff(c_525,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_524,c_123])).

tff(c_528,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_525])).

tff(c_529,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_531,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_529])).

tff(c_532,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_752,plain,(
    ! [B_93,A_94] :
      ( r2_hidden(B_93,A_94)
      | ~ m1_subset_1(B_93,A_94)
      | v1_xboole_0(A_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_759,plain,(
    ! [B_93,A_15] :
      ( r1_tarski(B_93,A_15)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_752,c_18])).

tff(c_764,plain,(
    ! [B_95,A_96] :
      ( r1_tarski(B_95,A_96)
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_96)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_759])).

tff(c_777,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_764])).

tff(c_800,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_777,c_8])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_801,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_777,c_6])).

tff(c_955,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k3_subset_1(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_968,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_955])).

tff(c_16,plain,(
    ! [A_13,B_14] : k5_xboole_0(A_13,k4_xboole_0(B_14,A_13)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_972,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_968,c_16])).

tff(c_981,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_801,c_972])).

tff(c_533,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_577,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_587,plain,(
    k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_533,c_577])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_652,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1097,plain,(
    ! [B_108,A_109] : k5_xboole_0(B_108,k3_xboole_0(A_109,B_108)) = k4_xboole_0(B_108,A_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_652])).

tff(c_1116,plain,(
    k5_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_587,c_1097])).

tff(c_1137,plain,(
    k4_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_981,c_1116])).

tff(c_12,plain,(
    ! [A_10,B_11] : r1_tarski(k4_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1152,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1137,c_12])).

tff(c_1163,plain,(
    k3_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1152,c_8])).

tff(c_1187,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1163,c_2])).

tff(c_1201,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_800,c_1187])).

tff(c_1203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_532,c_1201])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:37:59 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.67/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.53  
% 2.99/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.53  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.99/1.53  
% 2.99/1.53  %Foreground sorts:
% 2.99/1.53  
% 2.99/1.53  
% 2.99/1.53  %Background operators:
% 2.99/1.53  
% 2.99/1.53  
% 2.99/1.53  %Foreground operators:
% 2.99/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.99/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.99/1.53  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.99/1.53  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.99/1.53  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.99/1.53  tff('#skF_3', type, '#skF_3': $i).
% 2.99/1.53  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.99/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.99/1.53  tff('#skF_4', type, '#skF_4': $i).
% 2.99/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.99/1.53  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.99/1.53  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.99/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.99/1.53  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.99/1.53  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.99/1.53  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.99/1.53  
% 2.99/1.55  tff(f_67, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.99/1.55  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_subset_1)).
% 2.99/1.55  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.99/1.55  tff(f_43, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.99/1.55  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.99/1.55  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.99/1.55  tff(f_52, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.99/1.55  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.99/1.55  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.99/1.55  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.99/1.55  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.99/1.55  tff(f_45, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.99/1.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.99/1.55  tff(f_41, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.99/1.55  tff(c_38, plain, (![A_22]: (k2_subset_1(A_22)=A_22)), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.99/1.55  tff(c_46, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.99/1.55  tff(c_54, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_46])).
% 2.99/1.55  tff(c_112, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 2.99/1.55  tff(c_10, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.99/1.55  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.99/1.55  tff(c_52, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.99/1.55  tff(c_53, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_52])).
% 2.99/1.55  tff(c_113, plain, ('#skF_3'='#skF_4'), inference(splitLeft, [status(thm)], [c_53])).
% 2.99/1.55  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.99/1.55  tff(c_114, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_113, c_44])).
% 2.99/1.55  tff(c_42, plain, (![A_25]: (~v1_xboole_0(k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.99/1.55  tff(c_284, plain, (![B_55, A_56]: (r2_hidden(B_55, A_56) | ~m1_subset_1(B_55, A_56) | v1_xboole_0(A_56))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.55  tff(c_18, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.99/1.55  tff(c_288, plain, (![B_55, A_15]: (r1_tarski(B_55, A_15) | ~m1_subset_1(B_55, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_284, c_18])).
% 2.99/1.55  tff(c_442, plain, (![B_66, A_67]: (r1_tarski(B_66, A_67) | ~m1_subset_1(B_66, k1_zfmisc_1(A_67)))), inference(negUnitSimplification, [status(thm)], [c_42, c_288])).
% 2.99/1.55  tff(c_451, plain, (r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_114, c_442])).
% 2.99/1.55  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.55  tff(c_459, plain, (k3_xboole_0('#skF_4', '#skF_4')='#skF_4'), inference(resolution, [status(thm)], [c_451, c_8])).
% 2.99/1.55  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.55  tff(c_467, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_459, c_4])).
% 2.99/1.55  tff(c_470, plain, (k4_xboole_0('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_14, c_467])).
% 2.99/1.55  tff(c_514, plain, (![A_68, B_69]: (k4_xboole_0(A_68, B_69)=k3_subset_1(A_68, B_69) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.55  tff(c_521, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_114, c_514])).
% 2.99/1.55  tff(c_524, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_470, c_521])).
% 2.99/1.55  tff(c_123, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_113, c_112])).
% 2.99/1.55  tff(c_525, plain, (~r1_tarski(k1_xboole_0, '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_524, c_123])).
% 2.99/1.55  tff(c_528, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_525])).
% 2.99/1.55  tff(c_529, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_53])).
% 2.99/1.55  tff(c_531, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_529])).
% 2.99/1.55  tff(c_532, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 2.99/1.55  tff(c_752, plain, (![B_93, A_94]: (r2_hidden(B_93, A_94) | ~m1_subset_1(B_93, A_94) | v1_xboole_0(A_94))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.99/1.55  tff(c_759, plain, (![B_93, A_15]: (r1_tarski(B_93, A_15) | ~m1_subset_1(B_93, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_752, c_18])).
% 2.99/1.55  tff(c_764, plain, (![B_95, A_96]: (r1_tarski(B_95, A_96) | ~m1_subset_1(B_95, k1_zfmisc_1(A_96)))), inference(negUnitSimplification, [status(thm)], [c_42, c_759])).
% 2.99/1.55  tff(c_777, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_764])).
% 2.99/1.55  tff(c_800, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_777, c_8])).
% 2.99/1.55  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.99/1.55  tff(c_801, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_777, c_6])).
% 2.99/1.55  tff(c_955, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k3_subset_1(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.99/1.55  tff(c_968, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_955])).
% 2.99/1.55  tff(c_16, plain, (![A_13, B_14]: (k5_xboole_0(A_13, k4_xboole_0(B_14, A_13))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.99/1.55  tff(c_972, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_968, c_16])).
% 2.99/1.55  tff(c_981, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_801, c_972])).
% 2.99/1.55  tff(c_533, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 2.99/1.55  tff(c_577, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.99/1.55  tff(c_587, plain, (k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_533, c_577])).
% 2.99/1.55  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.99/1.55  tff(c_652, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.99/1.55  tff(c_1097, plain, (![B_108, A_109]: (k5_xboole_0(B_108, k3_xboole_0(A_109, B_108))=k4_xboole_0(B_108, A_109))), inference(superposition, [status(thm), theory('equality')], [c_2, c_652])).
% 2.99/1.55  tff(c_1116, plain, (k5_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_587, c_1097])).
% 2.99/1.55  tff(c_1137, plain, (k4_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_981, c_1116])).
% 2.99/1.55  tff(c_12, plain, (![A_10, B_11]: (r1_tarski(k4_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.99/1.55  tff(c_1152, plain, (r1_tarski('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1137, c_12])).
% 2.99/1.55  tff(c_1163, plain, (k3_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(resolution, [status(thm)], [c_1152, c_8])).
% 2.99/1.55  tff(c_1187, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1163, c_2])).
% 2.99/1.55  tff(c_1201, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_800, c_1187])).
% 2.99/1.55  tff(c_1203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_532, c_1201])).
% 2.99/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.99/1.55  
% 2.99/1.55  Inference rules
% 2.99/1.55  ----------------------
% 2.99/1.55  #Ref     : 0
% 2.99/1.55  #Sup     : 288
% 2.99/1.55  #Fact    : 0
% 2.99/1.55  #Define  : 0
% 2.99/1.55  #Split   : 2
% 2.99/1.55  #Chain   : 0
% 2.99/1.55  #Close   : 0
% 2.99/1.55  
% 2.99/1.55  Ordering : KBO
% 2.99/1.55  
% 2.99/1.55  Simplification rules
% 2.99/1.55  ----------------------
% 2.99/1.55  #Subsume      : 7
% 2.99/1.55  #Demod        : 115
% 2.99/1.55  #Tautology    : 198
% 2.99/1.55  #SimpNegUnit  : 7
% 2.99/1.55  #BackRed      : 9
% 2.99/1.55  
% 2.99/1.55  #Partial instantiations: 0
% 2.99/1.55  #Strategies tried      : 1
% 2.99/1.55  
% 2.99/1.55  Timing (in seconds)
% 2.99/1.55  ----------------------
% 2.99/1.56  Preprocessing        : 0.39
% 2.99/1.56  Parsing              : 0.20
% 2.99/1.56  CNF conversion       : 0.02
% 2.99/1.56  Main loop            : 0.36
% 2.99/1.56  Inferencing          : 0.13
% 2.99/1.56  Reduction            : 0.12
% 2.99/1.56  Demodulation         : 0.09
% 2.99/1.56  BG Simplification    : 0.02
% 2.99/1.56  Subsumption          : 0.05
% 2.99/1.56  Abstraction          : 0.02
% 2.99/1.56  MUC search           : 0.00
% 2.99/1.56  Cooper               : 0.00
% 2.99/1.56  Total                : 0.78
% 2.99/1.56  Index Insertion      : 0.00
% 2.99/1.56  Index Deletion       : 0.00
% 2.99/1.56  Index Matching       : 0.00
% 2.99/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
