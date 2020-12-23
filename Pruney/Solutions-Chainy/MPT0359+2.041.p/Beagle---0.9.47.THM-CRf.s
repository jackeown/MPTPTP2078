%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:14 EST 2020

% Result     : Theorem 3.06s
% Output     : CNFRefutation 3.06s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 148 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :    9
%              Number of atoms          :  117 ( 234 expanded)
%              Number of equality atoms :   47 (  97 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ( r1_tarski(k3_subset_1(A,B),B)
        <=> B = k2_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_subset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_70,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_667,plain,(
    ! [A_99,B_100] :
      ( k4_xboole_0(A_99,B_100) = k3_subset_1(A_99,B_100)
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_680,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_667])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k1_xboole_0
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_96,plain,(
    ! [B_35] : k4_xboole_0(B_35,B_35) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_12,plain,(
    ! [A_5,B_6] : r1_tarski(k4_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    ! [B_38] : r1_tarski(k1_xboole_0,B_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_12])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_119,plain,(
    ! [B_38] : k4_xboole_0(k1_xboole_0,B_38) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_115,c_10])).

tff(c_95,plain,(
    ! [B_2] : k4_xboole_0(B_2,B_2) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_6,c_87])).

tff(c_36,plain,(
    ! [A_16] : k2_subset_1(A_16) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_54,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_46])).

tff(c_69,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_53,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_52])).

tff(c_70,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_53])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_44])).

tff(c_351,plain,(
    ! [A_64,B_65] :
      ( k4_xboole_0(A_64,B_65) = k3_subset_1(A_64,B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_357,plain,(
    k4_xboole_0('#skF_4','#skF_4') = k3_subset_1('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_351])).

tff(c_364,plain,(
    k3_subset_1('#skF_4','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_357])).

tff(c_106,plain,(
    ! [A_36,B_37] :
      ( r1_tarski(A_36,B_37)
      | k4_xboole_0(A_36,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_71,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_69])).

tff(c_114,plain,(
    k4_xboole_0(k3_subset_1('#skF_4','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_106,c_71])).

tff(c_377,plain,(
    k4_xboole_0(k1_xboole_0,'#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_364,c_114])).

tff(c_381,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_377])).

tff(c_382,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_40,plain,(
    ! [A_19] : ~ v1_xboole_0(k1_zfmisc_1(A_19)) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_559,plain,(
    ! [B_87,A_88] :
      ( r2_hidden(B_87,A_88)
      | ~ m1_subset_1(B_87,A_88)
      | v1_xboole_0(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [C_13,A_9] :
      ( r1_tarski(C_13,A_9)
      | ~ r2_hidden(C_13,k1_zfmisc_1(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_563,plain,(
    ! [B_87,A_9] :
      ( r1_tarski(B_87,A_9)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9)) ) ),
    inference(resolution,[status(thm)],[c_559,c_16])).

tff(c_578,plain,(
    ! [B_91,A_92] :
      ( r1_tarski(B_91,A_92)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_92)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_563])).

tff(c_587,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_578])).

tff(c_607,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_609,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_587,c_607])).

tff(c_622,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_382,c_609])).

tff(c_634,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_622])).

tff(c_685,plain,(
    k3_subset_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_680,c_634])).

tff(c_383,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_396,plain,(
    ! [A_72,B_73] :
      ( k4_xboole_0(A_72,B_73) = k1_xboole_0
      | ~ r1_tarski(A_72,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_406,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_383,c_396])).

tff(c_762,plain,(
    ! [A_103,B_104] :
      ( k3_subset_1(A_103,k3_subset_1(A_103,B_104)) = B_104
      | ~ m1_subset_1(B_104,k1_zfmisc_1(A_103)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_772,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_44,c_762])).

tff(c_698,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_680,c_12])).

tff(c_18,plain,(
    ! [C_13,A_9] :
      ( r2_hidden(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_567,plain,(
    ! [B_89,A_90] :
      ( m1_subset_1(B_89,A_90)
      | ~ r2_hidden(B_89,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_573,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | v1_xboole_0(k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(resolution,[status(thm)],[c_18,c_567])).

tff(c_577,plain,(
    ! [C_13,A_9] :
      ( m1_subset_1(C_13,k1_zfmisc_1(A_9))
      | ~ r1_tarski(C_13,A_9) ) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_573])).

tff(c_874,plain,(
    ! [A_111,C_112] :
      ( k4_xboole_0(A_111,C_112) = k3_subset_1(A_111,C_112)
      | ~ r1_tarski(C_112,A_111) ) ),
    inference(resolution,[status(thm)],[c_577,c_667])).

tff(c_877,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_698,c_874])).

tff(c_897,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_772,c_877])).

tff(c_525,plain,(
    ! [A_84,B_85] :
      ( r1_tarski(A_84,B_85)
      | k4_xboole_0(A_84,B_85) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_7,B_8] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k4_xboole_0(B_8,A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_539,plain,(
    ! [A_84,B_8] :
      ( k1_xboole_0 = A_84
      | k4_xboole_0(A_84,k4_xboole_0(B_8,A_84)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_525,c_14])).

tff(c_949,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_897,c_539])).

tff(c_964,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_406,c_949])).

tff(c_966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_685,c_964])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:24:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.06/1.48  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  
% 3.06/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.49  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.06/1.49  
% 3.06/1.49  %Foreground sorts:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Background operators:
% 3.06/1.49  
% 3.06/1.49  
% 3.06/1.49  %Foreground operators:
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.06/1.49  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.06/1.49  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.06/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.06/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.06/1.49  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.06/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.06/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.06/1.49  tff('#skF_4', type, '#skF_4': $i).
% 3.06/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.06/1.49  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.06/1.49  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.06/1.49  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.06/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.06/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.06/1.49  
% 3.06/1.50  tff(f_81, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 3.06/1.50  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.06/1.50  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.06/1.50  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.06/1.50  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.06/1.50  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.06/1.50  tff(f_70, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 3.06/1.50  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.06/1.50  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 3.06/1.50  tff(f_74, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.06/1.50  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 3.06/1.50  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.06/1.50  tff(c_667, plain, (![A_99, B_100]: (k4_xboole_0(A_99, B_100)=k3_subset_1(A_99, B_100) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.50  tff(c_680, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_44, c_667])).
% 3.06/1.50  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.50  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.50  tff(c_87, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k1_xboole_0 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.50  tff(c_96, plain, (![B_35]: (k4_xboole_0(B_35, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_87])).
% 3.06/1.50  tff(c_12, plain, (![A_5, B_6]: (r1_tarski(k4_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.06/1.50  tff(c_115, plain, (![B_38]: (r1_tarski(k1_xboole_0, B_38))), inference(superposition, [status(thm), theory('equality')], [c_96, c_12])).
% 3.06/1.50  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.50  tff(c_119, plain, (![B_38]: (k4_xboole_0(k1_xboole_0, B_38)=k1_xboole_0)), inference(resolution, [status(thm)], [c_115, c_10])).
% 3.06/1.50  tff(c_95, plain, (![B_2]: (k4_xboole_0(B_2, B_2)=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_87])).
% 3.06/1.50  tff(c_36, plain, (![A_16]: (k2_subset_1(A_16)=A_16)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.06/1.50  tff(c_46, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.06/1.50  tff(c_54, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_46])).
% 3.06/1.50  tff(c_69, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_54])).
% 3.06/1.50  tff(c_52, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.06/1.50  tff(c_53, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_52])).
% 3.06/1.50  tff(c_70, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_69, c_53])).
% 3.06/1.50  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_70, c_44])).
% 3.06/1.50  tff(c_351, plain, (![A_64, B_65]: (k4_xboole_0(A_64, B_65)=k3_subset_1(A_64, B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_64)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.06/1.50  tff(c_357, plain, (k4_xboole_0('#skF_4', '#skF_4')=k3_subset_1('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_351])).
% 3.06/1.50  tff(c_364, plain, (k3_subset_1('#skF_4', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_95, c_357])).
% 3.06/1.50  tff(c_106, plain, (![A_36, B_37]: (r1_tarski(A_36, B_37) | k4_xboole_0(A_36, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.50  tff(c_71, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_69])).
% 3.06/1.50  tff(c_114, plain, (k4_xboole_0(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_106, c_71])).
% 3.06/1.50  tff(c_377, plain, (k4_xboole_0(k1_xboole_0, '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_364, c_114])).
% 3.06/1.50  tff(c_381, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_119, c_377])).
% 3.06/1.50  tff(c_382, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_54])).
% 3.06/1.50  tff(c_40, plain, (![A_19]: (~v1_xboole_0(k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.06/1.50  tff(c_559, plain, (![B_87, A_88]: (r2_hidden(B_87, A_88) | ~m1_subset_1(B_87, A_88) | v1_xboole_0(A_88))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.50  tff(c_16, plain, (![C_13, A_9]: (r1_tarski(C_13, A_9) | ~r2_hidden(C_13, k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.50  tff(c_563, plain, (![B_87, A_9]: (r1_tarski(B_87, A_9) | ~m1_subset_1(B_87, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)))), inference(resolution, [status(thm)], [c_559, c_16])).
% 3.06/1.50  tff(c_578, plain, (![B_91, A_92]: (r1_tarski(B_91, A_92) | ~m1_subset_1(B_91, k1_zfmisc_1(A_92)))), inference(negUnitSimplification, [status(thm)], [c_40, c_563])).
% 3.06/1.50  tff(c_587, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_578])).
% 3.06/1.50  tff(c_607, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.06/1.50  tff(c_609, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_587, c_607])).
% 3.06/1.50  tff(c_622, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_382, c_609])).
% 3.06/1.50  tff(c_634, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_622])).
% 3.06/1.50  tff(c_685, plain, (k3_subset_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_680, c_634])).
% 3.06/1.50  tff(c_383, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_54])).
% 3.06/1.50  tff(c_396, plain, (![A_72, B_73]: (k4_xboole_0(A_72, B_73)=k1_xboole_0 | ~r1_tarski(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.50  tff(c_406, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_383, c_396])).
% 3.06/1.50  tff(c_762, plain, (![A_103, B_104]: (k3_subset_1(A_103, k3_subset_1(A_103, B_104))=B_104 | ~m1_subset_1(B_104, k1_zfmisc_1(A_103)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.06/1.50  tff(c_772, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_44, c_762])).
% 3.06/1.50  tff(c_698, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_680, c_12])).
% 3.06/1.50  tff(c_18, plain, (![C_13, A_9]: (r2_hidden(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.06/1.50  tff(c_567, plain, (![B_89, A_90]: (m1_subset_1(B_89, A_90) | ~r2_hidden(B_89, A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.06/1.50  tff(c_573, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | v1_xboole_0(k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(resolution, [status(thm)], [c_18, c_567])).
% 3.06/1.50  tff(c_577, plain, (![C_13, A_9]: (m1_subset_1(C_13, k1_zfmisc_1(A_9)) | ~r1_tarski(C_13, A_9))), inference(negUnitSimplification, [status(thm)], [c_40, c_573])).
% 3.06/1.50  tff(c_874, plain, (![A_111, C_112]: (k4_xboole_0(A_111, C_112)=k3_subset_1(A_111, C_112) | ~r1_tarski(C_112, A_111))), inference(resolution, [status(thm)], [c_577, c_667])).
% 3.06/1.50  tff(c_877, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_698, c_874])).
% 3.06/1.50  tff(c_897, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_772, c_877])).
% 3.06/1.50  tff(c_525, plain, (![A_84, B_85]: (r1_tarski(A_84, B_85) | k4_xboole_0(A_84, B_85)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.06/1.50  tff(c_14, plain, (![A_7, B_8]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k4_xboole_0(B_8, A_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.06/1.50  tff(c_539, plain, (![A_84, B_8]: (k1_xboole_0=A_84 | k4_xboole_0(A_84, k4_xboole_0(B_8, A_84))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_525, c_14])).
% 3.06/1.50  tff(c_949, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_897, c_539])).
% 3.06/1.50  tff(c_964, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_406, c_949])).
% 3.06/1.50  tff(c_966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_685, c_964])).
% 3.06/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.06/1.50  
% 3.06/1.50  Inference rules
% 3.06/1.50  ----------------------
% 3.06/1.50  #Ref     : 0
% 3.06/1.50  #Sup     : 207
% 3.06/1.50  #Fact    : 0
% 3.06/1.50  #Define  : 0
% 3.06/1.50  #Split   : 3
% 3.06/1.50  #Chain   : 0
% 3.06/1.50  #Close   : 0
% 3.06/1.51  
% 3.06/1.51  Ordering : KBO
% 3.06/1.51  
% 3.06/1.51  Simplification rules
% 3.06/1.51  ----------------------
% 3.06/1.51  #Subsume      : 42
% 3.06/1.51  #Demod        : 66
% 3.06/1.51  #Tautology    : 104
% 3.06/1.51  #SimpNegUnit  : 12
% 3.06/1.51  #BackRed      : 6
% 3.06/1.51  
% 3.06/1.51  #Partial instantiations: 0
% 3.06/1.51  #Strategies tried      : 1
% 3.06/1.51  
% 3.06/1.51  Timing (in seconds)
% 3.06/1.51  ----------------------
% 3.06/1.51  Preprocessing        : 0.34
% 3.06/1.51  Parsing              : 0.17
% 3.06/1.51  CNF conversion       : 0.02
% 3.06/1.51  Main loop            : 0.34
% 3.06/1.51  Inferencing          : 0.13
% 3.06/1.51  Reduction            : 0.11
% 3.06/1.51  Demodulation         : 0.07
% 3.06/1.51  BG Simplification    : 0.02
% 3.06/1.51  Subsumption          : 0.06
% 3.06/1.51  Abstraction          : 0.02
% 3.06/1.51  MUC search           : 0.00
% 3.06/1.51  Cooper               : 0.00
% 3.06/1.51  Total                : 0.72
% 3.06/1.51  Index Insertion      : 0.00
% 3.06/1.51  Index Deletion       : 0.00
% 3.06/1.51  Index Matching       : 0.00
% 3.06/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
