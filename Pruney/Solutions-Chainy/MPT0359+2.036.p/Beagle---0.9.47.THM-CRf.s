%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:14 EST 2020

% Result     : Theorem 2.94s
% Output     : CNFRefutation 2.94s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 148 expanded)
%              Number of leaves         :   27 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :  123 ( 256 expanded)
%              Number of equality atoms :   40 (  85 expanded)
%              Maximal formula depth    :    6 (   4 average)
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

tff(f_85,negated_conjecture,(
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

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_74,axiom,(
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

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_78,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k4_xboole_0(B,A))
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_xboole_1)).

tff(c_46,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_662,plain,(
    ! [A_105,B_106] :
      ( k4_xboole_0(A_105,B_106) = k3_subset_1(A_105,B_106)
      | ~ m1_subset_1(B_106,k1_zfmisc_1(A_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_679,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_46,c_662])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_36,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_48,plain,
    ( k2_subset_1('#skF_3') != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_56,plain,
    ( '#skF_3' != '#skF_4'
    | ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_48])).

tff(c_70,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_54,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | k2_subset_1('#skF_3') = '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,
    ( r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4')
    | '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_54])).

tff(c_78,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_55])).

tff(c_80,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_46])).

tff(c_311,plain,(
    ! [A_63,B_64] :
      ( m1_subset_1(k3_subset_1(A_63,B_64),k1_zfmisc_1(A_63))
      | ~ m1_subset_1(B_64,k1_zfmisc_1(A_63)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_42,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_zfmisc_1(A_20)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_195,plain,(
    ! [B_49,A_50] :
      ( r2_hidden(B_49,A_50)
      | ~ m1_subset_1(B_49,A_50)
      | v1_xboole_0(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_16,plain,(
    ! [C_12,A_8] :
      ( r1_tarski(C_12,A_8)
      | ~ r2_hidden(C_12,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_202,plain,(
    ! [B_49,A_8] :
      ( r1_tarski(B_49,A_8)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_195,c_16])).

tff(c_206,plain,(
    ! [B_49,A_8] :
      ( r1_tarski(B_49,A_8)
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_8)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_202])).

tff(c_330,plain,(
    ! [A_65,B_66] :
      ( r1_tarski(k3_subset_1(A_65,B_66),A_65)
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_311,c_206])).

tff(c_79,plain,(
    ~ r1_tarski(k3_subset_1('#skF_4','#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_70])).

tff(c_345,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_330,c_79])).

tff(c_359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_345])).

tff(c_360,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_476,plain,(
    ! [B_85,A_86] :
      ( r2_hidden(B_85,A_86)
      | ~ m1_subset_1(B_85,A_86)
      | v1_xboole_0(A_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_480,plain,(
    ! [B_85,A_8] :
      ( r1_tarski(B_85,A_8)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8)) ) ),
    inference(resolution,[status(thm)],[c_476,c_16])).

tff(c_484,plain,(
    ! [B_87,A_88] :
      ( r1_tarski(B_87,A_88)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_480])).

tff(c_493,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_46,c_484])).

tff(c_525,plain,(
    ! [B_93,A_94] :
      ( B_93 = A_94
      | ~ r1_tarski(B_93,A_94)
      | ~ r1_tarski(A_94,B_93) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_527,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_493,c_525])).

tff(c_538,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(negUnitSimplification,[status(thm)],[c_360,c_527])).

tff(c_549,plain,(
    k4_xboole_0('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_538])).

tff(c_692,plain,(
    k3_subset_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_679,c_549])).

tff(c_361,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_4') ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_381,plain,(
    ! [A_77,B_78] :
      ( k4_xboole_0(A_77,B_78) = k1_xboole_0
      | ~ r1_tarski(A_77,B_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_395,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_361,c_381])).

tff(c_716,plain,(
    ! [A_108,B_109] :
      ( k3_subset_1(A_108,k3_subset_1(A_108,B_109)) = B_109
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_108)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_729,plain,(
    k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(resolution,[status(thm)],[c_46,c_716])).

tff(c_599,plain,(
    ! [A_99,B_100] :
      ( m1_subset_1(k3_subset_1(A_99,B_100),k1_zfmisc_1(A_99))
      | ~ m1_subset_1(B_100,k1_zfmisc_1(A_99)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_483,plain,(
    ! [B_85,A_8] :
      ( r1_tarski(B_85,A_8)
      | ~ m1_subset_1(B_85,k1_zfmisc_1(A_8)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_480])).

tff(c_608,plain,(
    ! [A_101,B_102] :
      ( r1_tarski(k3_subset_1(A_101,B_102),A_101)
      | ~ m1_subset_1(B_102,k1_zfmisc_1(A_101)) ) ),
    inference(resolution,[status(thm)],[c_599,c_483])).

tff(c_10,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1204,plain,(
    ! [A_131,B_132] :
      ( k4_xboole_0(k3_subset_1(A_131,B_132),A_131) = k1_xboole_0
      | ~ m1_subset_1(B_132,k1_zfmisc_1(A_131)) ) ),
    inference(resolution,[status(thm)],[c_608,c_10])).

tff(c_1225,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_46,c_1204])).

tff(c_18,plain,(
    ! [C_12,A_8] :
      ( r2_hidden(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_505,plain,(
    ! [B_89,A_90] :
      ( m1_subset_1(B_89,A_90)
      | ~ r2_hidden(B_89,A_90)
      | v1_xboole_0(A_90) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_511,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | v1_xboole_0(k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(resolution,[status(thm)],[c_18,c_505])).

tff(c_515,plain,(
    ! [C_12,A_8] :
      ( m1_subset_1(C_12,k1_zfmisc_1(A_8))
      | ~ r1_tarski(C_12,A_8) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_511])).

tff(c_742,plain,(
    ! [A_110,C_111] :
      ( k4_xboole_0(A_110,C_111) = k3_subset_1(A_110,C_111)
      | ~ r1_tarski(C_111,A_110) ) ),
    inference(resolution,[status(thm)],[c_515,c_662])).

tff(c_1301,plain,(
    ! [B_135,A_136] :
      ( k4_xboole_0(B_135,A_136) = k3_subset_1(B_135,A_136)
      | k4_xboole_0(A_136,B_135) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_742])).

tff(c_1305,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1225,c_1301])).

tff(c_1322,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_3','#skF_4')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_1305])).

tff(c_405,plain,(
    ! [A_80,B_81] :
      ( k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,k4_xboole_0(B_81,A_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_417,plain,(
    ! [A_3,B_81] :
      ( k1_xboole_0 = A_3
      | k4_xboole_0(A_3,k4_xboole_0(B_81,A_3)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_405])).

tff(c_1342,plain,
    ( k3_subset_1('#skF_3','#skF_4') = k1_xboole_0
    | k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_4') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_1322,c_417])).

tff(c_1352,plain,(
    k3_subset_1('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_395,c_1342])).

tff(c_1354,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_692,c_1352])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n024.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:05:21 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.94/1.45  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.45  
% 2.94/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.45  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.94/1.45  
% 2.94/1.45  %Foreground sorts:
% 2.94/1.45  
% 2.94/1.45  
% 2.94/1.45  %Background operators:
% 2.94/1.45  
% 2.94/1.45  
% 2.94/1.45  %Foreground operators:
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.94/1.45  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.94/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.94/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.94/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.94/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.94/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.94/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.94/1.45  tff('#skF_4', type, '#skF_4': $i).
% 2.94/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.94/1.45  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.94/1.45  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.94/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.94/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.94/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.94/1.45  
% 2.94/1.47  tff(f_85, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 2.94/1.47  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.94/1.47  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.94/1.47  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.94/1.47  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.94/1.47  tff(f_74, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.94/1.47  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 2.94/1.47  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.94/1.47  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.94/1.47  tff(f_78, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.94/1.47  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k4_xboole_0(B, A)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_xboole_1)).
% 2.94/1.47  tff(c_46, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.94/1.47  tff(c_662, plain, (![A_105, B_106]: (k4_xboole_0(A_105, B_106)=k3_subset_1(A_105, B_106) | ~m1_subset_1(B_106, k1_zfmisc_1(A_105)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.94/1.47  tff(c_679, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_46, c_662])).
% 2.94/1.47  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | k4_xboole_0(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.47  tff(c_36, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.94/1.47  tff(c_48, plain, (k2_subset_1('#skF_3')!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.94/1.47  tff(c_56, plain, ('#skF_3'!='#skF_4' | ~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_48])).
% 2.94/1.47  tff(c_70, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitLeft, [status(thm)], [c_56])).
% 2.94/1.47  tff(c_54, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | k2_subset_1('#skF_3')='#skF_4'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.94/1.47  tff(c_55, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4') | '#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_54])).
% 2.94/1.47  tff(c_78, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_70, c_55])).
% 2.94/1.47  tff(c_80, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_46])).
% 2.94/1.47  tff(c_311, plain, (![A_63, B_64]: (m1_subset_1(k3_subset_1(A_63, B_64), k1_zfmisc_1(A_63)) | ~m1_subset_1(B_64, k1_zfmisc_1(A_63)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.94/1.47  tff(c_42, plain, (![A_20]: (~v1_xboole_0(k1_zfmisc_1(A_20)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.94/1.47  tff(c_195, plain, (![B_49, A_50]: (r2_hidden(B_49, A_50) | ~m1_subset_1(B_49, A_50) | v1_xboole_0(A_50))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.94/1.47  tff(c_16, plain, (![C_12, A_8]: (r1_tarski(C_12, A_8) | ~r2_hidden(C_12, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.47  tff(c_202, plain, (![B_49, A_8]: (r1_tarski(B_49, A_8) | ~m1_subset_1(B_49, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_195, c_16])).
% 2.94/1.47  tff(c_206, plain, (![B_49, A_8]: (r1_tarski(B_49, A_8) | ~m1_subset_1(B_49, k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_42, c_202])).
% 2.94/1.47  tff(c_330, plain, (![A_65, B_66]: (r1_tarski(k3_subset_1(A_65, B_66), A_65) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_311, c_206])).
% 2.94/1.47  tff(c_79, plain, (~r1_tarski(k3_subset_1('#skF_4', '#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_78, c_70])).
% 2.94/1.47  tff(c_345, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_330, c_79])).
% 2.94/1.47  tff(c_359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_80, c_345])).
% 2.94/1.47  tff(c_360, plain, ('#skF_3'!='#skF_4'), inference(splitRight, [status(thm)], [c_56])).
% 2.94/1.47  tff(c_476, plain, (![B_85, A_86]: (r2_hidden(B_85, A_86) | ~m1_subset_1(B_85, A_86) | v1_xboole_0(A_86))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.94/1.47  tff(c_480, plain, (![B_85, A_8]: (r1_tarski(B_85, A_8) | ~m1_subset_1(B_85, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)))), inference(resolution, [status(thm)], [c_476, c_16])).
% 2.94/1.47  tff(c_484, plain, (![B_87, A_88]: (r1_tarski(B_87, A_88) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)))), inference(negUnitSimplification, [status(thm)], [c_42, c_480])).
% 2.94/1.47  tff(c_493, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_46, c_484])).
% 2.94/1.47  tff(c_525, plain, (![B_93, A_94]: (B_93=A_94 | ~r1_tarski(B_93, A_94) | ~r1_tarski(A_94, B_93))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.94/1.47  tff(c_527, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_493, c_525])).
% 2.94/1.47  tff(c_538, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(negUnitSimplification, [status(thm)], [c_360, c_527])).
% 2.94/1.47  tff(c_549, plain, (k4_xboole_0('#skF_3', '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_8, c_538])).
% 2.94/1.47  tff(c_692, plain, (k3_subset_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_679, c_549])).
% 2.94/1.47  tff(c_361, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')), inference(splitRight, [status(thm)], [c_56])).
% 2.94/1.47  tff(c_381, plain, (![A_77, B_78]: (k4_xboole_0(A_77, B_78)=k1_xboole_0 | ~r1_tarski(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.47  tff(c_395, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_361, c_381])).
% 2.94/1.47  tff(c_716, plain, (![A_108, B_109]: (k3_subset_1(A_108, k3_subset_1(A_108, B_109))=B_109 | ~m1_subset_1(B_109, k1_zfmisc_1(A_108)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.94/1.47  tff(c_729, plain, (k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(resolution, [status(thm)], [c_46, c_716])).
% 2.94/1.47  tff(c_599, plain, (![A_99, B_100]: (m1_subset_1(k3_subset_1(A_99, B_100), k1_zfmisc_1(A_99)) | ~m1_subset_1(B_100, k1_zfmisc_1(A_99)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.94/1.47  tff(c_483, plain, (![B_85, A_8]: (r1_tarski(B_85, A_8) | ~m1_subset_1(B_85, k1_zfmisc_1(A_8)))), inference(negUnitSimplification, [status(thm)], [c_42, c_480])).
% 2.94/1.47  tff(c_608, plain, (![A_101, B_102]: (r1_tarski(k3_subset_1(A_101, B_102), A_101) | ~m1_subset_1(B_102, k1_zfmisc_1(A_101)))), inference(resolution, [status(thm)], [c_599, c_483])).
% 2.94/1.47  tff(c_10, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.94/1.47  tff(c_1204, plain, (![A_131, B_132]: (k4_xboole_0(k3_subset_1(A_131, B_132), A_131)=k1_xboole_0 | ~m1_subset_1(B_132, k1_zfmisc_1(A_131)))), inference(resolution, [status(thm)], [c_608, c_10])).
% 2.94/1.47  tff(c_1225, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_46, c_1204])).
% 2.94/1.47  tff(c_18, plain, (![C_12, A_8]: (r2_hidden(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.94/1.47  tff(c_505, plain, (![B_89, A_90]: (m1_subset_1(B_89, A_90) | ~r2_hidden(B_89, A_90) | v1_xboole_0(A_90))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.94/1.47  tff(c_511, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | v1_xboole_0(k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(resolution, [status(thm)], [c_18, c_505])).
% 2.94/1.47  tff(c_515, plain, (![C_12, A_8]: (m1_subset_1(C_12, k1_zfmisc_1(A_8)) | ~r1_tarski(C_12, A_8))), inference(negUnitSimplification, [status(thm)], [c_42, c_511])).
% 2.94/1.47  tff(c_742, plain, (![A_110, C_111]: (k4_xboole_0(A_110, C_111)=k3_subset_1(A_110, C_111) | ~r1_tarski(C_111, A_110))), inference(resolution, [status(thm)], [c_515, c_662])).
% 2.94/1.47  tff(c_1301, plain, (![B_135, A_136]: (k4_xboole_0(B_135, A_136)=k3_subset_1(B_135, A_136) | k4_xboole_0(A_136, B_135)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_742])).
% 2.94/1.47  tff(c_1305, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1225, c_1301])).
% 2.94/1.47  tff(c_1322, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_3', '#skF_4'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_729, c_1305])).
% 2.94/1.47  tff(c_405, plain, (![A_80, B_81]: (k1_xboole_0=A_80 | ~r1_tarski(A_80, k4_xboole_0(B_81, A_80)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.94/1.47  tff(c_417, plain, (![A_3, B_81]: (k1_xboole_0=A_3 | k4_xboole_0(A_3, k4_xboole_0(B_81, A_3))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_405])).
% 2.94/1.47  tff(c_1342, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0 | k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_4')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_1322, c_417])).
% 2.94/1.47  tff(c_1352, plain, (k3_subset_1('#skF_3', '#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_395, c_1342])).
% 2.94/1.47  tff(c_1354, plain, $false, inference(negUnitSimplification, [status(thm)], [c_692, c_1352])).
% 2.94/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.94/1.47  
% 2.94/1.47  Inference rules
% 2.94/1.47  ----------------------
% 2.94/1.47  #Ref     : 0
% 2.94/1.47  #Sup     : 290
% 2.94/1.47  #Fact    : 0
% 2.94/1.47  #Define  : 0
% 2.94/1.47  #Split   : 3
% 2.94/1.47  #Chain   : 0
% 2.94/1.47  #Close   : 0
% 2.94/1.47  
% 2.94/1.47  Ordering : KBO
% 2.94/1.47  
% 2.94/1.47  Simplification rules
% 2.94/1.47  ----------------------
% 2.94/1.47  #Subsume      : 52
% 2.94/1.47  #Demod        : 105
% 2.94/1.47  #Tautology    : 160
% 2.94/1.47  #SimpNegUnit  : 13
% 2.94/1.47  #BackRed      : 10
% 2.94/1.47  
% 2.94/1.47  #Partial instantiations: 0
% 2.94/1.47  #Strategies tried      : 1
% 2.94/1.47  
% 2.94/1.47  Timing (in seconds)
% 2.94/1.47  ----------------------
% 2.94/1.47  Preprocessing        : 0.31
% 2.94/1.47  Parsing              : 0.16
% 2.94/1.47  CNF conversion       : 0.02
% 2.94/1.47  Main loop            : 0.39
% 2.94/1.47  Inferencing          : 0.14
% 2.94/1.47  Reduction            : 0.12
% 2.94/1.47  Demodulation         : 0.08
% 2.94/1.47  BG Simplification    : 0.02
% 2.94/1.47  Subsumption          : 0.08
% 2.94/1.47  Abstraction          : 0.02
% 2.94/1.47  MUC search           : 0.00
% 2.94/1.47  Cooper               : 0.00
% 2.94/1.47  Total                : 0.74
% 2.94/1.47  Index Insertion      : 0.00
% 2.94/1.47  Index Deletion       : 0.00
% 2.94/1.48  Index Matching       : 0.00
% 2.94/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------
