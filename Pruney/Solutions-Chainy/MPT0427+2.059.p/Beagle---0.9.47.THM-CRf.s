%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:04 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 240 expanded)
%              Number of leaves         :   27 (  88 expanded)
%              Depth                    :    9
%              Number of atoms          :  106 ( 491 expanded)
%              Number of equality atoms :   46 ( 215 expanded)
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

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => ( ( B != k1_xboole_0
         => k8_setfam_1(A,B) = k6_setfam_1(A,B) )
        & ( B = k1_xboole_0
         => k8_setfam_1(A,B) = A ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_setfam_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => m1_subset_1(k8_setfam_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k8_setfam_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_96,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(k1_zfmisc_1(A)))
           => ( r1_tarski(B,C)
             => r1_tarski(k8_setfam_1(A,C),k8_setfam_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_setfam_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(k1_zfmisc_1(A)))
     => k6_setfam_1(A,B) = k1_setfam_1(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_setfam_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_86,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => ( A = k1_xboole_0
        | r1_tarski(k1_setfam_1(B),k1_setfam_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_setfam_1)).

tff(c_14,plain,(
    ! [A_8] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    ! [A_9] :
      ( k8_setfam_1(A_9,k1_xboole_0) = A_9
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_40,plain,(
    ! [A_9] : k8_setfam_1(A_9,k1_xboole_0) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_16])).

tff(c_805,plain,(
    ! [A_109,B_110] :
      ( m1_subset_1(k8_setfam_1(A_109,B_110),k1_zfmisc_1(A_109))
      | ~ m1_subset_1(B_110,k1_zfmisc_1(k1_zfmisc_1(A_109))) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_817,plain,(
    ! [A_9] :
      ( m1_subset_1(A_9,k1_zfmisc_1(A_9))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_zfmisc_1(A_9))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_805])).

tff(c_823,plain,(
    ! [A_111] : m1_subset_1(A_111,k1_zfmisc_1(A_111)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_817])).

tff(c_24,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_835,plain,(
    ! [A_111] : r1_tarski(A_111,A_111) ),
    inference(resolution,[status(thm)],[c_823,c_24])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_684,plain,(
    ! [A_98,B_99] :
      ( k6_setfam_1(A_98,B_99) = k1_setfam_1(B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(k1_zfmisc_1(A_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_700,plain,(
    k6_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_684])).

tff(c_923,plain,(
    ! [A_120,B_121] :
      ( k8_setfam_1(A_120,B_121) = k6_setfam_1(A_120,B_121)
      | k1_xboole_0 = B_121
      | ~ m1_subset_1(B_121,k1_zfmisc_1(k1_zfmisc_1(A_120))) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_938,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k6_setfam_1('#skF_1','#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_36,c_923])).

tff(c_951,plain,
    ( k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3')
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_700,c_938])).

tff(c_987,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_951])).

tff(c_38,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1(k1_zfmisc_1('#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_701,plain,(
    k6_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_684])).

tff(c_941,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k6_setfam_1('#skF_1','#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_38,c_923])).

tff(c_953,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_701,c_941])).

tff(c_1019,plain,
    ( k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2')
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_953])).

tff(c_1020,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_1019])).

tff(c_32,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1027,plain,(
    ~ r1_tarski(k8_setfam_1('#skF_1','#skF_3'),k8_setfam_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1020,c_32])).

tff(c_1035,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_835,c_1027])).

tff(c_1037,plain,(
    '#skF_2' != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_1019])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1012,plain,(
    ! [A_1] : k4_xboole_0('#skF_3',A_1) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_987,c_2])).

tff(c_34,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_12,plain,(
    ! [A_6,B_7] :
      ( r1_xboole_0(A_6,B_7)
      | k4_xboole_0(A_6,B_7) != A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_106,plain,(
    ! [A_37,C_38,B_39] :
      ( r1_xboole_0(A_37,C_38)
      | ~ r1_xboole_0(B_39,C_38)
      | ~ r1_tarski(A_37,B_39) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1216,plain,(
    ! [A_135,B_136,A_137] :
      ( r1_xboole_0(A_135,B_136)
      | ~ r1_tarski(A_135,A_137)
      | k4_xboole_0(A_137,B_136) != A_137 ) ),
    inference(resolution,[status(thm)],[c_12,c_106])).

tff(c_1228,plain,(
    ! [B_136] :
      ( r1_xboole_0('#skF_2',B_136)
      | k4_xboole_0('#skF_3',B_136) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_34,c_1216])).

tff(c_1238,plain,(
    ! [B_138] : r1_xboole_0('#skF_2',B_138) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1012,c_1228])).

tff(c_8,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | k1_xboole_0 = A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1009,plain,(
    ! [A_5] :
      ( ~ r1_xboole_0(A_5,A_5)
      | A_5 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_987,c_8])).

tff(c_1242,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1238,c_1009])).

tff(c_1251,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1037,c_1242])).

tff(c_1252,plain,(
    k8_setfam_1('#skF_1','#skF_3') = k1_setfam_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_951])).

tff(c_881,plain,(
    ! [A_118,B_119] :
      ( r1_tarski(k8_setfam_1(A_118,B_119),A_118)
      | ~ m1_subset_1(B_119,k1_zfmisc_1(k1_zfmisc_1(A_118))) ) ),
    inference(resolution,[status(thm)],[c_805,c_24])).

tff(c_901,plain,(
    r1_tarski(k8_setfam_1('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_881])).

tff(c_1254,plain,(
    r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_901])).

tff(c_1282,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_953])).

tff(c_1306,plain,(
    ! [A_9] : k8_setfam_1(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1282,c_40])).

tff(c_1255,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k8_setfam_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_32])).

tff(c_1339,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1306,c_1255])).

tff(c_1343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1254,c_1339])).

tff(c_1345,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_30,plain,(
    ! [B_21,A_20] :
      ( r1_tarski(k1_setfam_1(B_21),k1_setfam_1(A_20))
      | k1_xboole_0 = A_20
      | ~ r1_tarski(A_20,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1344,plain,(
    k8_setfam_1('#skF_1','#skF_2') = k1_setfam_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_953])).

tff(c_1346,plain,(
    ~ r1_tarski(k1_setfam_1('#skF_3'),k1_setfam_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1344,c_1255])).

tff(c_1359,plain,
    ( k1_xboole_0 = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_30,c_1346])).

tff(c_1362,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1359])).

tff(c_1364,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1345,c_1362])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:25:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.49  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.50  
% 3.18/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.50  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > k8_setfam_1 > k6_setfam_1 > k4_xboole_0 > #nlpp > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.50  
% 3.18/1.50  %Foreground sorts:
% 3.18/1.50  
% 3.18/1.50  
% 3.18/1.50  %Background operators:
% 3.18/1.50  
% 3.18/1.50  
% 3.18/1.50  %Foreground operators:
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.50  tff(k8_setfam_1, type, k8_setfam_1: ($i * $i) > $i).
% 3.18/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.50  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.50  tff(k6_setfam_1, type, k6_setfam_1: ($i * $i) > $i).
% 3.18/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.18/1.50  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.18/1.50  
% 3.18/1.52  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.18/1.52  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => ((~(B = k1_xboole_0) => (k8_setfam_1(A, B) = k6_setfam_1(A, B))) & ((B = k1_xboole_0) => (k8_setfam_1(A, B) = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_setfam_1)).
% 3.18/1.52  tff(f_66, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => m1_subset_1(k8_setfam_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k8_setfam_1)).
% 3.18/1.52  tff(f_74, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.18/1.52  tff(f_96, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k1_zfmisc_1(A))) => (r1_tarski(B, C) => r1_tarski(k8_setfam_1(A, C), k8_setfam_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_setfam_1)).
% 3.18/1.52  tff(f_70, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(k1_zfmisc_1(A))) => (k6_setfam_1(A, B) = k1_setfam_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_setfam_1)).
% 3.18/1.52  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 3.18/1.52  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.18/1.52  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.18/1.52  tff(f_45, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.18/1.52  tff(f_86, axiom, (![A, B]: (r1_tarski(A, B) => ((A = k1_xboole_0) | r1_tarski(k1_setfam_1(B), k1_setfam_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_setfam_1)).
% 3.18/1.52  tff(c_14, plain, (![A_8]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.52  tff(c_16, plain, (![A_9]: (k8_setfam_1(A_9, k1_xboole_0)=A_9 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.52  tff(c_40, plain, (![A_9]: (k8_setfam_1(A_9, k1_xboole_0)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_16])).
% 3.18/1.52  tff(c_805, plain, (![A_109, B_110]: (m1_subset_1(k8_setfam_1(A_109, B_110), k1_zfmisc_1(A_109)) | ~m1_subset_1(B_110, k1_zfmisc_1(k1_zfmisc_1(A_109))))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.18/1.52  tff(c_817, plain, (![A_9]: (m1_subset_1(A_9, k1_zfmisc_1(A_9)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_zfmisc_1(A_9))))), inference(superposition, [status(thm), theory('equality')], [c_40, c_805])).
% 3.18/1.52  tff(c_823, plain, (![A_111]: (m1_subset_1(A_111, k1_zfmisc_1(A_111)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_817])).
% 3.18/1.52  tff(c_24, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.18/1.52  tff(c_835, plain, (![A_111]: (r1_tarski(A_111, A_111))), inference(resolution, [status(thm)], [c_823, c_24])).
% 3.18/1.52  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.52  tff(c_684, plain, (![A_98, B_99]: (k6_setfam_1(A_98, B_99)=k1_setfam_1(B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(k1_zfmisc_1(A_98))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.18/1.52  tff(c_700, plain, (k6_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_684])).
% 3.18/1.52  tff(c_923, plain, (![A_120, B_121]: (k8_setfam_1(A_120, B_121)=k6_setfam_1(A_120, B_121) | k1_xboole_0=B_121 | ~m1_subset_1(B_121, k1_zfmisc_1(k1_zfmisc_1(A_120))))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.18/1.52  tff(c_938, plain, (k8_setfam_1('#skF_1', '#skF_3')=k6_setfam_1('#skF_1', '#skF_3') | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_36, c_923])).
% 3.18/1.52  tff(c_951, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3') | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_700, c_938])).
% 3.18/1.52  tff(c_987, plain, (k1_xboole_0='#skF_3'), inference(splitLeft, [status(thm)], [c_951])).
% 3.18/1.52  tff(c_38, plain, (m1_subset_1('#skF_2', k1_zfmisc_1(k1_zfmisc_1('#skF_1')))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.52  tff(c_701, plain, (k6_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(resolution, [status(thm)], [c_38, c_684])).
% 3.18/1.52  tff(c_941, plain, (k8_setfam_1('#skF_1', '#skF_2')=k6_setfam_1('#skF_1', '#skF_2') | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_38, c_923])).
% 3.18/1.52  tff(c_953, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_701, c_941])).
% 3.18/1.52  tff(c_1019, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2') | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_987, c_953])).
% 3.18/1.52  tff(c_1020, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_1019])).
% 3.18/1.52  tff(c_32, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.52  tff(c_1027, plain, (~r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), k8_setfam_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1020, c_32])).
% 3.18/1.52  tff(c_1035, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_835, c_1027])).
% 3.18/1.52  tff(c_1037, plain, ('#skF_2'!='#skF_3'), inference(splitRight, [status(thm)], [c_1019])).
% 3.18/1.52  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.52  tff(c_1012, plain, (![A_1]: (k4_xboole_0('#skF_3', A_1)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_987, c_987, c_2])).
% 3.18/1.52  tff(c_34, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.18/1.52  tff(c_12, plain, (![A_6, B_7]: (r1_xboole_0(A_6, B_7) | k4_xboole_0(A_6, B_7)!=A_6)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.52  tff(c_106, plain, (![A_37, C_38, B_39]: (r1_xboole_0(A_37, C_38) | ~r1_xboole_0(B_39, C_38) | ~r1_tarski(A_37, B_39))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.18/1.52  tff(c_1216, plain, (![A_135, B_136, A_137]: (r1_xboole_0(A_135, B_136) | ~r1_tarski(A_135, A_137) | k4_xboole_0(A_137, B_136)!=A_137)), inference(resolution, [status(thm)], [c_12, c_106])).
% 3.18/1.52  tff(c_1228, plain, (![B_136]: (r1_xboole_0('#skF_2', B_136) | k4_xboole_0('#skF_3', B_136)!='#skF_3')), inference(resolution, [status(thm)], [c_34, c_1216])).
% 3.18/1.52  tff(c_1238, plain, (![B_138]: (r1_xboole_0('#skF_2', B_138))), inference(demodulation, [status(thm), theory('equality')], [c_1012, c_1228])).
% 3.18/1.52  tff(c_8, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | k1_xboole_0=A_5)), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.18/1.52  tff(c_1009, plain, (![A_5]: (~r1_xboole_0(A_5, A_5) | A_5='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_987, c_8])).
% 3.18/1.52  tff(c_1242, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_1238, c_1009])).
% 3.18/1.52  tff(c_1251, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1037, c_1242])).
% 3.18/1.52  tff(c_1252, plain, (k8_setfam_1('#skF_1', '#skF_3')=k1_setfam_1('#skF_3')), inference(splitRight, [status(thm)], [c_951])).
% 3.18/1.52  tff(c_881, plain, (![A_118, B_119]: (r1_tarski(k8_setfam_1(A_118, B_119), A_118) | ~m1_subset_1(B_119, k1_zfmisc_1(k1_zfmisc_1(A_118))))), inference(resolution, [status(thm)], [c_805, c_24])).
% 3.18/1.52  tff(c_901, plain, (r1_tarski(k8_setfam_1('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_36, c_881])).
% 3.18/1.52  tff(c_1254, plain, (r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_901])).
% 3.18/1.52  tff(c_1282, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_953])).
% 3.18/1.52  tff(c_1306, plain, (![A_9]: (k8_setfam_1(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_1282, c_40])).
% 3.18/1.52  tff(c_1255, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k8_setfam_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_32])).
% 3.18/1.52  tff(c_1339, plain, (~r1_tarski(k1_setfam_1('#skF_3'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1306, c_1255])).
% 3.18/1.52  tff(c_1343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1254, c_1339])).
% 3.18/1.52  tff(c_1345, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_953])).
% 3.18/1.52  tff(c_30, plain, (![B_21, A_20]: (r1_tarski(k1_setfam_1(B_21), k1_setfam_1(A_20)) | k1_xboole_0=A_20 | ~r1_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.52  tff(c_1344, plain, (k8_setfam_1('#skF_1', '#skF_2')=k1_setfam_1('#skF_2')), inference(splitRight, [status(thm)], [c_953])).
% 3.18/1.52  tff(c_1346, plain, (~r1_tarski(k1_setfam_1('#skF_3'), k1_setfam_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1344, c_1255])).
% 3.18/1.52  tff(c_1359, plain, (k1_xboole_0='#skF_2' | ~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_30, c_1346])).
% 3.18/1.52  tff(c_1362, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1359])).
% 3.18/1.52  tff(c_1364, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1345, c_1362])).
% 3.18/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.52  
% 3.18/1.52  Inference rules
% 3.18/1.52  ----------------------
% 3.18/1.52  #Ref     : 0
% 3.18/1.52  #Sup     : 269
% 3.18/1.52  #Fact    : 0
% 3.18/1.52  #Define  : 0
% 3.18/1.52  #Split   : 10
% 3.18/1.52  #Chain   : 0
% 3.18/1.52  #Close   : 0
% 3.18/1.52  
% 3.18/1.52  Ordering : KBO
% 3.18/1.52  
% 3.18/1.52  Simplification rules
% 3.18/1.52  ----------------------
% 3.18/1.52  #Subsume      : 20
% 3.18/1.52  #Demod        : 253
% 3.18/1.52  #Tautology    : 146
% 3.18/1.52  #SimpNegUnit  : 4
% 3.18/1.52  #BackRed      : 110
% 3.18/1.52  
% 3.18/1.52  #Partial instantiations: 0
% 3.18/1.52  #Strategies tried      : 1
% 3.18/1.52  
% 3.18/1.52  Timing (in seconds)
% 3.18/1.52  ----------------------
% 3.18/1.52  Preprocessing        : 0.30
% 3.18/1.52  Parsing              : 0.17
% 3.18/1.52  CNF conversion       : 0.02
% 3.18/1.52  Main loop            : 0.44
% 3.18/1.52  Inferencing          : 0.15
% 3.18/1.52  Reduction            : 0.14
% 3.18/1.52  Demodulation         : 0.10
% 3.18/1.52  BG Simplification    : 0.02
% 3.18/1.52  Subsumption          : 0.08
% 3.18/1.52  Abstraction          : 0.02
% 3.18/1.52  MUC search           : 0.00
% 3.18/1.52  Cooper               : 0.00
% 3.18/1.52  Total                : 0.78
% 3.18/1.52  Index Insertion      : 0.00
% 3.18/1.52  Index Deletion       : 0.00
% 3.18/1.52  Index Matching       : 0.00
% 3.18/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
