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
% DateTime   : Thu Dec  3 09:56:51 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.23s
% Verified   : 
% Statistics : Number of formulae       :   80 (  96 expanded)
%              Number of leaves         :   35 (  45 expanded)
%              Depth                    :   15
%              Number of atoms          :  105 ( 162 expanded)
%              Number of equality atoms :   28 (  37 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( A != k1_xboole_0
       => ! [B] :
            ( m1_subset_1(B,k1_zfmisc_1(A))
           => ! [C] :
                ( m1_subset_1(C,A)
               => ( ~ r2_hidden(C,B)
                 => r2_hidden(C,k3_subset_1(A,B)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_69,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_75,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_86,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_73,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_84,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_xboole_0(B,k3_subset_1(A,C))
          <=> r1_tarski(B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_40,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_54,plain,(
    m1_subset_1('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_126,plain,(
    ! [B_44,A_45] :
      ( v1_xboole_0(B_44)
      | ~ m1_subset_1(B_44,A_45)
      | ~ v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_146,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_54,c_126])).

tff(c_147,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_146])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r2_hidden(B_13,A_12)
      | ~ m1_subset_1(B_13,A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_52,plain,(
    ~ r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_56,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_38,plain,(
    ! [A_18] : m1_subset_1(k2_subset_1(A_18),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_60,plain,(
    ! [A_18] : m1_subset_1(A_18,k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_38])).

tff(c_22,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_32,plain,(
    ! [A_14] : k1_subset_1(A_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = k2_subset_1(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_59,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_subset_1(A_21)) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_42])).

tff(c_61,plain,(
    ! [A_21] : k3_subset_1(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_59])).

tff(c_48,plain,(
    ! [A_26] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_26)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_220,plain,(
    ! [A_56,B_57] :
      ( k3_subset_1(A_56,k3_subset_1(A_56,B_57)) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_229,plain,(
    ! [A_26] : k3_subset_1(A_26,k3_subset_1(A_26,k1_xboole_0)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_48,c_220])).

tff(c_234,plain,(
    ! [A_26] : k3_subset_1(A_26,A_26) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_61,c_229])).

tff(c_614,plain,(
    ! [B_105,C_106,A_107] :
      ( r1_tarski(B_105,C_106)
      | ~ r1_xboole_0(B_105,k3_subset_1(A_107,C_106))
      | ~ m1_subset_1(C_106,k1_zfmisc_1(A_107))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_627,plain,(
    ! [B_105,A_26] :
      ( r1_tarski(B_105,A_26)
      | ~ r1_xboole_0(B_105,k1_xboole_0)
      | ~ m1_subset_1(A_26,k1_zfmisc_1(A_26))
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_26)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_614])).

tff(c_649,plain,(
    ! [B_109,A_110] :
      ( r1_tarski(B_109,A_110)
      | ~ m1_subset_1(B_109,k1_zfmisc_1(A_110)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_22,c_627])).

tff(c_664,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_56,c_649])).

tff(c_20,plain,(
    ! [A_9,B_10] :
      ( k3_xboole_0(A_9,B_10) = A_9
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_670,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_664,c_20])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_691,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_670,c_2])).

tff(c_257,plain,(
    ! [A_59,B_60] :
      ( k4_xboole_0(A_59,B_60) = k3_subset_1(A_59,B_60)
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_272,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_56,c_257])).

tff(c_18,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_351,plain,(
    ! [A_72,C_73,B_74] :
      ( r2_hidden(A_72,C_73)
      | ~ r2_hidden(A_72,B_74)
      | r2_hidden(A_72,k5_xboole_0(B_74,C_73)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1029,plain,(
    ! [A_125,A_126,B_127] :
      ( r2_hidden(A_125,k3_xboole_0(A_126,B_127))
      | ~ r2_hidden(A_125,A_126)
      | r2_hidden(A_125,k4_xboole_0(A_126,B_127)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_351])).

tff(c_1047,plain,(
    ! [A_125] :
      ( r2_hidden(A_125,k3_xboole_0('#skF_1','#skF_2'))
      | ~ r2_hidden(A_125,'#skF_1')
      | r2_hidden(A_125,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_272,c_1029])).

tff(c_1268,plain,(
    ! [A_149] :
      ( r2_hidden(A_149,'#skF_2')
      | ~ r2_hidden(A_149,'#skF_1')
      | r2_hidden(A_149,k3_subset_1('#skF_1','#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_691,c_1047])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_1282,plain,
    ( r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_1268,c_50])).

tff(c_1293,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_1282])).

tff(c_1296,plain,
    ( ~ m1_subset_1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_26,c_1293])).

tff(c_1299,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1296])).

tff(c_1301,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_1299])).

tff(c_1303,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_146])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1310,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_1303,c_4])).

tff(c_1314,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_1310])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:18:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.57  
% 3.23/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.58  %$ r2_hidden > r1_xboole_0 > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.23/1.58  
% 3.23/1.58  %Foreground sorts:
% 3.23/1.58  
% 3.23/1.58  
% 3.23/1.58  %Background operators:
% 3.23/1.58  
% 3.23/1.58  
% 3.23/1.58  %Foreground operators:
% 3.23/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.58  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.23/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.58  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.23/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.58  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.23/1.58  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.23/1.58  tff('#skF_2', type, '#skF_2': $i).
% 3.23/1.58  tff('#skF_3', type, '#skF_3': $i).
% 3.23/1.58  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.58  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.58  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.23/1.58  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.23/1.58  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.23/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.23/1.58  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.58  
% 3.23/1.59  tff(f_101, negated_conjecture, ~(![A]: (~(A = k1_xboole_0) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, A) => (~r2_hidden(C, B) => r2_hidden(C, k3_subset_1(A, B))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_subset_1)).
% 3.23/1.59  tff(f_59, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 3.23/1.59  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.23/1.59  tff(f_69, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 3.23/1.59  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.23/1.59  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.23/1.59  tff(f_75, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.23/1.59  tff(f_86, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.23/1.59  tff(f_73, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.23/1.59  tff(f_84, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, k3_subset_1(A, C)) <=> r1_tarski(B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_subset_1)).
% 3.23/1.59  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.23/1.59  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.23/1.59  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.23/1.59  tff(f_40, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.23/1.59  tff(f_38, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_0)).
% 3.23/1.59  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.23/1.59  tff(c_58, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.59  tff(c_54, plain, (m1_subset_1('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.59  tff(c_126, plain, (![B_44, A_45]: (v1_xboole_0(B_44) | ~m1_subset_1(B_44, A_45) | ~v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.59  tff(c_146, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_54, c_126])).
% 3.23/1.59  tff(c_147, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_146])).
% 3.23/1.59  tff(c_26, plain, (![B_13, A_12]: (r2_hidden(B_13, A_12) | ~m1_subset_1(B_13, A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.23/1.59  tff(c_52, plain, (~r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.59  tff(c_56, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.59  tff(c_34, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.23/1.59  tff(c_38, plain, (![A_18]: (m1_subset_1(k2_subset_1(A_18), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 3.23/1.59  tff(c_60, plain, (![A_18]: (m1_subset_1(A_18, k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_38])).
% 3.23/1.59  tff(c_22, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.23/1.59  tff(c_32, plain, (![A_14]: (k1_subset_1(A_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.23/1.59  tff(c_42, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=k2_subset_1(A_21))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.23/1.59  tff(c_59, plain, (![A_21]: (k3_subset_1(A_21, k1_subset_1(A_21))=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_42])).
% 3.23/1.59  tff(c_61, plain, (![A_21]: (k3_subset_1(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_32, c_59])).
% 3.23/1.59  tff(c_48, plain, (![A_26]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_26)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.23/1.59  tff(c_220, plain, (![A_56, B_57]: (k3_subset_1(A_56, k3_subset_1(A_56, B_57))=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.23/1.59  tff(c_229, plain, (![A_26]: (k3_subset_1(A_26, k3_subset_1(A_26, k1_xboole_0))=k1_xboole_0)), inference(resolution, [status(thm)], [c_48, c_220])).
% 3.23/1.59  tff(c_234, plain, (![A_26]: (k3_subset_1(A_26, A_26)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_61, c_229])).
% 3.23/1.59  tff(c_614, plain, (![B_105, C_106, A_107]: (r1_tarski(B_105, C_106) | ~r1_xboole_0(B_105, k3_subset_1(A_107, C_106)) | ~m1_subset_1(C_106, k1_zfmisc_1(A_107)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_107)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.23/1.59  tff(c_627, plain, (![B_105, A_26]: (r1_tarski(B_105, A_26) | ~r1_xboole_0(B_105, k1_xboole_0) | ~m1_subset_1(A_26, k1_zfmisc_1(A_26)) | ~m1_subset_1(B_105, k1_zfmisc_1(A_26)))), inference(superposition, [status(thm), theory('equality')], [c_234, c_614])).
% 3.23/1.59  tff(c_649, plain, (![B_109, A_110]: (r1_tarski(B_109, A_110) | ~m1_subset_1(B_109, k1_zfmisc_1(A_110)))), inference(demodulation, [status(thm), theory('equality')], [c_60, c_22, c_627])).
% 3.23/1.59  tff(c_664, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_56, c_649])).
% 3.23/1.59  tff(c_20, plain, (![A_9, B_10]: (k3_xboole_0(A_9, B_10)=A_9 | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.23/1.59  tff(c_670, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_664, c_20])).
% 3.23/1.59  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.23/1.59  tff(c_691, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_670, c_2])).
% 3.23/1.59  tff(c_257, plain, (![A_59, B_60]: (k4_xboole_0(A_59, B_60)=k3_subset_1(A_59, B_60) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.23/1.59  tff(c_272, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_56, c_257])).
% 3.23/1.59  tff(c_18, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.23/1.59  tff(c_351, plain, (![A_72, C_73, B_74]: (r2_hidden(A_72, C_73) | ~r2_hidden(A_72, B_74) | r2_hidden(A_72, k5_xboole_0(B_74, C_73)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.23/1.59  tff(c_1029, plain, (![A_125, A_126, B_127]: (r2_hidden(A_125, k3_xboole_0(A_126, B_127)) | ~r2_hidden(A_125, A_126) | r2_hidden(A_125, k4_xboole_0(A_126, B_127)))), inference(superposition, [status(thm), theory('equality')], [c_18, c_351])).
% 3.23/1.59  tff(c_1047, plain, (![A_125]: (r2_hidden(A_125, k3_xboole_0('#skF_1', '#skF_2')) | ~r2_hidden(A_125, '#skF_1') | r2_hidden(A_125, k3_subset_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_272, c_1029])).
% 3.23/1.59  tff(c_1268, plain, (![A_149]: (r2_hidden(A_149, '#skF_2') | ~r2_hidden(A_149, '#skF_1') | r2_hidden(A_149, k3_subset_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_691, c_1047])).
% 3.23/1.59  tff(c_50, plain, (~r2_hidden('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.23/1.59  tff(c_1282, plain, (r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_1268, c_50])).
% 3.23/1.59  tff(c_1293, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_52, c_1282])).
% 3.23/1.59  tff(c_1296, plain, (~m1_subset_1('#skF_3', '#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_26, c_1293])).
% 3.23/1.59  tff(c_1299, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1296])).
% 3.23/1.59  tff(c_1301, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_1299])).
% 3.23/1.59  tff(c_1303, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_146])).
% 3.23/1.59  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.23/1.59  tff(c_1310, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_1303, c_4])).
% 3.23/1.59  tff(c_1314, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_1310])).
% 3.23/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.23/1.59  
% 3.23/1.59  Inference rules
% 3.23/1.59  ----------------------
% 3.23/1.59  #Ref     : 0
% 3.23/1.59  #Sup     : 291
% 3.23/1.59  #Fact    : 0
% 3.23/1.59  #Define  : 0
% 3.23/1.59  #Split   : 11
% 3.23/1.59  #Chain   : 0
% 3.23/1.59  #Close   : 0
% 3.23/1.59  
% 3.23/1.59  Ordering : KBO
% 3.23/1.59  
% 3.23/1.59  Simplification rules
% 3.23/1.59  ----------------------
% 3.23/1.59  #Subsume      : 34
% 3.23/1.59  #Demod        : 104
% 3.23/1.59  #Tautology    : 151
% 3.23/1.59  #SimpNegUnit  : 13
% 3.23/1.59  #BackRed      : 7
% 3.23/1.59  
% 3.23/1.59  #Partial instantiations: 0
% 3.23/1.59  #Strategies tried      : 1
% 3.23/1.59  
% 3.23/1.59  Timing (in seconds)
% 3.23/1.59  ----------------------
% 3.23/1.59  Preprocessing        : 0.34
% 3.23/1.59  Parsing              : 0.19
% 3.23/1.59  CNF conversion       : 0.02
% 3.23/1.59  Main loop            : 0.46
% 3.23/1.60  Inferencing          : 0.17
% 3.23/1.60  Reduction            : 0.14
% 3.23/1.60  Demodulation         : 0.10
% 3.23/1.60  BG Simplification    : 0.02
% 3.23/1.60  Subsumption          : 0.09
% 3.23/1.60  Abstraction          : 0.02
% 3.23/1.60  MUC search           : 0.00
% 3.23/1.60  Cooper               : 0.00
% 3.23/1.60  Total                : 0.84
% 3.23/1.60  Index Insertion      : 0.00
% 3.23/1.60  Index Deletion       : 0.00
% 3.23/1.60  Index Matching       : 0.00
% 3.23/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------
