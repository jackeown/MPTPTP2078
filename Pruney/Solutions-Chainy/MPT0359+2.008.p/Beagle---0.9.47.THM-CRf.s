%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:10 EST 2020

% Result     : Theorem 4.45s
% Output     : CNFRefutation 4.45s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 199 expanded)
%              Number of leaves         :   31 (  75 expanded)
%              Depth                    :   11
%              Number of atoms          :   91 ( 299 expanded)
%              Number of equality atoms :   46 ( 150 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_53,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_49,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_88,negated_conjecture,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_61,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ( r1_tarski(B,k3_subset_1(A,B))
      <=> B = k1_subset_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_subset_1)).

tff(c_137,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_190,plain,(
    ! [A_46] : k2_xboole_0(k1_xboole_0,A_46) = A_46 ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_14])).

tff(c_26,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_202,plain,(
    ! [A_46] : r1_tarski(k1_xboole_0,A_46) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_26])).

tff(c_388,plain,(
    ! [A_61,B_62] : k4_xboole_0(A_61,k4_xboole_0(A_61,B_62)) = k3_xboole_0(A_61,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_105,plain,(
    ! [A_41,B_42] : r1_tarski(k4_xboole_0(A_41,B_42),A_41) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_22,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_113,plain,(
    ! [B_42] : k4_xboole_0(k1_xboole_0,B_42) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_105,c_22])).

tff(c_431,plain,(
    ! [B_63] : k3_xboole_0(k1_xboole_0,B_63) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_113])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_436,plain,(
    ! [B_63] : k3_xboole_0(B_63,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_4])).

tff(c_20,plain,(
    ! [A_15] : k4_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_426,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k3_xboole_0(A_15,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_388])).

tff(c_567,plain,(
    ! [A_15] : k4_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_436,c_426])).

tff(c_32,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_46,plain,
    ( k2_subset_1('#skF_1') != '#skF_2'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_53,plain,
    ( '#skF_2' != '#skF_1'
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_46])).

tff(c_115,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_53])).

tff(c_52,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | k2_subset_1('#skF_1') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_54,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_52])).

tff(c_273,plain,(
    '#skF_2' = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_115,c_54])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_275,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_44])).

tff(c_898,plain,(
    ! [A_92,B_93] :
      ( k4_xboole_0(A_92,B_93) = k3_subset_1(A_92,B_93)
      | ~ m1_subset_1(B_93,k1_zfmisc_1(A_92)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_904,plain,(
    k4_xboole_0('#skF_1','#skF_1') = k3_subset_1('#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_275,c_898])).

tff(c_907,plain,(
    k3_subset_1('#skF_1','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_567,c_904])).

tff(c_274,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_273,c_115])).

tff(c_909,plain,(
    ~ r1_tarski(k1_xboole_0,'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_274])).

tff(c_912,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_909])).

tff(c_913,plain,(
    '#skF_2' != '#skF_1' ),
    inference(splitRight,[status(thm)],[c_53])).

tff(c_36,plain,(
    ! [A_27,B_28] :
      ( m1_subset_1(k3_subset_1(A_27,B_28),k1_zfmisc_1(A_27))
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_936,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_913,c_54])).

tff(c_1719,plain,(
    ! [A_142,B_143] :
      ( k3_subset_1(A_142,k3_subset_1(A_142,B_143)) = B_143
      | ~ m1_subset_1(B_143,k1_zfmisc_1(A_142)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1725,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_1719])).

tff(c_30,plain,(
    ! [A_23] : k1_subset_1(A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_42,plain,(
    ! [A_31,B_32] :
      ( k1_subset_1(A_31) = B_32
      | ~ r1_tarski(B_32,k3_subset_1(A_31,B_32))
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1948,plain,(
    ! [B_155,A_156] :
      ( k1_xboole_0 = B_155
      | ~ r1_tarski(B_155,k3_subset_1(A_156,B_155))
      | ~ m1_subset_1(B_155,k1_zfmisc_1(A_156)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_42])).

tff(c_1951,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_2')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1725,c_1948])).

tff(c_1973,plain,
    ( k3_subset_1('#skF_1','#skF_2') = k1_xboole_0
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_936,c_1951])).

tff(c_3788,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1973])).

tff(c_3791,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_36,c_3788])).

tff(c_3795,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3791])).

tff(c_3796,plain,(
    k3_subset_1('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_1973])).

tff(c_3801,plain,(
    k3_subset_1('#skF_1',k1_xboole_0) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3796,c_1725])).

tff(c_3818,plain,
    ( m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3796,c_36])).

tff(c_3824,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_3818])).

tff(c_34,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k3_subset_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4098,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k3_subset_1('#skF_1',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_3824,c_34])).

tff(c_4102,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3801,c_20,c_4098])).

tff(c_4104,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_913,c_4102])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:18:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.45/1.85  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.85  
% 4.45/1.85  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.86  %$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.45/1.86  
% 4.45/1.86  %Foreground sorts:
% 4.45/1.86  
% 4.45/1.86  
% 4.45/1.86  %Background operators:
% 4.45/1.86  
% 4.45/1.86  
% 4.45/1.86  %Foreground operators:
% 4.45/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.45/1.86  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.45/1.86  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.45/1.86  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.45/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.45/1.86  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.45/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.45/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.45/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.45/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.45/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.45/1.86  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 4.45/1.86  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.45/1.86  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.45/1.86  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.45/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.45/1.86  
% 4.45/1.87  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.45/1.87  tff(f_41, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 4.45/1.87  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.45/1.87  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.45/1.87  tff(f_43, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 4.45/1.87  tff(f_53, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_1)).
% 4.45/1.87  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.45/1.87  tff(f_49, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 4.45/1.87  tff(f_63, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.45/1.87  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), B) <=> (B = k2_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_subset_1)).
% 4.45/1.87  tff(f_67, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.45/1.87  tff(f_71, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.45/1.87  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.45/1.87  tff(f_61, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 4.45/1.87  tff(f_81, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, B)) <=> (B = k1_subset_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_subset_1)).
% 4.45/1.87  tff(c_137, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.45/1.87  tff(c_14, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.45/1.87  tff(c_190, plain, (![A_46]: (k2_xboole_0(k1_xboole_0, A_46)=A_46)), inference(superposition, [status(thm), theory('equality')], [c_137, c_14])).
% 4.45/1.87  tff(c_26, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.45/1.87  tff(c_202, plain, (![A_46]: (r1_tarski(k1_xboole_0, A_46))), inference(superposition, [status(thm), theory('equality')], [c_190, c_26])).
% 4.45/1.87  tff(c_388, plain, (![A_61, B_62]: (k4_xboole_0(A_61, k4_xboole_0(A_61, B_62))=k3_xboole_0(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.45/1.87  tff(c_105, plain, (![A_41, B_42]: (r1_tarski(k4_xboole_0(A_41, B_42), A_41))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.45/1.87  tff(c_22, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.45/1.87  tff(c_113, plain, (![B_42]: (k4_xboole_0(k1_xboole_0, B_42)=k1_xboole_0)), inference(resolution, [status(thm)], [c_105, c_22])).
% 4.45/1.87  tff(c_431, plain, (![B_63]: (k3_xboole_0(k1_xboole_0, B_63)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_388, c_113])).
% 4.45/1.87  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.45/1.87  tff(c_436, plain, (![B_63]: (k3_xboole_0(B_63, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_431, c_4])).
% 4.45/1.87  tff(c_20, plain, (![A_15]: (k4_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.45/1.87  tff(c_426, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k3_xboole_0(A_15, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_20, c_388])).
% 4.45/1.87  tff(c_567, plain, (![A_15]: (k4_xboole_0(A_15, A_15)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_436, c_426])).
% 4.45/1.87  tff(c_32, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.45/1.87  tff(c_46, plain, (k2_subset_1('#skF_1')!='#skF_2' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.87  tff(c_53, plain, ('#skF_2'!='#skF_1' | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_46])).
% 4.45/1.87  tff(c_115, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(splitLeft, [status(thm)], [c_53])).
% 4.45/1.87  tff(c_52, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | k2_subset_1('#skF_1')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.87  tff(c_54, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | '#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_52])).
% 4.45/1.87  tff(c_273, plain, ('#skF_2'='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_115, c_54])).
% 4.45/1.87  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.45/1.87  tff(c_275, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_273, c_44])).
% 4.45/1.87  tff(c_898, plain, (![A_92, B_93]: (k4_xboole_0(A_92, B_93)=k3_subset_1(A_92, B_93) | ~m1_subset_1(B_93, k1_zfmisc_1(A_92)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.45/1.87  tff(c_904, plain, (k4_xboole_0('#skF_1', '#skF_1')=k3_subset_1('#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_275, c_898])).
% 4.45/1.87  tff(c_907, plain, (k3_subset_1('#skF_1', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_567, c_904])).
% 4.45/1.87  tff(c_274, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_273, c_115])).
% 4.45/1.87  tff(c_909, plain, (~r1_tarski(k1_xboole_0, '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_907, c_274])).
% 4.45/1.87  tff(c_912, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_909])).
% 4.45/1.87  tff(c_913, plain, ('#skF_2'!='#skF_1'), inference(splitRight, [status(thm)], [c_53])).
% 4.45/1.87  tff(c_36, plain, (![A_27, B_28]: (m1_subset_1(k3_subset_1(A_27, B_28), k1_zfmisc_1(A_27)) | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.45/1.87  tff(c_936, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_913, c_54])).
% 4.45/1.87  tff(c_1719, plain, (![A_142, B_143]: (k3_subset_1(A_142, k3_subset_1(A_142, B_143))=B_143 | ~m1_subset_1(B_143, k1_zfmisc_1(A_142)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.45/1.87  tff(c_1725, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_44, c_1719])).
% 4.45/1.87  tff(c_30, plain, (![A_23]: (k1_subset_1(A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.45/1.87  tff(c_42, plain, (![A_31, B_32]: (k1_subset_1(A_31)=B_32 | ~r1_tarski(B_32, k3_subset_1(A_31, B_32)) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.45/1.87  tff(c_1948, plain, (![B_155, A_156]: (k1_xboole_0=B_155 | ~r1_tarski(B_155, k3_subset_1(A_156, B_155)) | ~m1_subset_1(B_155, k1_zfmisc_1(A_156)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_42])).
% 4.45/1.87  tff(c_1951, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_2') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1725, c_1948])).
% 4.45/1.87  tff(c_1973, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0 | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_936, c_1951])).
% 4.45/1.87  tff(c_3788, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1973])).
% 4.45/1.87  tff(c_3791, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_36, c_3788])).
% 4.45/1.87  tff(c_3795, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_3791])).
% 4.45/1.87  tff(c_3796, plain, (k3_subset_1('#skF_1', '#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_1973])).
% 4.45/1.87  tff(c_3801, plain, (k3_subset_1('#skF_1', k1_xboole_0)='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_3796, c_1725])).
% 4.45/1.87  tff(c_3818, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_3796, c_36])).
% 4.45/1.87  tff(c_3824, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_3818])).
% 4.45/1.87  tff(c_34, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k3_subset_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.45/1.87  tff(c_4098, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k3_subset_1('#skF_1', k1_xboole_0)), inference(resolution, [status(thm)], [c_3824, c_34])).
% 4.45/1.87  tff(c_4102, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3801, c_20, c_4098])).
% 4.45/1.87  tff(c_4104, plain, $false, inference(negUnitSimplification, [status(thm)], [c_913, c_4102])).
% 4.45/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.45/1.87  
% 4.45/1.87  Inference rules
% 4.45/1.87  ----------------------
% 4.45/1.87  #Ref     : 0
% 4.45/1.87  #Sup     : 970
% 4.45/1.87  #Fact    : 0
% 4.45/1.87  #Define  : 0
% 4.45/1.87  #Split   : 5
% 4.45/1.87  #Chain   : 0
% 4.45/1.87  #Close   : 0
% 4.45/1.87  
% 4.45/1.87  Ordering : KBO
% 4.45/1.87  
% 4.45/1.87  Simplification rules
% 4.45/1.87  ----------------------
% 4.45/1.87  #Subsume      : 200
% 4.45/1.87  #Demod        : 508
% 4.45/1.87  #Tautology    : 509
% 4.45/1.87  #SimpNegUnit  : 8
% 4.45/1.87  #BackRed      : 13
% 4.45/1.87  
% 4.45/1.87  #Partial instantiations: 0
% 4.45/1.87  #Strategies tried      : 1
% 4.45/1.87  
% 4.45/1.87  Timing (in seconds)
% 4.45/1.87  ----------------------
% 4.45/1.87  Preprocessing        : 0.34
% 4.45/1.87  Parsing              : 0.18
% 4.45/1.87  CNF conversion       : 0.02
% 4.45/1.87  Main loop            : 0.75
% 4.45/1.87  Inferencing          : 0.23
% 4.45/1.87  Reduction            : 0.30
% 4.45/1.88  Demodulation         : 0.24
% 4.45/1.88  BG Simplification    : 0.03
% 4.45/1.88  Subsumption          : 0.14
% 4.45/1.88  Abstraction          : 0.04
% 4.45/1.88  MUC search           : 0.00
% 4.45/1.88  Cooper               : 0.00
% 4.45/1.88  Total                : 1.12
% 4.45/1.88  Index Insertion      : 0.00
% 4.45/1.88  Index Deletion       : 0.00
% 4.45/1.88  Index Matching       : 0.00
% 4.45/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
