%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:59 EST 2020

% Result     : Theorem 4.89s
% Output     : CNFRefutation 5.22s
% Verified   : 
% Statistics : Number of formulae       :   72 ( 130 expanded)
%              Number of leaves         :   30 (  56 expanded)
%              Depth                    :   11
%              Number of atoms          :   85 ( 183 expanded)
%              Number of equality atoms :   28 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_49,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_35,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_62,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_30,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_395,plain,(
    ! [A_58,B_59] :
      ( k4_xboole_0(A_58,B_59) = k3_subset_1(A_58,B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_425,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_395])).

tff(c_22,plain,(
    ! [A_18,B_19] : k6_subset_1(A_18,B_19) = k4_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_16,B_17] : m1_subset_1(k6_subset_1(A_16,B_17),k1_zfmisc_1(A_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_37,plain,(
    ! [A_16,B_17] : m1_subset_1(k4_xboole_0(A_16,B_17),k1_zfmisc_1(A_16)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_20])).

tff(c_632,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_37])).

tff(c_32,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_25] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_14,plain,(
    ! [A_12] : k1_subset_1(A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_13] : k2_subset_1(A_13) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_24,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_subset_1(A_20)) = k2_subset_1(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_38,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_subset_1(A_20)) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_24])).

tff(c_39,plain,(
    ! [A_20] : k3_subset_1(A_20,k1_xboole_0) = A_20 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_38])).

tff(c_8,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_591,plain,(
    ! [C_67,A_68,B_69] :
      ( r1_tarski(C_67,k3_subset_1(A_68,B_69))
      | ~ r1_tarski(B_69,k3_subset_1(A_68,C_67))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_610,plain,(
    ! [C_67,A_68] :
      ( r1_tarski(C_67,k3_subset_1(A_68,k1_xboole_0))
      | ~ m1_subset_1(C_67,k1_zfmisc_1(A_68))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_8,c_591])).

tff(c_674,plain,(
    ! [C_71,A_72] :
      ( r1_tarski(C_71,A_72)
      | ~ m1_subset_1(C_71,k1_zfmisc_1(A_72)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_39,c_610])).

tff(c_722,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_36,c_674])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_730,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_722,c_6])).

tff(c_795,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_730])).

tff(c_12,plain,(
    ! [A_10,B_11] : k4_xboole_0(A_10,k4_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_407,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_subset_1(A_16,k4_xboole_0(A_16,B_17)) ),
    inference(resolution,[status(thm)],[c_37,c_395])).

tff(c_1360,plain,(
    ! [A_83,B_84] : k3_subset_1(A_83,k4_xboole_0(A_83,B_84)) = k3_xboole_0(A_83,B_84) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_407])).

tff(c_1395,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_425,c_1360])).

tff(c_1423,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_795,c_1395])).

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_719,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_674])).

tff(c_726,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_719,c_6])).

tff(c_756,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_726])).

tff(c_422,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_395])).

tff(c_26,plain,(
    ! [C_24,A_21,B_22] :
      ( r1_tarski(C_24,k3_subset_1(A_21,B_22))
      | ~ r1_tarski(B_22,k3_subset_1(A_21,C_24))
      | ~ m1_subset_1(C_24,k1_zfmisc_1(A_21))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_21)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_1365,plain,(
    ! [A_83,B_84,B_22] :
      ( r1_tarski(k4_xboole_0(A_83,B_84),k3_subset_1(A_83,B_22))
      | ~ r1_tarski(B_22,k3_xboole_0(A_83,B_84))
      | ~ m1_subset_1(k4_xboole_0(A_83,B_84),k1_zfmisc_1(A_83))
      | ~ m1_subset_1(B_22,k1_zfmisc_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1360,c_26])).

tff(c_5046,plain,(
    ! [A_126,B_127,B_128] :
      ( r1_tarski(k4_xboole_0(A_126,B_127),k3_subset_1(A_126,B_128))
      | ~ r1_tarski(B_128,k3_xboole_0(A_126,B_127))
      | ~ m1_subset_1(B_128,k1_zfmisc_1(A_126)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_37,c_1365])).

tff(c_5120,plain,(
    ! [B_128] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1',B_128))
      | ~ r1_tarski(B_128,k3_xboole_0('#skF_1','#skF_3'))
      | ~ m1_subset_1(B_128,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_422,c_5046])).

tff(c_5738,plain,(
    ! [B_136] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1',B_136))
      | ~ r1_tarski(B_136,'#skF_3')
      | ~ m1_subset_1(B_136,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_756,c_5120])).

tff(c_5757,plain,
    ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2')
    | ~ r1_tarski(k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1423,c_5738])).

tff(c_5781,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_32,c_5757])).

tff(c_5783,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_5781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:57:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.89/1.94  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.94  
% 5.22/1.94  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.95  %$ r1_tarski > m1_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 5.22/1.95  
% 5.22/1.95  %Foreground sorts:
% 5.22/1.95  
% 5.22/1.95  
% 5.22/1.95  %Background operators:
% 5.22/1.95  
% 5.22/1.95  
% 5.22/1.95  %Foreground operators:
% 5.22/1.95  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.22/1.95  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.22/1.95  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.22/1.95  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.22/1.95  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.22/1.95  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.22/1.95  tff('#skF_2', type, '#skF_2': $i).
% 5.22/1.95  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 5.22/1.95  tff('#skF_3', type, '#skF_3': $i).
% 5.22/1.95  tff('#skF_1', type, '#skF_1': $i).
% 5.22/1.95  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.22/1.95  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.22/1.95  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.22/1.95  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.22/1.95  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.22/1.95  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.22/1.95  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.22/1.95  
% 5.22/1.96  tff(f_74, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 5.22/1.96  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.22/1.96  tff(f_51, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 5.22/1.96  tff(f_49, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 5.22/1.96  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.22/1.96  tff(f_64, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 5.22/1.96  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 5.22/1.96  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.22/1.96  tff(f_53, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 5.22/1.96  tff(f_35, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 5.22/1.96  tff(f_62, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 5.22/1.96  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.22/1.96  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 5.22/1.96  tff(c_30, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.22/1.96  tff(c_36, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.22/1.96  tff(c_395, plain, (![A_58, B_59]: (k4_xboole_0(A_58, B_59)=k3_subset_1(A_58, B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_58)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.22/1.96  tff(c_425, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_395])).
% 5.22/1.96  tff(c_22, plain, (![A_18, B_19]: (k6_subset_1(A_18, B_19)=k4_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.22/1.96  tff(c_20, plain, (![A_16, B_17]: (m1_subset_1(k6_subset_1(A_16, B_17), k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.22/1.96  tff(c_37, plain, (![A_16, B_17]: (m1_subset_1(k4_xboole_0(A_16, B_17), k1_zfmisc_1(A_16)))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_20])).
% 5.22/1.96  tff(c_632, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_425, c_37])).
% 5.22/1.96  tff(c_32, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.22/1.96  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.22/1.96  tff(c_28, plain, (![A_25]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 5.22/1.96  tff(c_14, plain, (![A_12]: (k1_subset_1(A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.22/1.96  tff(c_16, plain, (![A_13]: (k2_subset_1(A_13)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.22/1.96  tff(c_24, plain, (![A_20]: (k3_subset_1(A_20, k1_subset_1(A_20))=k2_subset_1(A_20))), inference(cnfTransformation, [status(thm)], [f_53])).
% 5.22/1.96  tff(c_38, plain, (![A_20]: (k3_subset_1(A_20, k1_subset_1(A_20))=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_24])).
% 5.22/1.96  tff(c_39, plain, (![A_20]: (k3_subset_1(A_20, k1_xboole_0)=A_20)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_38])).
% 5.22/1.96  tff(c_8, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.22/1.96  tff(c_591, plain, (![C_67, A_68, B_69]: (r1_tarski(C_67, k3_subset_1(A_68, B_69)) | ~r1_tarski(B_69, k3_subset_1(A_68, C_67)) | ~m1_subset_1(C_67, k1_zfmisc_1(A_68)) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.22/1.96  tff(c_610, plain, (![C_67, A_68]: (r1_tarski(C_67, k3_subset_1(A_68, k1_xboole_0)) | ~m1_subset_1(C_67, k1_zfmisc_1(A_68)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_8, c_591])).
% 5.22/1.96  tff(c_674, plain, (![C_71, A_72]: (r1_tarski(C_71, A_72) | ~m1_subset_1(C_71, k1_zfmisc_1(A_72)))), inference(demodulation, [status(thm), theory('equality')], [c_28, c_39, c_610])).
% 5.22/1.96  tff(c_722, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_36, c_674])).
% 5.22/1.96  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.22/1.96  tff(c_730, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_722, c_6])).
% 5.22/1.96  tff(c_795, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_2, c_730])).
% 5.22/1.96  tff(c_12, plain, (![A_10, B_11]: (k4_xboole_0(A_10, k4_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.22/1.96  tff(c_407, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_subset_1(A_16, k4_xboole_0(A_16, B_17)))), inference(resolution, [status(thm)], [c_37, c_395])).
% 5.22/1.96  tff(c_1360, plain, (![A_83, B_84]: (k3_subset_1(A_83, k4_xboole_0(A_83, B_84))=k3_xboole_0(A_83, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_407])).
% 5.22/1.96  tff(c_1395, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_425, c_1360])).
% 5.22/1.96  tff(c_1423, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_795, c_1395])).
% 5.22/1.96  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.22/1.96  tff(c_719, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_674])).
% 5.22/1.96  tff(c_726, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_719, c_6])).
% 5.22/1.96  tff(c_756, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_726])).
% 5.22/1.96  tff(c_422, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_34, c_395])).
% 5.22/1.96  tff(c_26, plain, (![C_24, A_21, B_22]: (r1_tarski(C_24, k3_subset_1(A_21, B_22)) | ~r1_tarski(B_22, k3_subset_1(A_21, C_24)) | ~m1_subset_1(C_24, k1_zfmisc_1(A_21)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_21)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 5.22/1.96  tff(c_1365, plain, (![A_83, B_84, B_22]: (r1_tarski(k4_xboole_0(A_83, B_84), k3_subset_1(A_83, B_22)) | ~r1_tarski(B_22, k3_xboole_0(A_83, B_84)) | ~m1_subset_1(k4_xboole_0(A_83, B_84), k1_zfmisc_1(A_83)) | ~m1_subset_1(B_22, k1_zfmisc_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_1360, c_26])).
% 5.22/1.96  tff(c_5046, plain, (![A_126, B_127, B_128]: (r1_tarski(k4_xboole_0(A_126, B_127), k3_subset_1(A_126, B_128)) | ~r1_tarski(B_128, k3_xboole_0(A_126, B_127)) | ~m1_subset_1(B_128, k1_zfmisc_1(A_126)))), inference(demodulation, [status(thm), theory('equality')], [c_37, c_1365])).
% 5.22/1.96  tff(c_5120, plain, (![B_128]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', B_128)) | ~r1_tarski(B_128, k3_xboole_0('#skF_1', '#skF_3')) | ~m1_subset_1(B_128, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_422, c_5046])).
% 5.22/1.96  tff(c_5738, plain, (![B_136]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', B_136)) | ~r1_tarski(B_136, '#skF_3') | ~m1_subset_1(B_136, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_756, c_5120])).
% 5.22/1.96  tff(c_5757, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2') | ~r1_tarski(k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1423, c_5738])).
% 5.22/1.96  tff(c_5781, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_632, c_32, c_5757])).
% 5.22/1.96  tff(c_5783, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_5781])).
% 5.22/1.96  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.22/1.96  
% 5.22/1.96  Inference rules
% 5.22/1.96  ----------------------
% 5.22/1.96  #Ref     : 0
% 5.22/1.96  #Sup     : 1415
% 5.22/1.96  #Fact    : 0
% 5.22/1.96  #Define  : 0
% 5.22/1.96  #Split   : 0
% 5.22/1.96  #Chain   : 0
% 5.22/1.96  #Close   : 0
% 5.22/1.96  
% 5.22/1.96  Ordering : KBO
% 5.22/1.96  
% 5.22/1.96  Simplification rules
% 5.22/1.96  ----------------------
% 5.22/1.96  #Subsume      : 28
% 5.22/1.96  #Demod        : 2117
% 5.22/1.96  #Tautology    : 1198
% 5.22/1.96  #SimpNegUnit  : 1
% 5.22/1.96  #BackRed      : 3
% 5.22/1.96  
% 5.22/1.96  #Partial instantiations: 0
% 5.22/1.96  #Strategies tried      : 1
% 5.22/1.96  
% 5.22/1.96  Timing (in seconds)
% 5.22/1.96  ----------------------
% 5.22/1.96  Preprocessing        : 0.29
% 5.22/1.96  Parsing              : 0.16
% 5.22/1.96  CNF conversion       : 0.02
% 5.22/1.96  Main loop            : 0.92
% 5.22/1.96  Inferencing          : 0.24
% 5.22/1.96  Reduction            : 0.48
% 5.22/1.96  Demodulation         : 0.41
% 5.22/1.96  BG Simplification    : 0.03
% 5.22/1.96  Subsumption          : 0.12
% 5.22/1.96  Abstraction          : 0.04
% 5.22/1.96  MUC search           : 0.00
% 5.22/1.96  Cooper               : 0.00
% 5.22/1.96  Total                : 1.24
% 5.22/1.96  Index Insertion      : 0.00
% 5.22/1.96  Index Deletion       : 0.00
% 5.22/1.96  Index Matching       : 0.00
% 5.22/1.96  BG Taut test         : 0.00
%------------------------------------------------------------------------------
