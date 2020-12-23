%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:56:19 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.24s
% Verified   : 
% Statistics : Number of formulae       :   74 ( 104 expanded)
%              Number of leaves         :   33 (  47 expanded)
%              Depth                    :   12
%              Number of atoms          :   87 ( 146 expanded)
%              Number of equality atoms :   40 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_83,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(A))
       => ( ( r1_tarski(B,C)
            & r1_tarski(B,k3_subset_1(A,C)) )
         => B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_subset_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_55,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_57,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_63,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,k3_subset_1(A,C))
           => r1_tarski(C,k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_449,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_458,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_449])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    ! [A_28] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_28)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_24,plain,(
    ! [A_19] : k1_subset_1(A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_26,plain,(
    ! [A_20] : k2_subset_1(A_20) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_30,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_subset_1(A_23)) = k2_subset_1(A_23) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_43,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_subset_1(A_23)) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_30])).

tff(c_44,plain,(
    ! [A_23] : k3_subset_1(A_23,k1_xboole_0) = A_23 ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_43])).

tff(c_16,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_550,plain,(
    ! [C_65,A_66,B_67] :
      ( r1_tarski(C_65,k3_subset_1(A_66,B_67))
      | ~ r1_tarski(B_67,k3_subset_1(A_66,C_65))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_560,plain,(
    ! [C_65,A_66] :
      ( r1_tarski(C_65,k3_subset_1(A_66,k1_xboole_0))
      | ~ m1_subset_1(C_65,k1_zfmisc_1(A_66))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_66)) ) ),
    inference(resolution,[status(thm)],[c_16,c_550])).

tff(c_712,plain,(
    ! [C_74,A_75] :
      ( r1_tarski(C_74,A_75)
      | ~ m1_subset_1(C_74,k1_zfmisc_1(A_75)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_44,c_560])).

tff(c_721,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_712])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k3_xboole_0(A_11,B_12) = A_11
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_728,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_721,c_14])).

tff(c_752,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_728])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_766,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_752,c_12])).

tff(c_773,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_458,c_766])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_7,B_8] : r1_xboole_0(k3_xboole_0(A_7,B_8),k5_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_739,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_3','#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_728,c_10])).

tff(c_754,plain,(
    r1_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_739])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = A_17
      | ~ r1_xboole_0(A_17,B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_785,plain,(
    k4_xboole_0('#skF_3',k5_xboole_0('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_754,c_20])).

tff(c_832,plain,(
    k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_773,c_785])).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_22,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_367,plain,(
    ! [A_55,C_56,B_57] :
      ( r1_xboole_0(A_55,C_56)
      | ~ r1_xboole_0(B_57,C_56)
      | ~ r1_tarski(A_55,B_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1776,plain,(
    ! [A_103,B_104,A_105] :
      ( r1_xboole_0(A_103,B_104)
      | ~ r1_tarski(A_103,A_105)
      | k4_xboole_0(A_105,B_104) != A_105 ) ),
    inference(resolution,[status(thm)],[c_22,c_367])).

tff(c_1793,plain,(
    ! [B_106] :
      ( r1_xboole_0('#skF_2',B_106)
      | k4_xboole_0('#skF_3',B_106) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_40,c_1776])).

tff(c_1809,plain,(
    ! [B_108] :
      ( k4_xboole_0('#skF_2',B_108) = '#skF_2'
      | k4_xboole_0('#skF_3',B_108) != '#skF_3' ) ),
    inference(resolution,[status(thm)],[c_1793,c_20])).

tff(c_38,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_162,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k1_xboole_0
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_176,plain,(
    k4_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_38,c_162])).

tff(c_1841,plain,
    ( k1_xboole_0 = '#skF_2'
    | k4_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_3')) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1809,c_176])).

tff(c_1880,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_832,c_1841])).

tff(c_1882,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_1880])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n011.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:11:57 EST 2020
% 0.11/0.32  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.59  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.59  
% 3.24/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.59  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.24/1.59  
% 3.24/1.59  %Foreground sorts:
% 3.24/1.59  
% 3.24/1.59  
% 3.24/1.59  %Background operators:
% 3.24/1.59  
% 3.24/1.59  
% 3.24/1.59  %Foreground operators:
% 3.24/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.24/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.24/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.24/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.24/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.24/1.59  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.24/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.24/1.59  tff('#skF_2', type, '#skF_2': $i).
% 3.24/1.59  tff('#skF_3', type, '#skF_3': $i).
% 3.24/1.59  tff('#skF_1', type, '#skF_1': $i).
% 3.24/1.59  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.24/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.24/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.24/1.59  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.24/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.24/1.59  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.24/1.59  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.24/1.59  
% 3.24/1.61  tff(f_83, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => ((r1_tarski(B, C) & r1_tarski(B, k3_subset_1(A, C))) => (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_subset_1)).
% 3.24/1.61  tff(f_61, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 3.24/1.61  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.24/1.61  tff(f_74, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 3.24/1.61  tff(f_55, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 3.24/1.61  tff(f_57, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 3.24/1.61  tff(f_63, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 3.24/1.61  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.24/1.61  tff(f_72, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, k3_subset_1(A, C)) => r1_tarski(C, k3_subset_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_subset_1)).
% 3.24/1.61  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.24/1.61  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.24/1.61  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.24/1.61  tff(f_35, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 3.24/1.61  tff(f_53, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.24/1.61  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.24/1.61  tff(f_33, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 3.24/1.61  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.24/1.61  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.24/1.61  tff(c_449, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.24/1.61  tff(c_458, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_449])).
% 3.24/1.61  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.24/1.61  tff(c_34, plain, (![A_28]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.24/1.61  tff(c_24, plain, (![A_19]: (k1_subset_1(A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.24/1.61  tff(c_26, plain, (![A_20]: (k2_subset_1(A_20)=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.24/1.61  tff(c_30, plain, (![A_23]: (k3_subset_1(A_23, k1_subset_1(A_23))=k2_subset_1(A_23))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.24/1.61  tff(c_43, plain, (![A_23]: (k3_subset_1(A_23, k1_subset_1(A_23))=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_30])).
% 3.24/1.61  tff(c_44, plain, (![A_23]: (k3_subset_1(A_23, k1_xboole_0)=A_23)), inference(demodulation, [status(thm), theory('equality')], [c_24, c_43])).
% 3.24/1.61  tff(c_16, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.24/1.61  tff(c_550, plain, (![C_65, A_66, B_67]: (r1_tarski(C_65, k3_subset_1(A_66, B_67)) | ~r1_tarski(B_67, k3_subset_1(A_66, C_65)) | ~m1_subset_1(C_65, k1_zfmisc_1(A_66)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.24/1.61  tff(c_560, plain, (![C_65, A_66]: (r1_tarski(C_65, k3_subset_1(A_66, k1_xboole_0)) | ~m1_subset_1(C_65, k1_zfmisc_1(A_66)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_66)))), inference(resolution, [status(thm)], [c_16, c_550])).
% 3.24/1.61  tff(c_712, plain, (![C_74, A_75]: (r1_tarski(C_74, A_75) | ~m1_subset_1(C_74, k1_zfmisc_1(A_75)))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_44, c_560])).
% 3.24/1.61  tff(c_721, plain, (r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_712])).
% 3.24/1.61  tff(c_14, plain, (![A_11, B_12]: (k3_xboole_0(A_11, B_12)=A_11 | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.24/1.61  tff(c_728, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_721, c_14])).
% 3.24/1.61  tff(c_752, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_2, c_728])).
% 3.24/1.61  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.24/1.61  tff(c_766, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_752, c_12])).
% 3.24/1.61  tff(c_773, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_458, c_766])).
% 3.24/1.61  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.24/1.61  tff(c_10, plain, (![A_7, B_8]: (r1_xboole_0(k3_xboole_0(A_7, B_8), k5_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.24/1.61  tff(c_739, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_3', '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_728, c_10])).
% 3.24/1.61  tff(c_754, plain, (r1_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_739])).
% 3.24/1.61  tff(c_20, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=A_17 | ~r1_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.61  tff(c_785, plain, (k4_xboole_0('#skF_3', k5_xboole_0('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_754, c_20])).
% 3.24/1.61  tff(c_832, plain, (k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_773, c_785])).
% 3.24/1.61  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.24/1.61  tff(c_22, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.24/1.61  tff(c_367, plain, (![A_55, C_56, B_57]: (r1_xboole_0(A_55, C_56) | ~r1_xboole_0(B_57, C_56) | ~r1_tarski(A_55, B_57))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.24/1.61  tff(c_1776, plain, (![A_103, B_104, A_105]: (r1_xboole_0(A_103, B_104) | ~r1_tarski(A_103, A_105) | k4_xboole_0(A_105, B_104)!=A_105)), inference(resolution, [status(thm)], [c_22, c_367])).
% 3.24/1.61  tff(c_1793, plain, (![B_106]: (r1_xboole_0('#skF_2', B_106) | k4_xboole_0('#skF_3', B_106)!='#skF_3')), inference(resolution, [status(thm)], [c_40, c_1776])).
% 3.24/1.61  tff(c_1809, plain, (![B_108]: (k4_xboole_0('#skF_2', B_108)='#skF_2' | k4_xboole_0('#skF_3', B_108)!='#skF_3')), inference(resolution, [status(thm)], [c_1793, c_20])).
% 3.24/1.61  tff(c_38, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.24/1.61  tff(c_162, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k1_xboole_0 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.24/1.61  tff(c_176, plain, (k4_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k1_xboole_0), inference(resolution, [status(thm)], [c_38, c_162])).
% 3.24/1.61  tff(c_1841, plain, (k1_xboole_0='#skF_2' | k4_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_3'))!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1809, c_176])).
% 3.24/1.61  tff(c_1880, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_832, c_1841])).
% 3.24/1.61  tff(c_1882, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_1880])).
% 3.24/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.24/1.61  
% 3.24/1.61  Inference rules
% 3.24/1.61  ----------------------
% 3.24/1.61  #Ref     : 0
% 3.24/1.61  #Sup     : 484
% 3.24/1.61  #Fact    : 0
% 3.24/1.61  #Define  : 0
% 3.24/1.61  #Split   : 3
% 3.24/1.61  #Chain   : 0
% 3.24/1.61  #Close   : 0
% 3.24/1.61  
% 3.24/1.61  Ordering : KBO
% 3.24/1.61  
% 3.24/1.61  Simplification rules
% 3.24/1.61  ----------------------
% 3.24/1.61  #Subsume      : 71
% 3.24/1.61  #Demod        : 294
% 3.24/1.61  #Tautology    : 268
% 3.24/1.61  #SimpNegUnit  : 7
% 3.24/1.61  #BackRed      : 6
% 3.24/1.61  
% 3.24/1.61  #Partial instantiations: 0
% 3.24/1.61  #Strategies tried      : 1
% 3.24/1.61  
% 3.24/1.61  Timing (in seconds)
% 3.24/1.61  ----------------------
% 3.24/1.61  Preprocessing        : 0.29
% 3.24/1.61  Parsing              : 0.15
% 3.24/1.61  CNF conversion       : 0.02
% 3.24/1.61  Main loop            : 0.54
% 3.24/1.61  Inferencing          : 0.17
% 3.24/1.61  Reduction            : 0.21
% 3.24/1.61  Demodulation         : 0.17
% 3.24/1.61  BG Simplification    : 0.02
% 3.24/1.61  Subsumption          : 0.09
% 3.24/1.61  Abstraction          : 0.02
% 3.24/1.61  MUC search           : 0.00
% 3.24/1.61  Cooper               : 0.00
% 3.24/1.61  Total                : 0.86
% 3.24/1.61  Index Insertion      : 0.00
% 3.24/1.61  Index Deletion       : 0.00
% 3.24/1.61  Index Matching       : 0.00
% 3.24/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------
