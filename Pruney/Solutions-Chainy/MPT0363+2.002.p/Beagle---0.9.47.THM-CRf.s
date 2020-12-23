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
% DateTime   : Thu Dec  3 09:56:36 EST 2020

% Result     : Theorem 4.94s
% Output     : CNFRefutation 4.94s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 110 expanded)
%              Number of leaves         :   26 (  47 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 183 expanded)
%              Number of equality atoms :   24 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_xboole_0(B,C)
            <=> r1_tarski(B,k3_subset_1(A,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_41,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : r1_tarski(k3_xboole_0(A,B),k2_xboole_0(A,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,k2_xboole_0(B,C))
        & r1_xboole_0(A,C) )
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k4_xboole_0(B,C))
     => ( r1_tarski(A,B)
        & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_529,plain,(
    ! [A_93,B_94] :
      ( k3_subset_1(A_93,k3_subset_1(A_93,B_94)) = B_94
      | ~ m1_subset_1(B_94,k1_zfmisc_1(A_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_535,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_26,c_529])).

tff(c_362,plain,(
    ! [A_87,B_88] :
      ( k4_xboole_0(A_87,B_88) = k3_subset_1(A_87,B_88)
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_87)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_370,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_362])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_411,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_370,c_10])).

tff(c_628,plain,(
    ! [A_97,B_98] :
      ( m1_subset_1(k3_subset_1(A_97,B_98),k1_zfmisc_1(A_97))
      | ~ m1_subset_1(B_98,k1_zfmisc_1(A_97)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_18,plain,(
    ! [A_17,B_18] :
      ( k4_xboole_0(A_17,B_18) = k3_subset_1(A_17,B_18)
      | ~ m1_subset_1(B_18,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1738,plain,(
    ! [A_187,B_188] :
      ( k4_xboole_0(A_187,k3_subset_1(A_187,B_188)) = k3_subset_1(A_187,k3_subset_1(A_187,B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1(A_187)) ) ),
    inference(resolution,[status(thm)],[c_628,c_18])).

tff(c_1744,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_1738])).

tff(c_1749,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_535,c_411,c_1744])).

tff(c_14,plain,(
    ! [A_13] : r1_xboole_0(A_13,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : r1_tarski(k3_xboole_0(A_6,B_7),k2_xboole_0(A_6,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_743,plain,(
    ! [A_111,B_112,C_113] :
      ( r1_tarski(A_111,B_112)
      | ~ r1_xboole_0(A_111,C_113)
      | ~ r1_tarski(A_111,k2_xboole_0(B_112,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_999,plain,(
    ! [A_140,B_141,C_142] :
      ( r1_tarski(k3_xboole_0(A_140,B_141),A_140)
      | ~ r1_xboole_0(k3_xboole_0(A_140,B_141),C_142) ) ),
    inference(resolution,[status(thm)],[c_8,c_743])).

tff(c_1028,plain,(
    ! [A_140,B_141] : r1_tarski(k3_xboole_0(A_140,B_141),A_140) ),
    inference(resolution,[status(thm)],[c_14,c_999])).

tff(c_1837,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1749,c_1028])).

tff(c_34,plain,
    ( r1_xboole_0('#skF_2','#skF_3')
    | r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_102,plain,(
    r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_28,plain,
    ( ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3'))
    | ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_155,plain,(
    ~ r1_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_28])).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_190,plain,(
    ! [A_60,B_61] :
      ( k4_xboole_0(A_60,B_61) = k3_subset_1(A_60,B_61)
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_197,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_190])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_tarski(A_3,k4_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_251,plain,(
    ! [A_64] :
      ( r1_xboole_0(A_64,'#skF_3')
      | ~ r1_tarski(A_64,k3_subset_1('#skF_1','#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_4])).

tff(c_262,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_102,c_251])).

tff(c_272,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_262])).

tff(c_273,plain,(
    r1_xboole_0('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_369,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_362])).

tff(c_386,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_369,c_10])).

tff(c_534,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_529])).

tff(c_1742,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_1738])).

tff(c_1747,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_386,c_534,c_1742])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1285,plain,(
    ! [A_163,A_164,B_165] :
      ( r1_tarski(A_163,A_164)
      | ~ r1_xboole_0(A_163,B_165)
      | ~ r1_tarski(A_163,k2_xboole_0(B_165,A_164)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_743])).

tff(c_3228,plain,(
    ! [A_262,A_263,B_264] :
      ( r1_tarski(A_262,k4_xboole_0(A_263,B_264))
      | ~ r1_xboole_0(A_262,k3_xboole_0(A_263,B_264))
      | ~ r1_tarski(A_262,A_263) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1285])).

tff(c_3240,plain,(
    ! [A_262] :
      ( r1_tarski(A_262,k4_xboole_0('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_262,'#skF_3')
      | ~ r1_tarski(A_262,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1747,c_3228])).

tff(c_3572,plain,(
    ! [A_287] :
      ( r1_tarski(A_287,k3_subset_1('#skF_1','#skF_3'))
      | ~ r1_xboole_0(A_287,'#skF_3')
      | ~ r1_tarski(A_287,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_369,c_3240])).

tff(c_274,plain,(
    ~ r1_tarski('#skF_2',k3_subset_1('#skF_1','#skF_3')) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_3581,plain,
    ( ~ r1_xboole_0('#skF_2','#skF_3')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_3572,c_274])).

tff(c_3587,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1837,c_273,c_3581])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:55:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.94/1.99  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/2.00  
% 4.94/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/2.00  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 4.94/2.00  
% 4.94/2.00  %Foreground sorts:
% 4.94/2.00  
% 4.94/2.00  
% 4.94/2.00  %Background operators:
% 4.94/2.00  
% 4.94/2.00  
% 4.94/2.00  %Foreground operators:
% 4.94/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.94/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.94/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.94/2.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.94/2.00  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.94/2.00  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.94/2.00  tff('#skF_2', type, '#skF_2': $i).
% 4.94/2.00  tff('#skF_3', type, '#skF_3': $i).
% 4.94/2.00  tff('#skF_1', type, '#skF_1': $i).
% 4.94/2.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.94/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.94/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.94/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.94/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.94/2.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.94/2.00  
% 4.94/2.02  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_xboole_0(B, C) <=> r1_tarski(B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_subset_1)).
% 4.94/2.02  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.94/2.02  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.94/2.02  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.94/2.02  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.94/2.02  tff(f_41, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 4.94/2.02  tff(f_35, axiom, (![A, B, C]: r1_tarski(k3_xboole_0(A, B), k2_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_xboole_1)).
% 4.94/2.02  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 4.94/2.02  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 4.94/2.02  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.94/2.02  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.94/2.02  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/2.02  tff(c_529, plain, (![A_93, B_94]: (k3_subset_1(A_93, k3_subset_1(A_93, B_94))=B_94 | ~m1_subset_1(B_94, k1_zfmisc_1(A_93)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.94/2.02  tff(c_535, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_26, c_529])).
% 4.94/2.02  tff(c_362, plain, (![A_87, B_88]: (k4_xboole_0(A_87, B_88)=k3_subset_1(A_87, B_88) | ~m1_subset_1(B_88, k1_zfmisc_1(A_87)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.94/2.02  tff(c_370, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_362])).
% 4.94/2.02  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.94/2.02  tff(c_411, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_370, c_10])).
% 4.94/2.02  tff(c_628, plain, (![A_97, B_98]: (m1_subset_1(k3_subset_1(A_97, B_98), k1_zfmisc_1(A_97)) | ~m1_subset_1(B_98, k1_zfmisc_1(A_97)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.94/2.02  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, B_18)=k3_subset_1(A_17, B_18) | ~m1_subset_1(B_18, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.94/2.02  tff(c_1738, plain, (![A_187, B_188]: (k4_xboole_0(A_187, k3_subset_1(A_187, B_188))=k3_subset_1(A_187, k3_subset_1(A_187, B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1(A_187)))), inference(resolution, [status(thm)], [c_628, c_18])).
% 4.94/2.02  tff(c_1744, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_1738])).
% 4.94/2.02  tff(c_1749, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_535, c_411, c_1744])).
% 4.94/2.02  tff(c_14, plain, (![A_13]: (r1_xboole_0(A_13, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.94/2.02  tff(c_8, plain, (![A_6, B_7, C_8]: (r1_tarski(k3_xboole_0(A_6, B_7), k2_xboole_0(A_6, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.94/2.02  tff(c_743, plain, (![A_111, B_112, C_113]: (r1_tarski(A_111, B_112) | ~r1_xboole_0(A_111, C_113) | ~r1_tarski(A_111, k2_xboole_0(B_112, C_113)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.94/2.02  tff(c_999, plain, (![A_140, B_141, C_142]: (r1_tarski(k3_xboole_0(A_140, B_141), A_140) | ~r1_xboole_0(k3_xboole_0(A_140, B_141), C_142))), inference(resolution, [status(thm)], [c_8, c_743])).
% 4.94/2.02  tff(c_1028, plain, (![A_140, B_141]: (r1_tarski(k3_xboole_0(A_140, B_141), A_140))), inference(resolution, [status(thm)], [c_14, c_999])).
% 4.94/2.02  tff(c_1837, plain, (r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1749, c_1028])).
% 4.94/2.02  tff(c_34, plain, (r1_xboole_0('#skF_2', '#skF_3') | r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/2.02  tff(c_102, plain, (r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitLeft, [status(thm)], [c_34])).
% 4.94/2.02  tff(c_28, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/2.02  tff(c_155, plain, (~r1_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_102, c_28])).
% 4.94/2.02  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.94/2.02  tff(c_190, plain, (![A_60, B_61]: (k4_xboole_0(A_60, B_61)=k3_subset_1(A_60, B_61) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.94/2.02  tff(c_197, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_190])).
% 4.94/2.02  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_tarski(A_3, k4_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.94/2.02  tff(c_251, plain, (![A_64]: (r1_xboole_0(A_64, '#skF_3') | ~r1_tarski(A_64, k3_subset_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_197, c_4])).
% 4.94/2.02  tff(c_262, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_102, c_251])).
% 4.94/2.02  tff(c_272, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_262])).
% 4.94/2.02  tff(c_273, plain, (r1_xboole_0('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_34])).
% 4.94/2.02  tff(c_369, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_362])).
% 4.94/2.02  tff(c_386, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_369, c_10])).
% 4.94/2.02  tff(c_534, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_529])).
% 4.94/2.02  tff(c_1742, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_1738])).
% 4.94/2.02  tff(c_1747, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_386, c_534, c_1742])).
% 4.94/2.02  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.94/2.02  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.94/2.02  tff(c_1285, plain, (![A_163, A_164, B_165]: (r1_tarski(A_163, A_164) | ~r1_xboole_0(A_163, B_165) | ~r1_tarski(A_163, k2_xboole_0(B_165, A_164)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_743])).
% 4.94/2.02  tff(c_3228, plain, (![A_262, A_263, B_264]: (r1_tarski(A_262, k4_xboole_0(A_263, B_264)) | ~r1_xboole_0(A_262, k3_xboole_0(A_263, B_264)) | ~r1_tarski(A_262, A_263))), inference(superposition, [status(thm), theory('equality')], [c_12, c_1285])).
% 4.94/2.02  tff(c_3240, plain, (![A_262]: (r1_tarski(A_262, k4_xboole_0('#skF_1', '#skF_3')) | ~r1_xboole_0(A_262, '#skF_3') | ~r1_tarski(A_262, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1747, c_3228])).
% 4.94/2.02  tff(c_3572, plain, (![A_287]: (r1_tarski(A_287, k3_subset_1('#skF_1', '#skF_3')) | ~r1_xboole_0(A_287, '#skF_3') | ~r1_tarski(A_287, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_369, c_3240])).
% 4.94/2.02  tff(c_274, plain, (~r1_tarski('#skF_2', k3_subset_1('#skF_1', '#skF_3'))), inference(splitRight, [status(thm)], [c_34])).
% 4.94/2.02  tff(c_3581, plain, (~r1_xboole_0('#skF_2', '#skF_3') | ~r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_3572, c_274])).
% 4.94/2.02  tff(c_3587, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1837, c_273, c_3581])).
% 4.94/2.02  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.94/2.02  
% 4.94/2.02  Inference rules
% 4.94/2.02  ----------------------
% 4.94/2.02  #Ref     : 0
% 4.94/2.02  #Sup     : 860
% 4.94/2.02  #Fact    : 0
% 4.94/2.02  #Define  : 0
% 4.94/2.02  #Split   : 5
% 4.94/2.02  #Chain   : 0
% 4.94/2.02  #Close   : 0
% 4.94/2.02  
% 4.94/2.02  Ordering : KBO
% 4.94/2.02  
% 4.94/2.02  Simplification rules
% 4.94/2.02  ----------------------
% 4.94/2.02  #Subsume      : 45
% 4.94/2.02  #Demod        : 524
% 4.94/2.02  #Tautology    : 428
% 4.94/2.02  #SimpNegUnit  : 1
% 4.94/2.02  #BackRed      : 21
% 4.94/2.02  
% 4.94/2.02  #Partial instantiations: 0
% 4.94/2.02  #Strategies tried      : 1
% 4.94/2.02  
% 4.94/2.02  Timing (in seconds)
% 4.94/2.02  ----------------------
% 4.94/2.02  Preprocessing        : 0.37
% 4.94/2.02  Parsing              : 0.21
% 4.94/2.02  CNF conversion       : 0.02
% 4.94/2.02  Main loop            : 0.87
% 4.94/2.02  Inferencing          : 0.29
% 4.94/2.02  Reduction            : 0.33
% 4.94/2.02  Demodulation         : 0.26
% 4.94/2.02  BG Simplification    : 0.03
% 4.94/2.02  Subsumption          : 0.15
% 4.94/2.02  Abstraction          : 0.03
% 4.94/2.02  MUC search           : 0.00
% 4.94/2.02  Cooper               : 0.00
% 4.94/2.02  Total                : 1.27
% 4.94/2.02  Index Insertion      : 0.00
% 4.94/2.02  Index Deletion       : 0.00
% 4.94/2.02  Index Matching       : 0.00
% 4.94/2.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
