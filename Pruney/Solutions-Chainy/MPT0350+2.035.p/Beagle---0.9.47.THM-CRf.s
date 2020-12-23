%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:30 EST 2020

% Result     : Theorem 4.77s
% Output     : CNFRefutation 5.03s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 123 expanded)
%              Number of leaves         :   28 (  53 expanded)
%              Depth                    :   10
%              Number of atoms          :   83 ( 161 expanded)
%              Number of equality atoms :   42 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_39,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_45,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(c_12,plain,(
    ! [A_10] : k2_subset_1(A_10) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_28,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_33,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_28])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_13] : m1_subset_1(k2_subset_1(A_13),k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_31,plain,(
    ! [A_13] : m1_subset_1(A_13,k1_zfmisc_1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_528,plain,(
    ! [A_60,B_61,C_62] :
      ( k4_subset_1(A_60,B_61,C_62) = k2_xboole_0(B_61,C_62)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(A_60))
      | ~ m1_subset_1(B_61,k1_zfmisc_1(A_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_766,plain,(
    ! [A_68,B_69] :
      ( k4_subset_1(A_68,B_69,A_68) = k2_xboole_0(B_69,A_68)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_68)) ) ),
    inference(resolution,[status(thm)],[c_31,c_528])).

tff(c_776,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_766])).

tff(c_788,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_776])).

tff(c_10,plain,(
    ! [A_9] : k1_subset_1(A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_26,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_subset_1(A_24)) = k2_subset_1(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_32,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_subset_1(A_24)) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_34,plain,(
    ! [A_24] : k3_subset_1(A_24,k1_xboole_0) = A_24 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_32])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_688,plain,(
    ! [B_67] :
      ( k4_subset_1('#skF_1',B_67,'#skF_2') = k2_xboole_0(B_67,'#skF_2')
      | ~ m1_subset_1(B_67,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_528])).

tff(c_709,plain,(
    k4_subset_1('#skF_1','#skF_1','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_688])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k4_subset_1(A_16,B_17,C_18),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_735,plain,
    ( m1_subset_1(k2_xboole_0('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_709,c_20])).

tff(c_739,plain,(
    m1_subset_1(k2_xboole_0('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_31,c_30,c_735])).

tff(c_14,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_748,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_739,c_14])).

tff(c_755,plain,(
    k3_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_748])).

tff(c_403,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k4_subset_1(A_54,B_55,C_56),k1_zfmisc_1(A_54))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_22,plain,(
    ! [A_19,B_20] :
      ( k3_subset_1(A_19,k3_subset_1(A_19,B_20)) = B_20
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1855,plain,(
    ! [A_94,B_95,C_96] :
      ( k3_subset_1(A_94,k3_subset_1(A_94,k4_subset_1(A_94,B_95,C_96))) = k4_subset_1(A_94,B_95,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_94))
      | ~ m1_subset_1(B_95,k1_zfmisc_1(A_94)) ) ),
    inference(resolution,[status(thm)],[c_403,c_22])).

tff(c_1873,plain,
    ( k3_subset_1('#skF_1',k3_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2'))) = k4_subset_1('#skF_1','#skF_2','#skF_1')
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_788,c_1855])).

tff(c_1882,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_31,c_788,c_34,c_755,c_1873])).

tff(c_375,plain,(
    ! [A_52,B_53] :
      ( k4_xboole_0(A_52,B_53) = k3_subset_1(A_52,B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_386,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_375])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_397,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_4])).

tff(c_401,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_397])).

tff(c_18,plain,(
    ! [A_14,B_15] :
      ( m1_subset_1(k3_subset_1(A_14,B_15),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1498,plain,(
    ! [A_86,B_87,B_88] :
      ( k4_subset_1(A_86,B_87,k3_subset_1(A_86,B_88)) = k2_xboole_0(B_87,k3_subset_1(A_86,B_88))
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_86))
      | ~ m1_subset_1(B_88,k1_zfmisc_1(A_86)) ) ),
    inference(resolution,[status(thm)],[c_18,c_528])).

tff(c_1763,plain,(
    ! [B_92] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_92)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_92))
      | ~ m1_subset_1(B_92,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_1498])).

tff(c_1781,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_30,c_1763])).

tff(c_1793,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_401,c_1781])).

tff(c_2308,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1882,c_1793])).

tff(c_2309,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_33,c_2308])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:08:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.77/2.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.03/2.30  
% 5.03/2.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.03/2.30  %$ m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_1
% 5.03/2.30  
% 5.03/2.30  %Foreground sorts:
% 5.03/2.30  
% 5.03/2.30  
% 5.03/2.30  %Background operators:
% 5.03/2.30  
% 5.03/2.30  
% 5.03/2.30  %Foreground operators:
% 5.03/2.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.03/2.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.03/2.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.03/2.30  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.03/2.30  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.03/2.30  tff('#skF_2', type, '#skF_2': $i).
% 5.03/2.30  tff('#skF_1', type, '#skF_1': $i).
% 5.03/2.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.03/2.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.03/2.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 5.03/2.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.03/2.30  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 5.03/2.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.03/2.30  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 5.03/2.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.03/2.30  
% 5.03/2.33  tff(f_39, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 5.03/2.33  tff(f_72, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 5.03/2.33  tff(f_45, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 5.03/2.33  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 5.03/2.33  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.03/2.33  tff(f_37, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 5.03/2.33  tff(f_67, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_subset_1)).
% 5.03/2.33  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.03/2.33  tff(f_55, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.03/2.33  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.03/2.33  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.03/2.33  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 5.03/2.33  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.03/2.33  tff(c_12, plain, (![A_10]: (k2_subset_1(A_10)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 5.03/2.33  tff(c_28, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.03/2.33  tff(c_33, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_28])).
% 5.03/2.33  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.03/2.33  tff(c_16, plain, (![A_13]: (m1_subset_1(k2_subset_1(A_13), k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.03/2.33  tff(c_31, plain, (![A_13]: (m1_subset_1(A_13, k1_zfmisc_1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_16])).
% 5.03/2.33  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.03/2.33  tff(c_528, plain, (![A_60, B_61, C_62]: (k4_subset_1(A_60, B_61, C_62)=k2_xboole_0(B_61, C_62) | ~m1_subset_1(C_62, k1_zfmisc_1(A_60)) | ~m1_subset_1(B_61, k1_zfmisc_1(A_60)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 5.03/2.33  tff(c_766, plain, (![A_68, B_69]: (k4_subset_1(A_68, B_69, A_68)=k2_xboole_0(B_69, A_68) | ~m1_subset_1(B_69, k1_zfmisc_1(A_68)))), inference(resolution, [status(thm)], [c_31, c_528])).
% 5.03/2.33  tff(c_776, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_766])).
% 5.03/2.33  tff(c_788, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_776])).
% 5.03/2.33  tff(c_10, plain, (![A_9]: (k1_subset_1(A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.03/2.33  tff(c_26, plain, (![A_24]: (k3_subset_1(A_24, k1_subset_1(A_24))=k2_subset_1(A_24))), inference(cnfTransformation, [status(thm)], [f_67])).
% 5.03/2.33  tff(c_32, plain, (![A_24]: (k3_subset_1(A_24, k1_subset_1(A_24))=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 5.03/2.33  tff(c_34, plain, (![A_24]: (k3_subset_1(A_24, k1_xboole_0)=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_32])).
% 5.03/2.33  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.03/2.33  tff(c_688, plain, (![B_67]: (k4_subset_1('#skF_1', B_67, '#skF_2')=k2_xboole_0(B_67, '#skF_2') | ~m1_subset_1(B_67, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_528])).
% 5.03/2.33  tff(c_709, plain, (k4_subset_1('#skF_1', '#skF_1', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_31, c_688])).
% 5.03/2.33  tff(c_20, plain, (![A_16, B_17, C_18]: (m1_subset_1(k4_subset_1(A_16, B_17, C_18), k1_zfmisc_1(A_16)) | ~m1_subset_1(C_18, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.03/2.33  tff(c_735, plain, (m1_subset_1(k2_xboole_0('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_709, c_20])).
% 5.03/2.33  tff(c_739, plain, (m1_subset_1(k2_xboole_0('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_31, c_30, c_735])).
% 5.03/2.33  tff(c_14, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.03/2.33  tff(c_748, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_739, c_14])).
% 5.03/2.33  tff(c_755, plain, (k3_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_6, c_748])).
% 5.03/2.33  tff(c_403, plain, (![A_54, B_55, C_56]: (m1_subset_1(k4_subset_1(A_54, B_55, C_56), k1_zfmisc_1(A_54)) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.03/2.33  tff(c_22, plain, (![A_19, B_20]: (k3_subset_1(A_19, k3_subset_1(A_19, B_20))=B_20 | ~m1_subset_1(B_20, k1_zfmisc_1(A_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 5.03/2.33  tff(c_1855, plain, (![A_94, B_95, C_96]: (k3_subset_1(A_94, k3_subset_1(A_94, k4_subset_1(A_94, B_95, C_96)))=k4_subset_1(A_94, B_95, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_94)) | ~m1_subset_1(B_95, k1_zfmisc_1(A_94)))), inference(resolution, [status(thm)], [c_403, c_22])).
% 5.03/2.33  tff(c_1873, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2')))=k4_subset_1('#skF_1', '#skF_2', '#skF_1') | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_788, c_1855])).
% 5.03/2.33  tff(c_1882, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_30, c_31, c_788, c_34, c_755, c_1873])).
% 5.03/2.33  tff(c_375, plain, (![A_52, B_53]: (k4_xboole_0(A_52, B_53)=k3_subset_1(A_52, B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_52)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.03/2.33  tff(c_386, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_30, c_375])).
% 5.03/2.33  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.03/2.33  tff(c_397, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_386, c_4])).
% 5.03/2.33  tff(c_401, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_397])).
% 5.03/2.33  tff(c_18, plain, (![A_14, B_15]: (m1_subset_1(k3_subset_1(A_14, B_15), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.03/2.33  tff(c_1498, plain, (![A_86, B_87, B_88]: (k4_subset_1(A_86, B_87, k3_subset_1(A_86, B_88))=k2_xboole_0(B_87, k3_subset_1(A_86, B_88)) | ~m1_subset_1(B_87, k1_zfmisc_1(A_86)) | ~m1_subset_1(B_88, k1_zfmisc_1(A_86)))), inference(resolution, [status(thm)], [c_18, c_528])).
% 5.03/2.33  tff(c_1763, plain, (![B_92]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_92))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_92)) | ~m1_subset_1(B_92, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_1498])).
% 5.03/2.33  tff(c_1781, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_30, c_1763])).
% 5.03/2.33  tff(c_1793, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_401, c_1781])).
% 5.03/2.33  tff(c_2308, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1882, c_1793])).
% 5.03/2.33  tff(c_2309, plain, $false, inference(negUnitSimplification, [status(thm)], [c_33, c_2308])).
% 5.03/2.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.03/2.33  
% 5.03/2.33  Inference rules
% 5.03/2.33  ----------------------
% 5.03/2.33  #Ref     : 1
% 5.03/2.33  #Sup     : 574
% 5.03/2.33  #Fact    : 0
% 5.03/2.33  #Define  : 0
% 5.03/2.33  #Split   : 0
% 5.03/2.33  #Chain   : 0
% 5.03/2.33  #Close   : 0
% 5.03/2.33  
% 5.03/2.33  Ordering : KBO
% 5.03/2.33  
% 5.03/2.33  Simplification rules
% 5.03/2.33  ----------------------
% 5.03/2.33  #Subsume      : 28
% 5.03/2.33  #Demod        : 497
% 5.03/2.33  #Tautology    : 388
% 5.03/2.33  #SimpNegUnit  : 1
% 5.03/2.33  #BackRed      : 24
% 5.03/2.33  
% 5.03/2.33  #Partial instantiations: 0
% 5.03/2.33  #Strategies tried      : 1
% 5.03/2.33  
% 5.03/2.33  Timing (in seconds)
% 5.03/2.33  ----------------------
% 5.03/2.33  Preprocessing        : 0.47
% 5.03/2.33  Parsing              : 0.25
% 5.03/2.33  CNF conversion       : 0.03
% 5.03/2.33  Main loop            : 0.95
% 5.03/2.33  Inferencing          : 0.30
% 5.03/2.33  Reduction            : 0.40
% 5.03/2.33  Demodulation         : 0.32
% 5.03/2.33  BG Simplification    : 0.04
% 5.03/2.33  Subsumption          : 0.14
% 5.03/2.33  Abstraction          : 0.05
% 5.03/2.33  MUC search           : 0.00
% 5.03/2.33  Cooper               : 0.00
% 5.03/2.33  Total                : 1.47
% 5.03/2.33  Index Insertion      : 0.00
% 5.03/2.33  Index Deletion       : 0.00
% 5.03/2.33  Index Matching       : 0.00
% 5.03/2.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
