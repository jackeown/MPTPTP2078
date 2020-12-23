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
% DateTime   : Thu Dec  3 09:55:54 EST 2020

% Result     : Theorem 4.83s
% Output     : CNFRefutation 4.83s
% Verified   : 
% Statistics : Number of formulae       :   62 (  97 expanded)
%              Number of leaves         :   24 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   64 ( 130 expanded)
%              Number of equality atoms :   42 (  67 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_22,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_283,plain,(
    ! [A_45,B_46,C_47] :
      ( k9_subset_1(A_45,B_46,C_47) = k3_xboole_0(B_46,C_47)
      | ~ m1_subset_1(C_47,k1_zfmisc_1(A_45)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1937,plain,(
    ! [A_84,B_85,B_86] :
      ( k9_subset_1(A_84,B_85,k3_subset_1(A_84,B_86)) = k3_xboole_0(B_85,k3_subset_1(A_84,B_86))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_84)) ) ),
    inference(resolution,[status(thm)],[c_12,c_283])).

tff(c_1945,plain,(
    ! [B_85] : k9_subset_1('#skF_1',B_85,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_85,k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1937])).

tff(c_24,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_264,plain,(
    ! [A_41,B_42,C_43] :
      ( k7_subset_1(A_41,B_42,C_43) = k4_xboole_0(B_42,C_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_273,plain,(
    ! [C_43] : k7_subset_1('#skF_1','#skF_2',C_43) = k4_xboole_0('#skF_2',C_43) ),
    inference(resolution,[status(thm)],[c_24,c_264])).

tff(c_20,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_293,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_273,c_20])).

tff(c_2066,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_293])).

tff(c_131,plain,(
    ! [A_33,B_34] :
      ( k4_xboole_0(A_33,B_34) = k3_subset_1(A_33,B_34)
      | ~ m1_subset_1(B_34,k1_zfmisc_1(A_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_138,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_22,c_131])).

tff(c_8,plain,(
    ! [A_8,B_9] : k4_xboole_0(A_8,k4_xboole_0(A_8,B_9)) = k3_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_143,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_138,c_8])).

tff(c_88,plain,(
    ! [A_29,B_30] :
      ( k3_subset_1(A_29,k3_subset_1(A_29,B_30)) = B_30
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_93,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_22,c_88])).

tff(c_161,plain,(
    ! [A_35,B_36] :
      ( m1_subset_1(k3_subset_1(A_35,B_36),k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k3_subset_1(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1633,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,k3_subset_1(A_81,B_82)) = k3_subset_1(A_81,k3_subset_1(A_81,B_82))
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(resolution,[status(thm)],[c_161,c_10])).

tff(c_1637,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_22,c_1633])).

tff(c_1642,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_143,c_93,c_1637])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1691,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1642,c_4])).

tff(c_1704,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_1691])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_73,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k3_xboole_0(A_27,B_28)) = k4_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_82,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_73])).

tff(c_139,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_131])).

tff(c_150,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_8])).

tff(c_94,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_1639,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_24,c_1633])).

tff(c_1644,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_150,c_94,c_1639])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] : k5_xboole_0(k3_xboole_0(A_5,B_6),k3_xboole_0(C_7,B_6)) = k3_xboole_0(k5_xboole_0(A_5,C_7),B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1739,plain,(
    ! [C_7] : k5_xboole_0('#skF_2',k3_xboole_0(C_7,'#skF_2')) = k3_xboole_0(k5_xboole_0('#skF_1',C_7),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1644,c_6])).

tff(c_1847,plain,(
    ! [C_83] : k3_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_83)) = k4_xboole_0('#skF_2',C_83) ),
    inference(demodulation,[status(thm),theory(equality)],[c_82,c_2,c_1739])).

tff(c_1906,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1704,c_1847])).

tff(c_2599,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2066,c_1906])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 11:50:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.83/2.32  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/2.32  
% 4.83/2.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/2.32  %$ m1_subset_1 > k9_subset_1 > k7_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.83/2.32  
% 4.83/2.32  %Foreground sorts:
% 4.83/2.32  
% 4.83/2.32  
% 4.83/2.32  %Background operators:
% 4.83/2.32  
% 4.83/2.32  
% 4.83/2.32  %Foreground operators:
% 4.83/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.83/2.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.83/2.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.83/2.32  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.83/2.32  tff('#skF_2', type, '#skF_2': $i).
% 4.83/2.32  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.83/2.32  tff('#skF_3', type, '#skF_3': $i).
% 4.83/2.32  tff('#skF_1', type, '#skF_1': $i).
% 4.83/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.83/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.83/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.83/2.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.83/2.32  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 4.83/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.83/2.32  
% 4.83/2.34  tff(f_61, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_subset_1)).
% 4.83/2.34  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.83/2.34  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 4.83/2.34  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.83/2.34  tff(f_37, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.83/2.34  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.83/2.34  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.83/2.34  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.83/2.34  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.83/2.34  tff(f_31, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 4.83/2.34  tff(c_22, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.83/2.34  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.83/2.34  tff(c_283, plain, (![A_45, B_46, C_47]: (k9_subset_1(A_45, B_46, C_47)=k3_xboole_0(B_46, C_47) | ~m1_subset_1(C_47, k1_zfmisc_1(A_45)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.83/2.34  tff(c_1937, plain, (![A_84, B_85, B_86]: (k9_subset_1(A_84, B_85, k3_subset_1(A_84, B_86))=k3_xboole_0(B_85, k3_subset_1(A_84, B_86)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_84)))), inference(resolution, [status(thm)], [c_12, c_283])).
% 4.83/2.34  tff(c_1945, plain, (![B_85]: (k9_subset_1('#skF_1', B_85, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_85, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_22, c_1937])).
% 4.83/2.34  tff(c_24, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.83/2.34  tff(c_264, plain, (![A_41, B_42, C_43]: (k7_subset_1(A_41, B_42, C_43)=k4_xboole_0(B_42, C_43) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 4.83/2.34  tff(c_273, plain, (![C_43]: (k7_subset_1('#skF_1', '#skF_2', C_43)=k4_xboole_0('#skF_2', C_43))), inference(resolution, [status(thm)], [c_24, c_264])).
% 4.83/2.34  tff(c_20, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.83/2.34  tff(c_293, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_273, c_20])).
% 4.83/2.34  tff(c_2066, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_293])).
% 4.83/2.34  tff(c_131, plain, (![A_33, B_34]: (k4_xboole_0(A_33, B_34)=k3_subset_1(A_33, B_34) | ~m1_subset_1(B_34, k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.83/2.34  tff(c_138, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_22, c_131])).
% 4.83/2.34  tff(c_8, plain, (![A_8, B_9]: (k4_xboole_0(A_8, k4_xboole_0(A_8, B_9))=k3_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.83/2.34  tff(c_143, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_138, c_8])).
% 4.83/2.34  tff(c_88, plain, (![A_29, B_30]: (k3_subset_1(A_29, k3_subset_1(A_29, B_30))=B_30 | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.83/2.34  tff(c_93, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_22, c_88])).
% 4.83/2.34  tff(c_161, plain, (![A_35, B_36]: (m1_subset_1(k3_subset_1(A_35, B_36), k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.83/2.34  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k3_subset_1(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.83/2.34  tff(c_1633, plain, (![A_81, B_82]: (k4_xboole_0(A_81, k3_subset_1(A_81, B_82))=k3_subset_1(A_81, k3_subset_1(A_81, B_82)) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(resolution, [status(thm)], [c_161, c_10])).
% 4.83/2.34  tff(c_1637, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_22, c_1633])).
% 4.83/2.34  tff(c_1642, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_143, c_93, c_1637])).
% 4.83/2.34  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.83/2.34  tff(c_1691, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1642, c_4])).
% 4.83/2.34  tff(c_1704, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_138, c_1691])).
% 4.83/2.34  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.83/2.34  tff(c_73, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k3_xboole_0(A_27, B_28))=k4_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.83/2.34  tff(c_82, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_73])).
% 4.83/2.34  tff(c_139, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_24, c_131])).
% 4.83/2.34  tff(c_150, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_139, c_8])).
% 4.83/2.34  tff(c_94, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_24, c_88])).
% 4.83/2.34  tff(c_1639, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_24, c_1633])).
% 4.83/2.34  tff(c_1644, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_150, c_94, c_1639])).
% 4.83/2.34  tff(c_6, plain, (![A_5, B_6, C_7]: (k5_xboole_0(k3_xboole_0(A_5, B_6), k3_xboole_0(C_7, B_6))=k3_xboole_0(k5_xboole_0(A_5, C_7), B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.83/2.34  tff(c_1739, plain, (![C_7]: (k5_xboole_0('#skF_2', k3_xboole_0(C_7, '#skF_2'))=k3_xboole_0(k5_xboole_0('#skF_1', C_7), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1644, c_6])).
% 4.83/2.34  tff(c_1847, plain, (![C_83]: (k3_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_83))=k4_xboole_0('#skF_2', C_83))), inference(demodulation, [status(thm), theory('equality')], [c_82, c_2, c_1739])).
% 4.83/2.34  tff(c_1906, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1704, c_1847])).
% 4.83/2.34  tff(c_2599, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2066, c_1906])).
% 4.83/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.83/2.34  
% 4.83/2.34  Inference rules
% 4.83/2.34  ----------------------
% 4.83/2.34  #Ref     : 0
% 4.83/2.34  #Sup     : 712
% 4.83/2.34  #Fact    : 0
% 4.83/2.34  #Define  : 0
% 4.83/2.34  #Split   : 0
% 4.83/2.34  #Chain   : 0
% 4.83/2.34  #Close   : 0
% 4.83/2.34  
% 4.83/2.34  Ordering : KBO
% 4.83/2.34  
% 4.83/2.34  Simplification rules
% 4.83/2.34  ----------------------
% 4.83/2.34  #Subsume      : 35
% 4.83/2.34  #Demod        : 360
% 4.83/2.34  #Tautology    : 242
% 4.83/2.34  #SimpNegUnit  : 1
% 4.83/2.34  #BackRed      : 9
% 4.83/2.34  
% 4.83/2.34  #Partial instantiations: 0
% 4.83/2.34  #Strategies tried      : 1
% 4.83/2.34  
% 4.83/2.34  Timing (in seconds)
% 4.83/2.34  ----------------------
% 4.83/2.34  Preprocessing        : 0.47
% 4.83/2.34  Parsing              : 0.24
% 4.83/2.34  CNF conversion       : 0.03
% 4.83/2.34  Main loop            : 0.92
% 4.83/2.34  Inferencing          : 0.29
% 4.83/2.34  Reduction            : 0.39
% 4.83/2.34  Demodulation         : 0.32
% 4.83/2.34  BG Simplification    : 0.04
% 4.83/2.34  Subsumption          : 0.14
% 4.83/2.34  Abstraction          : 0.05
% 4.83/2.34  MUC search           : 0.00
% 4.83/2.34  Cooper               : 0.00
% 4.83/2.34  Total                : 1.42
% 4.83/2.34  Index Insertion      : 0.00
% 4.83/2.34  Index Deletion       : 0.00
% 4.83/2.34  Index Matching       : 0.00
% 4.83/2.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
