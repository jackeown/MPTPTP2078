%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:55 EST 2020

% Result     : Theorem 5.04s
% Output     : CNFRefutation 5.46s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 215 expanded)
%              Number of leaves         :   21 (  80 expanded)
%              Depth                    :   14
%              Number of atoms          :   83 ( 420 expanded)
%              Number of equality atoms :   32 ( 109 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_27,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_20,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(k3_subset_1(A_6,B_7),k1_zfmisc_1(A_6))
      | ~ m1_subset_1(B_7,k1_zfmisc_1(A_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_137,plain,(
    ! [A_35,B_36,C_37] :
      ( k4_subset_1(A_35,B_36,C_37) = k2_xboole_0(B_36,C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(A_35))
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_179,plain,(
    ! [B_40] :
      ( k4_subset_1('#skF_1',B_40,'#skF_2') = k2_xboole_0(B_40,'#skF_2')
      | ~ m1_subset_1(B_40,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_20,c_137])).

tff(c_962,plain,(
    ! [B_63] :
      ( k4_subset_1('#skF_1',k3_subset_1('#skF_1',B_63),'#skF_2') = k2_xboole_0(k3_subset_1('#skF_1',B_63),'#skF_2')
      | ~ m1_subset_1(B_63,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_6,c_179])).

tff(c_1028,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_20,c_962])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( m1_subset_1(k4_subset_1(A_8,B_9,C_10),k1_zfmisc_1(A_8))
      | ~ m1_subset_1(C_10,k1_zfmisc_1(A_8))
      | ~ m1_subset_1(B_9,k1_zfmisc_1(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1041,plain,
    ( m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1028,c_8])).

tff(c_1045,plain,
    ( m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1041])).

tff(c_1149,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_1045])).

tff(c_1152,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_6,c_1149])).

tff(c_1156,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_1152])).

tff(c_1158,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_1045])).

tff(c_18,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_145,plain,(
    ! [B_36] :
      ( k4_subset_1('#skF_1',B_36,'#skF_3') = k2_xboole_0(B_36,'#skF_3')
      | ~ m1_subset_1(B_36,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_18,c_137])).

tff(c_1264,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_1158,c_145])).

tff(c_118,plain,(
    ! [A_31,B_32,C_33] :
      ( k7_subset_1(A_31,B_32,C_33) = k4_xboole_0(B_32,C_33)
      | ~ m1_subset_1(B_32,k1_zfmisc_1(A_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    ! [C_33] : k7_subset_1('#skF_1','#skF_2',C_33) = k4_xboole_0('#skF_2',C_33) ),
    inference(resolution,[status(thm)],[c_20,c_118])).

tff(c_16,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k7_subset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_147,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_16])).

tff(c_1507,plain,(
    k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) != k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1264,c_147])).

tff(c_66,plain,(
    ! [A_27,B_28] :
      ( k3_subset_1(A_27,k3_subset_1(A_27,B_28)) = B_28
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_75,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_20,c_66])).

tff(c_22,plain,(
    ! [A_22,B_23] :
      ( k4_xboole_0(A_22,B_23) = k3_subset_1(A_22,B_23)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_201,plain,(
    ! [A_41,B_42] :
      ( k4_xboole_0(A_41,k3_subset_1(A_41,B_42)) = k3_subset_1(A_41,k3_subset_1(A_41,B_42))
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_41)) ) ),
    inference(resolution,[status(thm)],[c_6,c_22])).

tff(c_207,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_20,c_201])).

tff(c_212,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_207])).

tff(c_2,plain,(
    ! [A_1,B_2,C_3] : k4_xboole_0(k4_xboole_0(A_1,B_2),C_3) = k4_xboole_0(A_1,k2_xboole_0(B_2,C_3)) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_270,plain,(
    ! [C_3] : k4_xboole_0('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_3)) = k4_xboole_0('#skF_2',C_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_212,c_2])).

tff(c_1511,plain,
    ( m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_8])).

tff(c_1515,plain,(
    m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_18,c_1511])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k3_subset_1(A_4,B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1545,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3')) = k3_subset_1('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3')) ),
    inference(resolution,[status(thm)],[c_1515,c_4])).

tff(c_1558,plain,(
    k3_subset_1('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_270,c_1545])).

tff(c_213,plain,(
    ! [A_43,B_44,C_45] :
      ( m1_subset_1(k4_subset_1(A_43,B_44,C_45),k1_zfmisc_1(A_43))
      | ~ m1_subset_1(C_45,k1_zfmisc_1(A_43))
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( k3_subset_1(A_11,k3_subset_1(A_11,B_12)) = B_12
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1573,plain,(
    ! [A_75,B_76,C_77] :
      ( k3_subset_1(A_75,k3_subset_1(A_75,k4_subset_1(A_75,B_76,C_77))) = k4_subset_1(A_75,B_76,C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(A_75))
      | ~ m1_subset_1(B_76,k1_zfmisc_1(A_75)) ) ),
    inference(resolution,[status(thm)],[c_213,c_10])).

tff(c_1591,plain,
    ( k3_subset_1('#skF_1',k3_subset_1('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3'))) = k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1264,c_1573])).

tff(c_1645,plain,(
    k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1158,c_18,c_1558,c_1264,c_1591])).

tff(c_1647,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1507,c_1645])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:56:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.04/2.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/2.38  
% 5.04/2.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.04/2.38  %$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 5.04/2.38  
% 5.04/2.38  %Foreground sorts:
% 5.04/2.38  
% 5.04/2.38  
% 5.04/2.38  %Background operators:
% 5.04/2.38  
% 5.04/2.38  
% 5.04/2.38  %Foreground operators:
% 5.04/2.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.04/2.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.04/2.38  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 5.04/2.38  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 5.04/2.38  tff('#skF_2', type, '#skF_2': $i).
% 5.04/2.38  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 5.04/2.38  tff('#skF_3', type, '#skF_3': $i).
% 5.04/2.38  tff('#skF_1', type, '#skF_1': $i).
% 5.04/2.38  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 5.04/2.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.04/2.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.04/2.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.04/2.38  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 5.04/2.38  
% 5.46/2.40  tff(f_63, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_subset_1)).
% 5.46/2.40  tff(f_35, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 5.46/2.40  tff(f_51, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 5.46/2.40  tff(f_41, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 5.46/2.40  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 5.46/2.40  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 5.46/2.40  tff(f_31, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 5.46/2.40  tff(f_27, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_xboole_1)).
% 5.46/2.40  tff(c_20, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.46/2.40  tff(c_6, plain, (![A_6, B_7]: (m1_subset_1(k3_subset_1(A_6, B_7), k1_zfmisc_1(A_6)) | ~m1_subset_1(B_7, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.46/2.40  tff(c_137, plain, (![A_35, B_36, C_37]: (k4_subset_1(A_35, B_36, C_37)=k2_xboole_0(B_36, C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(A_35)) | ~m1_subset_1(B_36, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.46/2.40  tff(c_179, plain, (![B_40]: (k4_subset_1('#skF_1', B_40, '#skF_2')=k2_xboole_0(B_40, '#skF_2') | ~m1_subset_1(B_40, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_20, c_137])).
% 5.46/2.40  tff(c_962, plain, (![B_63]: (k4_subset_1('#skF_1', k3_subset_1('#skF_1', B_63), '#skF_2')=k2_xboole_0(k3_subset_1('#skF_1', B_63), '#skF_2') | ~m1_subset_1(B_63, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_6, c_179])).
% 5.46/2.40  tff(c_1028, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2')), inference(resolution, [status(thm)], [c_20, c_962])).
% 5.46/2.40  tff(c_8, plain, (![A_8, B_9, C_10]: (m1_subset_1(k4_subset_1(A_8, B_9, C_10), k1_zfmisc_1(A_8)) | ~m1_subset_1(C_10, k1_zfmisc_1(A_8)) | ~m1_subset_1(B_9, k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.46/2.40  tff(c_1041, plain, (m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1028, c_8])).
% 5.46/2.40  tff(c_1045, plain, (m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_20, c_1041])).
% 5.46/2.40  tff(c_1149, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_1045])).
% 5.46/2.40  tff(c_1152, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_6, c_1149])).
% 5.46/2.40  tff(c_1156, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_1152])).
% 5.46/2.40  tff(c_1158, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_1045])).
% 5.46/2.40  tff(c_18, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.46/2.40  tff(c_145, plain, (![B_36]: (k4_subset_1('#skF_1', B_36, '#skF_3')=k2_xboole_0(B_36, '#skF_3') | ~m1_subset_1(B_36, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_18, c_137])).
% 5.46/2.40  tff(c_1264, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_1158, c_145])).
% 5.46/2.40  tff(c_118, plain, (![A_31, B_32, C_33]: (k7_subset_1(A_31, B_32, C_33)=k4_xboole_0(B_32, C_33) | ~m1_subset_1(B_32, k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 5.46/2.40  tff(c_127, plain, (![C_33]: (k7_subset_1('#skF_1', '#skF_2', C_33)=k4_xboole_0('#skF_2', C_33))), inference(resolution, [status(thm)], [c_20, c_118])).
% 5.46/2.40  tff(c_16, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k3_subset_1('#skF_1', k7_subset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_63])).
% 5.46/2.40  tff(c_147, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k3_subset_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_16])).
% 5.46/2.40  tff(c_1507, plain, (k3_subset_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))!=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1264, c_147])).
% 5.46/2.40  tff(c_66, plain, (![A_27, B_28]: (k3_subset_1(A_27, k3_subset_1(A_27, B_28))=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.46/2.40  tff(c_75, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_20, c_66])).
% 5.46/2.40  tff(c_22, plain, (![A_22, B_23]: (k4_xboole_0(A_22, B_23)=k3_subset_1(A_22, B_23) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.46/2.40  tff(c_201, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_subset_1(A_41, B_42))=k3_subset_1(A_41, k3_subset_1(A_41, B_42)) | ~m1_subset_1(B_42, k1_zfmisc_1(A_41)))), inference(resolution, [status(thm)], [c_6, c_22])).
% 5.46/2.40  tff(c_207, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_20, c_201])).
% 5.46/2.40  tff(c_212, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_75, c_207])).
% 5.46/2.40  tff(c_2, plain, (![A_1, B_2, C_3]: (k4_xboole_0(k4_xboole_0(A_1, B_2), C_3)=k4_xboole_0(A_1, k2_xboole_0(B_2, C_3)))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.46/2.40  tff(c_270, plain, (![C_3]: (k4_xboole_0('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_3))=k4_xboole_0('#skF_2', C_3))), inference(superposition, [status(thm), theory('equality')], [c_212, c_2])).
% 5.46/2.40  tff(c_1511, plain, (m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_8])).
% 5.46/2.40  tff(c_1515, plain, (m1_subset_1(k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_1158, c_18, c_1511])).
% 5.46/2.40  tff(c_4, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k3_subset_1(A_4, B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.46/2.40  tff(c_1545, plain, (k4_xboole_0('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3'))=k3_subset_1('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3'))), inference(resolution, [status(thm)], [c_1515, c_4])).
% 5.46/2.40  tff(c_1558, plain, (k3_subset_1('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_270, c_1545])).
% 5.46/2.40  tff(c_213, plain, (![A_43, B_44, C_45]: (m1_subset_1(k4_subset_1(A_43, B_44, C_45), k1_zfmisc_1(A_43)) | ~m1_subset_1(C_45, k1_zfmisc_1(A_43)) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 5.46/2.40  tff(c_10, plain, (![A_11, B_12]: (k3_subset_1(A_11, k3_subset_1(A_11, B_12))=B_12 | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.46/2.40  tff(c_1573, plain, (![A_75, B_76, C_77]: (k3_subset_1(A_75, k3_subset_1(A_75, k4_subset_1(A_75, B_76, C_77)))=k4_subset_1(A_75, B_76, C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(A_75)) | ~m1_subset_1(B_76, k1_zfmisc_1(A_75)))), inference(resolution, [status(thm)], [c_213, c_10])).
% 5.46/2.40  tff(c_1591, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')))=k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3') | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_1264, c_1573])).
% 5.46/2.40  tff(c_1645, plain, (k3_subset_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1158, c_18, c_1558, c_1264, c_1591])).
% 5.46/2.40  tff(c_1647, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1507, c_1645])).
% 5.46/2.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.46/2.40  
% 5.46/2.40  Inference rules
% 5.46/2.40  ----------------------
% 5.46/2.40  #Ref     : 0
% 5.46/2.40  #Sup     : 457
% 5.46/2.40  #Fact    : 0
% 5.46/2.40  #Define  : 0
% 5.46/2.40  #Split   : 1
% 5.46/2.40  #Chain   : 0
% 5.46/2.40  #Close   : 0
% 5.46/2.40  
% 5.46/2.40  Ordering : KBO
% 5.46/2.40  
% 5.46/2.40  Simplification rules
% 5.46/2.40  ----------------------
% 5.46/2.40  #Subsume      : 2
% 5.46/2.40  #Demod        : 134
% 5.46/2.40  #Tautology    : 151
% 5.46/2.40  #SimpNegUnit  : 1
% 5.46/2.40  #BackRed      : 2
% 5.46/2.40  
% 5.46/2.40  #Partial instantiations: 0
% 5.46/2.40  #Strategies tried      : 1
% 5.46/2.40  
% 5.46/2.40  Timing (in seconds)
% 5.46/2.40  ----------------------
% 5.46/2.41  Preprocessing        : 0.45
% 5.46/2.41  Parsing              : 0.24
% 5.46/2.41  CNF conversion       : 0.03
% 5.46/2.41  Main loop            : 1.03
% 5.46/2.41  Inferencing          : 0.33
% 5.46/2.41  Reduction            : 0.35
% 5.46/2.41  Demodulation         : 0.26
% 5.46/2.41  BG Simplification    : 0.05
% 5.46/2.41  Subsumption          : 0.21
% 5.46/2.41  Abstraction          : 0.06
% 5.53/2.41  MUC search           : 0.00
% 5.53/2.41  Cooper               : 0.00
% 5.53/2.41  Total                : 1.53
% 5.53/2.41  Index Insertion      : 0.00
% 5.53/2.41  Index Deletion       : 0.00
% 5.53/2.41  Index Matching       : 0.00
% 5.53/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
