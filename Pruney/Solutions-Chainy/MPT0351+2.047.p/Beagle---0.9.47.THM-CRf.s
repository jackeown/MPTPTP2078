%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:43 EST 2020

% Result     : Theorem 2.79s
% Output     : CNFRefutation 2.79s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 211 expanded)
%              Number of leaves         :   27 (  84 expanded)
%              Depth                    :    9
%              Number of atoms          :   76 ( 305 expanded)
%              Number of equality atoms :   34 ( 115 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_76,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_53,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => m1_subset_1(k4_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_14,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_15] : m1_subset_1(k2_subset_1(A_15),k1_zfmisc_1(A_15)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_32,plain,(
    ! [A_15] : m1_subset_1(A_15,k1_zfmisc_1(A_15)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_18])).

tff(c_359,plain,(
    ! [A_56,B_57,C_58] :
      ( k4_subset_1(A_56,B_57,C_58) = k2_xboole_0(B_57,C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(A_56))
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_422,plain,(
    ! [A_62,B_63] :
      ( k4_subset_1(A_62,B_63,A_62) = k2_xboole_0(B_63,A_62)
      | ~ m1_subset_1(B_63,k1_zfmisc_1(A_62)) ) ),
    inference(resolution,[status(thm)],[c_32,c_359])).

tff(c_426,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_422])).

tff(c_434,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_426])).

tff(c_28,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_31,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_14,c_28])).

tff(c_570,plain,(
    k2_xboole_0('#skF_1','#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_31])).

tff(c_472,plain,(
    ! [B_65] :
      ( k4_subset_1('#skF_1',B_65,'#skF_2') = k2_xboole_0(B_65,'#skF_2')
      | ~ m1_subset_1(B_65,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_30,c_359])).

tff(c_493,plain,(
    k4_subset_1('#skF_1','#skF_1','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_472])).

tff(c_20,plain,(
    ! [A_16,B_17,C_18] :
      ( m1_subset_1(k4_subset_1(A_16,B_17,C_18),k1_zfmisc_1(A_16))
      | ~ m1_subset_1(C_18,k1_zfmisc_1(A_16))
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_506,plain,
    ( m1_subset_1(k2_xboole_0('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_493,c_20])).

tff(c_510,plain,(
    m1_subset_1(k2_xboole_0('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_506])).

tff(c_26,plain,(
    ! [A_24] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_24)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_93,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_98,plain,(
    ! [A_36] : k2_xboole_0(k1_xboole_0,A_36) = A_36 ),
    inference(resolution,[status(thm)],[c_6,c_93])).

tff(c_104,plain,(
    ! [A_36] : k2_xboole_0(A_36,k1_xboole_0) = A_36 ),
    inference(superposition,[status(thm),theory(equality)],[c_98,c_2])).

tff(c_365,plain,(
    ! [A_24,B_57] :
      ( k4_subset_1(A_24,B_57,k1_xboole_0) = k2_xboole_0(B_57,k1_xboole_0)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_24)) ) ),
    inference(resolution,[status(thm)],[c_26,c_359])).

tff(c_371,plain,(
    ! [A_24,B_57] :
      ( k4_subset_1(A_24,B_57,k1_xboole_0) = B_57
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_24)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_104,c_365])).

tff(c_531,plain,(
    k4_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2'),k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_510,c_371])).

tff(c_8,plain,(
    ! [A_6,B_7] : k4_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(A_13,B_14) = k3_subset_1(A_13,B_14)
      | ~ m1_subset_1(B_14,k1_zfmisc_1(A_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_526,plain,(
    k4_xboole_0('#skF_1',k2_xboole_0('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_510,c_16])).

tff(c_535,plain,(
    k3_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_526])).

tff(c_336,plain,(
    ! [A_53,B_54,C_55] :
      ( m1_subset_1(k4_subset_1(A_53,B_54,C_55),k1_zfmisc_1(A_53))
      | ~ m1_subset_1(C_55,k1_zfmisc_1(A_53))
      | ~ m1_subset_1(B_54,k1_zfmisc_1(A_53)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_24,plain,(
    ! [A_22,B_23] :
      ( k4_subset_1(A_22,B_23,k3_subset_1(A_22,B_23)) = k2_subset_1(A_22)
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_33,plain,(
    ! [A_22,B_23] :
      ( k4_subset_1(A_22,B_23,k3_subset_1(A_22,B_23)) = A_22
      | ~ m1_subset_1(B_23,k1_zfmisc_1(A_22)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_785,plain,(
    ! [A_74,B_75,C_76] :
      ( k4_subset_1(A_74,k4_subset_1(A_74,B_75,C_76),k3_subset_1(A_74,k4_subset_1(A_74,B_75,C_76))) = A_74
      | ~ m1_subset_1(C_76,k1_zfmisc_1(A_74))
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(resolution,[status(thm)],[c_336,c_33])).

tff(c_821,plain,
    ( k4_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2'),k3_subset_1('#skF_1',k4_subset_1('#skF_1',k2_xboole_0('#skF_1','#skF_2'),k1_xboole_0))) = '#skF_1'
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1(k2_xboole_0('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_531,c_785])).

tff(c_911,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_510,c_26,c_531,c_535,c_531,c_821])).

tff(c_913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_570,c_911])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 19:31:40 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.79/1.38  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.38  
% 2.79/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.39  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > k4_subset_1 > k4_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.79/1.39  
% 2.79/1.39  %Foreground sorts:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Background operators:
% 2.79/1.39  
% 2.79/1.39  
% 2.79/1.39  %Foreground operators:
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.79/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.79/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.79/1.39  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.79/1.39  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.79/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.79/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.79/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.79/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.79/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.79/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.79/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.79/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.79/1.39  
% 2.79/1.40  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.79/1.40  tff(f_76, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 2.79/1.40  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.79/1.40  tff(f_53, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.79/1.40  tff(f_65, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.79/1.40  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => m1_subset_1(k4_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_subset_1)).
% 2.79/1.40  tff(f_71, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.79/1.40  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.79/1.40  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.79/1.40  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.79/1.40  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.79/1.40  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 2.79/1.40  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.79/1.40  tff(c_30, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.79/1.40  tff(c_14, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.79/1.40  tff(c_18, plain, (![A_15]: (m1_subset_1(k2_subset_1(A_15), k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.79/1.40  tff(c_32, plain, (![A_15]: (m1_subset_1(A_15, k1_zfmisc_1(A_15)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_18])).
% 2.79/1.40  tff(c_359, plain, (![A_56, B_57, C_58]: (k4_subset_1(A_56, B_57, C_58)=k2_xboole_0(B_57, C_58) | ~m1_subset_1(C_58, k1_zfmisc_1(A_56)) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.79/1.40  tff(c_422, plain, (![A_62, B_63]: (k4_subset_1(A_62, B_63, A_62)=k2_xboole_0(B_63, A_62) | ~m1_subset_1(B_63, k1_zfmisc_1(A_62)))), inference(resolution, [status(thm)], [c_32, c_359])).
% 2.79/1.40  tff(c_426, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_30, c_422])).
% 2.79/1.40  tff(c_434, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_426])).
% 2.79/1.40  tff(c_28, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.79/1.40  tff(c_31, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_14, c_28])).
% 2.79/1.40  tff(c_570, plain, (k2_xboole_0('#skF_1', '#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_434, c_31])).
% 2.79/1.40  tff(c_472, plain, (![B_65]: (k4_subset_1('#skF_1', B_65, '#skF_2')=k2_xboole_0(B_65, '#skF_2') | ~m1_subset_1(B_65, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_30, c_359])).
% 2.79/1.40  tff(c_493, plain, (k4_subset_1('#skF_1', '#skF_1', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_472])).
% 2.79/1.40  tff(c_20, plain, (![A_16, B_17, C_18]: (m1_subset_1(k4_subset_1(A_16, B_17, C_18), k1_zfmisc_1(A_16)) | ~m1_subset_1(C_18, k1_zfmisc_1(A_16)) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.40  tff(c_506, plain, (m1_subset_1(k2_xboole_0('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_493, c_20])).
% 2.79/1.40  tff(c_510, plain, (m1_subset_1(k2_xboole_0('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_506])).
% 2.79/1.40  tff(c_26, plain, (![A_24]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_24)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.79/1.40  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.79/1.40  tff(c_93, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.79/1.40  tff(c_98, plain, (![A_36]: (k2_xboole_0(k1_xboole_0, A_36)=A_36)), inference(resolution, [status(thm)], [c_6, c_93])).
% 2.79/1.40  tff(c_104, plain, (![A_36]: (k2_xboole_0(A_36, k1_xboole_0)=A_36)), inference(superposition, [status(thm), theory('equality')], [c_98, c_2])).
% 2.79/1.40  tff(c_365, plain, (![A_24, B_57]: (k4_subset_1(A_24, B_57, k1_xboole_0)=k2_xboole_0(B_57, k1_xboole_0) | ~m1_subset_1(B_57, k1_zfmisc_1(A_24)))), inference(resolution, [status(thm)], [c_26, c_359])).
% 2.79/1.40  tff(c_371, plain, (![A_24, B_57]: (k4_subset_1(A_24, B_57, k1_xboole_0)=B_57 | ~m1_subset_1(B_57, k1_zfmisc_1(A_24)))), inference(demodulation, [status(thm), theory('equality')], [c_104, c_365])).
% 2.79/1.40  tff(c_531, plain, (k4_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_510, c_371])).
% 2.79/1.40  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(A_6, k2_xboole_0(A_6, B_7))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.79/1.40  tff(c_16, plain, (![A_13, B_14]: (k4_xboole_0(A_13, B_14)=k3_subset_1(A_13, B_14) | ~m1_subset_1(B_14, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.79/1.40  tff(c_526, plain, (k4_xboole_0('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_510, c_16])).
% 2.79/1.40  tff(c_535, plain, (k3_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_8, c_526])).
% 2.79/1.40  tff(c_336, plain, (![A_53, B_54, C_55]: (m1_subset_1(k4_subset_1(A_53, B_54, C_55), k1_zfmisc_1(A_53)) | ~m1_subset_1(C_55, k1_zfmisc_1(A_53)) | ~m1_subset_1(B_54, k1_zfmisc_1(A_53)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.79/1.40  tff(c_24, plain, (![A_22, B_23]: (k4_subset_1(A_22, B_23, k3_subset_1(A_22, B_23))=k2_subset_1(A_22) | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.79/1.40  tff(c_33, plain, (![A_22, B_23]: (k4_subset_1(A_22, B_23, k3_subset_1(A_22, B_23))=A_22 | ~m1_subset_1(B_23, k1_zfmisc_1(A_22)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 2.79/1.40  tff(c_785, plain, (![A_74, B_75, C_76]: (k4_subset_1(A_74, k4_subset_1(A_74, B_75, C_76), k3_subset_1(A_74, k4_subset_1(A_74, B_75, C_76)))=A_74 | ~m1_subset_1(C_76, k1_zfmisc_1(A_74)) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(resolution, [status(thm)], [c_336, c_33])).
% 2.79/1.40  tff(c_821, plain, (k4_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2'), k3_subset_1('#skF_1', k4_subset_1('#skF_1', k2_xboole_0('#skF_1', '#skF_2'), k1_xboole_0)))='#skF_1' | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k2_xboole_0('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_531, c_785])).
% 2.79/1.40  tff(c_911, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_510, c_26, c_531, c_535, c_531, c_821])).
% 2.79/1.40  tff(c_913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_570, c_911])).
% 2.79/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.79/1.40  
% 2.79/1.40  Inference rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Ref     : 0
% 2.79/1.40  #Sup     : 223
% 2.79/1.40  #Fact    : 0
% 2.79/1.40  #Define  : 0
% 2.79/1.40  #Split   : 0
% 2.79/1.40  #Chain   : 0
% 2.79/1.40  #Close   : 0
% 2.79/1.40  
% 2.79/1.40  Ordering : KBO
% 2.79/1.40  
% 2.79/1.40  Simplification rules
% 2.79/1.40  ----------------------
% 2.79/1.40  #Subsume      : 8
% 2.79/1.40  #Demod        : 130
% 2.79/1.40  #Tautology    : 120
% 2.79/1.40  #SimpNegUnit  : 1
% 2.79/1.40  #BackRed      : 1
% 2.79/1.40  
% 2.79/1.40  #Partial instantiations: 0
% 2.79/1.40  #Strategies tried      : 1
% 2.79/1.40  
% 2.79/1.40  Timing (in seconds)
% 2.79/1.40  ----------------------
% 2.79/1.40  Preprocessing        : 0.29
% 2.79/1.40  Parsing              : 0.16
% 2.79/1.40  CNF conversion       : 0.02
% 2.79/1.40  Main loop            : 0.36
% 2.79/1.40  Inferencing          : 0.13
% 2.79/1.40  Reduction            : 0.13
% 2.79/1.40  Demodulation         : 0.10
% 2.79/1.40  BG Simplification    : 0.02
% 2.79/1.40  Subsumption          : 0.06
% 2.79/1.40  Abstraction          : 0.02
% 2.79/1.40  MUC search           : 0.00
% 2.79/1.41  Cooper               : 0.00
% 2.79/1.41  Total                : 0.68
% 2.79/1.41  Index Insertion      : 0.00
% 2.79/1.41  Index Deletion       : 0.00
% 2.79/1.41  Index Matching       : 0.00
% 2.79/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
