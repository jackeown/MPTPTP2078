%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:49 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   62 (  95 expanded)
%              Number of leaves         :   21 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 155 expanded)
%              Number of equality atoms :   17 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(B,C)
            <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(c_26,plain,
    ( r1_tarski('#skF_2','#skF_3')
    | r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_93,plain,(
    r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_20,plain,
    ( ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2'))
    | ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_94,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_16,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [A_25,B_26] :
      ( k4_xboole_0(A_25,B_26) = k3_subset_1(A_25,B_26)
      | ~ m1_subset_1(B_26,k1_zfmisc_1(A_25)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_77,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_16,c_70])).

tff(c_8,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski(A_8,k2_xboole_0(B_9,C_10))
      | ~ r1_tarski(k4_xboole_0(A_8,B_9),C_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [C_34] :
      ( r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_34))
      | ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_8])).

tff(c_141,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_93,c_137])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    ! [A_27,B_28] :
      ( k3_subset_1(A_27,k3_subset_1(A_27,B_28)) = B_28
      | ~ m1_subset_1(B_28,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_95])).

tff(c_110,plain,(
    ! [A_29,B_30] :
      ( m1_subset_1(k3_subset_1(A_29,B_30),k1_zfmisc_1(A_29))
      | ~ m1_subset_1(B_30,k1_zfmisc_1(A_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_11,B_12] :
      ( k4_xboole_0(A_11,B_12) = k3_subset_1(A_11,B_12)
      | ~ m1_subset_1(B_12,k1_zfmisc_1(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_153,plain,(
    ! [A_38,B_39] :
      ( k4_xboole_0(A_38,k3_subset_1(A_38,B_39)) = k3_subset_1(A_38,k3_subset_1(A_38,B_39))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(resolution,[status(thm)],[c_110,c_10])).

tff(c_159,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_153])).

tff(c_164,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_101,c_159])).

tff(c_6,plain,(
    ! [A_5,B_6,C_7] :
      ( r1_tarski(k4_xboole_0(A_5,B_6),C_7)
      | ~ r1_tarski(A_5,k2_xboole_0(B_6,C_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_255,plain,(
    ! [C_44] :
      ( r1_tarski('#skF_2',C_44)
      | ~ r1_tarski('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_44)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_164,c_6])).

tff(c_377,plain,(
    ! [A_51] :
      ( r1_tarski('#skF_2',A_51)
      | ~ r1_tarski('#skF_1',k2_xboole_0(A_51,k3_subset_1('#skF_1','#skF_2'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_255])).

tff(c_391,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_141,c_377])).

tff(c_406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_391])).

tff(c_407,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_410,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_407])).

tff(c_411,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_431,plain,(
    ! [A_57,B_58] :
      ( k3_subset_1(A_57,k3_subset_1(A_57,B_58)) = B_58
      | ~ m1_subset_1(B_58,k1_zfmisc_1(A_57)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_440,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_18,c_431])).

tff(c_426,plain,(
    ! [A_55,B_56] :
      ( m1_subset_1(k3_subset_1(A_55,B_56),k1_zfmisc_1(A_55))
      | ~ m1_subset_1(B_56,k1_zfmisc_1(A_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_521,plain,(
    ! [A_65,B_66] :
      ( k4_xboole_0(A_65,k3_subset_1(A_65,B_66)) = k3_subset_1(A_65,k3_subset_1(A_65,B_66))
      | ~ m1_subset_1(B_66,k1_zfmisc_1(A_65)) ) ),
    inference(resolution,[status(thm)],[c_426,c_10])).

tff(c_527,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_18,c_521])).

tff(c_532,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_440,c_527])).

tff(c_562,plain,(
    ! [C_68] :
      ( r1_tarski('#skF_1',k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_68))
      | ~ r1_tarski('#skF_2',C_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_532,c_8])).

tff(c_697,plain,(
    ! [B_76] :
      ( r1_tarski('#skF_1',k2_xboole_0(B_76,k3_subset_1('#skF_1','#skF_2')))
      | ~ r1_tarski('#skF_2',B_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_562])).

tff(c_413,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k4_xboole_0(A_52,B_53),C_54)
      | ~ r1_tarski(A_52,k2_xboole_0(B_53,C_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_464,plain,(
    ! [C_62] :
      ( r1_tarski(k3_subset_1('#skF_1','#skF_3'),C_62)
      | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',C_62)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_77,c_413])).

tff(c_412,plain,(
    ~ r1_tarski(k3_subset_1('#skF_1','#skF_3'),k3_subset_1('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_472,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_464,c_412])).

tff(c_711,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_697,c_472])).

tff(c_726,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_411,c_711])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:14:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.40  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  
% 2.62/1.40  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.40  %$ r1_tarski > m1_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 2.62/1.40  
% 2.62/1.40  %Foreground sorts:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Background operators:
% 2.62/1.40  
% 2.62/1.40  
% 2.62/1.40  %Foreground operators:
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.40  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.62/1.40  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.62/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.40  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.62/1.40  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.40  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.40  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.40  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.40  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.62/1.40  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.62/1.40  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.40  
% 2.62/1.42  tff(f_59, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 2.62/1.42  tff(f_41, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.62/1.42  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 2.62/1.42  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.62/1.42  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.62/1.42  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.62/1.42  tff(f_33, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.62/1.42  tff(c_26, plain, (r1_tarski('#skF_2', '#skF_3') | r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.42  tff(c_93, plain, (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_26])).
% 2.62/1.42  tff(c_20, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2')) | ~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.42  tff(c_94, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 2.62/1.42  tff(c_16, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.42  tff(c_70, plain, (![A_25, B_26]: (k4_xboole_0(A_25, B_26)=k3_subset_1(A_25, B_26) | ~m1_subset_1(B_26, k1_zfmisc_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.42  tff(c_77, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_16, c_70])).
% 2.62/1.42  tff(c_8, plain, (![A_8, B_9, C_10]: (r1_tarski(A_8, k2_xboole_0(B_9, C_10)) | ~r1_tarski(k4_xboole_0(A_8, B_9), C_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.62/1.42  tff(c_137, plain, (![C_34]: (r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_34)) | ~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_34))), inference(superposition, [status(thm), theory('equality')], [c_77, c_8])).
% 2.62/1.42  tff(c_141, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_93, c_137])).
% 2.62/1.42  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.62/1.42  tff(c_18, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.62/1.42  tff(c_95, plain, (![A_27, B_28]: (k3_subset_1(A_27, k3_subset_1(A_27, B_28))=B_28 | ~m1_subset_1(B_28, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.42  tff(c_101, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_95])).
% 2.62/1.42  tff(c_110, plain, (![A_29, B_30]: (m1_subset_1(k3_subset_1(A_29, B_30), k1_zfmisc_1(A_29)) | ~m1_subset_1(B_30, k1_zfmisc_1(A_29)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.42  tff(c_10, plain, (![A_11, B_12]: (k4_xboole_0(A_11, B_12)=k3_subset_1(A_11, B_12) | ~m1_subset_1(B_12, k1_zfmisc_1(A_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.62/1.42  tff(c_153, plain, (![A_38, B_39]: (k4_xboole_0(A_38, k3_subset_1(A_38, B_39))=k3_subset_1(A_38, k3_subset_1(A_38, B_39)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(resolution, [status(thm)], [c_110, c_10])).
% 2.62/1.42  tff(c_159, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_153])).
% 2.62/1.42  tff(c_164, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_101, c_159])).
% 2.62/1.42  tff(c_6, plain, (![A_5, B_6, C_7]: (r1_tarski(k4_xboole_0(A_5, B_6), C_7) | ~r1_tarski(A_5, k2_xboole_0(B_6, C_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.42  tff(c_255, plain, (![C_44]: (r1_tarski('#skF_2', C_44) | ~r1_tarski('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_44)))), inference(superposition, [status(thm), theory('equality')], [c_164, c_6])).
% 2.62/1.42  tff(c_377, plain, (![A_51]: (r1_tarski('#skF_2', A_51) | ~r1_tarski('#skF_1', k2_xboole_0(A_51, k3_subset_1('#skF_1', '#skF_2'))))), inference(superposition, [status(thm), theory('equality')], [c_2, c_255])).
% 2.62/1.42  tff(c_391, plain, (r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_141, c_377])).
% 2.62/1.42  tff(c_406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_391])).
% 2.62/1.42  tff(c_407, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_20])).
% 2.62/1.42  tff(c_410, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_93, c_407])).
% 2.62/1.42  tff(c_411, plain, (r1_tarski('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.62/1.42  tff(c_431, plain, (![A_57, B_58]: (k3_subset_1(A_57, k3_subset_1(A_57, B_58))=B_58 | ~m1_subset_1(B_58, k1_zfmisc_1(A_57)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.42  tff(c_440, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_18, c_431])).
% 2.62/1.42  tff(c_426, plain, (![A_55, B_56]: (m1_subset_1(k3_subset_1(A_55, B_56), k1_zfmisc_1(A_55)) | ~m1_subset_1(B_56, k1_zfmisc_1(A_55)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.42  tff(c_521, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k3_subset_1(A_65, B_66))=k3_subset_1(A_65, k3_subset_1(A_65, B_66)) | ~m1_subset_1(B_66, k1_zfmisc_1(A_65)))), inference(resolution, [status(thm)], [c_426, c_10])).
% 2.62/1.42  tff(c_527, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_18, c_521])).
% 2.62/1.42  tff(c_532, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_440, c_527])).
% 2.62/1.42  tff(c_562, plain, (![C_68]: (r1_tarski('#skF_1', k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_68)) | ~r1_tarski('#skF_2', C_68))), inference(superposition, [status(thm), theory('equality')], [c_532, c_8])).
% 2.62/1.42  tff(c_697, plain, (![B_76]: (r1_tarski('#skF_1', k2_xboole_0(B_76, k3_subset_1('#skF_1', '#skF_2'))) | ~r1_tarski('#skF_2', B_76))), inference(superposition, [status(thm), theory('equality')], [c_2, c_562])).
% 2.62/1.42  tff(c_413, plain, (![A_52, B_53, C_54]: (r1_tarski(k4_xboole_0(A_52, B_53), C_54) | ~r1_tarski(A_52, k2_xboole_0(B_53, C_54)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.62/1.42  tff(c_464, plain, (![C_62]: (r1_tarski(k3_subset_1('#skF_1', '#skF_3'), C_62) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_3', C_62)))), inference(superposition, [status(thm), theory('equality')], [c_77, c_413])).
% 2.62/1.42  tff(c_412, plain, (~r1_tarski(k3_subset_1('#skF_1', '#skF_3'), k3_subset_1('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_26])).
% 2.62/1.42  tff(c_472, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_464, c_412])).
% 2.62/1.42  tff(c_711, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_697, c_472])).
% 2.62/1.42  tff(c_726, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_411, c_711])).
% 2.62/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.62/1.42  
% 2.62/1.42  Inference rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Ref     : 0
% 2.62/1.42  #Sup     : 172
% 2.62/1.42  #Fact    : 0
% 2.62/1.42  #Define  : 0
% 2.62/1.42  #Split   : 2
% 2.62/1.42  #Chain   : 0
% 2.62/1.42  #Close   : 0
% 2.62/1.42  
% 2.62/1.42  Ordering : KBO
% 2.62/1.42  
% 2.62/1.42  Simplification rules
% 2.62/1.42  ----------------------
% 2.62/1.42  #Subsume      : 18
% 2.62/1.42  #Demod        : 47
% 2.62/1.42  #Tautology    : 90
% 2.62/1.42  #SimpNegUnit  : 1
% 2.62/1.42  #BackRed      : 0
% 2.62/1.42  
% 2.62/1.42  #Partial instantiations: 0
% 2.62/1.42  #Strategies tried      : 1
% 2.62/1.42  
% 2.62/1.42  Timing (in seconds)
% 2.62/1.42  ----------------------
% 2.62/1.42  Preprocessing        : 0.29
% 2.62/1.42  Parsing              : 0.16
% 2.62/1.42  CNF conversion       : 0.02
% 2.62/1.42  Main loop            : 0.33
% 2.62/1.42  Inferencing          : 0.13
% 2.62/1.42  Reduction            : 0.10
% 2.62/1.42  Demodulation         : 0.07
% 2.62/1.42  BG Simplification    : 0.02
% 2.62/1.42  Subsumption          : 0.06
% 2.62/1.42  Abstraction          : 0.02
% 2.62/1.42  MUC search           : 0.00
% 2.62/1.42  Cooper               : 0.00
% 2.62/1.42  Total                : 0.66
% 2.62/1.42  Index Insertion      : 0.00
% 2.62/1.42  Index Deletion       : 0.00
% 2.62/1.42  Index Matching       : 0.00
% 2.62/1.42  BG Taut test         : 0.00
%------------------------------------------------------------------------------
