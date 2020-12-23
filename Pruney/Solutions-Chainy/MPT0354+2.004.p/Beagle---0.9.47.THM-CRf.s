%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:55 EST 2020

% Result     : Theorem 4.58s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 113 expanded)
%              Number of leaves         :   25 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   74 ( 165 expanded)
%              Number of equality atoms :   38 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

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
           => k3_subset_1(A,k7_subset_1(A,B,C)) = k4_subset_1(A,k3_subset_1(A,B),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k7_subset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(A,k4_xboole_0(B,C)) = k2_xboole_0(k4_xboole_0(A,B),k3_xboole_0(A,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_24,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_107,plain,(
    ! [A_36,B_37] :
      ( k4_xboole_0(A_36,B_37) = k3_subset_1(A_36,B_37)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_36)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_118,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_24,c_107])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_123,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_4])).

tff(c_81,plain,(
    ! [A_34,B_35] :
      ( k3_subset_1(A_34,k3_subset_1(A_34,B_35)) = B_35
      | ~ m1_subset_1(B_35,k1_zfmisc_1(A_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_89,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_24,c_81])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( m1_subset_1(k3_subset_1(A_12,B_13),k1_zfmisc_1(A_12))
      | ~ m1_subset_1(B_13,k1_zfmisc_1(A_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1505,plain,(
    ! [A_111,B_112] :
      ( k4_xboole_0(A_111,k3_subset_1(A_111,B_112)) = k3_subset_1(A_111,k3_subset_1(A_111,B_112))
      | ~ m1_subset_1(B_112,k1_zfmisc_1(A_111)) ) ),
    inference(resolution,[status(thm)],[c_12,c_107])).

tff(c_1535,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_3')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_1505])).

tff(c_1557,plain,(
    k3_xboole_0('#skF_1','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_123,c_89,c_1535])).

tff(c_26,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_199,plain,(
    ! [A_43,B_44,C_45] :
      ( k7_subset_1(A_43,B_44,C_45) = k4_xboole_0(B_44,C_45)
      | ~ m1_subset_1(B_44,k1_zfmisc_1(A_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_257,plain,(
    ! [C_49] : k7_subset_1('#skF_1','#skF_2',C_49) = k4_xboole_0('#skF_2',C_49) ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_14,plain,(
    ! [A_14,B_15,C_16] :
      ( m1_subset_1(k7_subset_1(A_14,B_15,C_16),k1_zfmisc_1(A_14))
      | ~ m1_subset_1(B_15,k1_zfmisc_1(A_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_263,plain,(
    ! [C_49] :
      ( m1_subset_1(k4_xboole_0('#skF_2',C_49),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_257,c_14])).

tff(c_316,plain,(
    ! [C_53] : m1_subset_1(k4_xboole_0('#skF_2',C_53),k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_263])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = k3_subset_1(A_10,B_11)
      | ~ m1_subset_1(B_11,k1_zfmisc_1(A_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_333,plain,(
    ! [C_53] : k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_53)) = k3_subset_1('#skF_1',k4_xboole_0('#skF_2',C_53)) ),
    inference(resolution,[status(thm)],[c_316,c_10])).

tff(c_119,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_107])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_271,plain,(
    ! [A_50,B_51,C_52] : k2_xboole_0(k4_xboole_0(A_50,B_51),k3_xboole_0(A_50,C_52)) = k4_xboole_0(A_50,k4_xboole_0(B_51,C_52)) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_710,plain,(
    ! [A_73,C_74,B_75] : k2_xboole_0(k3_xboole_0(A_73,C_74),k4_xboole_0(A_73,B_75)) = k4_xboole_0(A_73,k4_xboole_0(B_75,C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_271])).

tff(c_752,plain,(
    ! [C_74] : k2_xboole_0(k3_xboole_0('#skF_1',C_74),k3_subset_1('#skF_1','#skF_2')) = k4_xboole_0('#skF_1',k4_xboole_0('#skF_2',C_74)) ),
    inference(superposition,[status(thm),theory(equality)],[c_119,c_710])).

tff(c_769,plain,(
    ! [C_74] : k2_xboole_0(k3_xboole_0('#skF_1',C_74),k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k4_xboole_0('#skF_2',C_74)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_333,c_752])).

tff(c_1570,plain,(
    k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1557,c_769])).

tff(c_211,plain,(
    ! [C_45] : k7_subset_1('#skF_1','#skF_2',C_45) = k4_xboole_0('#skF_2',C_45) ),
    inference(resolution,[status(thm)],[c_26,c_199])).

tff(c_22,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k7_subset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_256,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k3_subset_1('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_211,c_22])).

tff(c_2527,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') != k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1570,c_256])).

tff(c_2387,plain,(
    ! [A_128,B_129,C_130] :
      ( k7_subset_1(A_128,k3_subset_1(A_128,B_129),C_130) = k4_xboole_0(k3_subset_1(A_128,B_129),C_130)
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(resolution,[status(thm)],[c_12,c_199])).

tff(c_2744,plain,(
    ! [C_137] : k7_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),C_137) = k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_137) ),
    inference(resolution,[status(thm)],[c_26,c_2387])).

tff(c_2753,plain,(
    ! [C_137] :
      ( m1_subset_1(k4_xboole_0(k3_subset_1('#skF_1','#skF_2'),C_137),k1_zfmisc_1('#skF_1'))
      | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2744,c_14])).

tff(c_3066,plain,(
    ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_2753])).

tff(c_3069,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_12,c_3066])).

tff(c_3073,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_3069])).

tff(c_3075,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_2753])).

tff(c_444,plain,(
    ! [A_59,B_60,C_61] :
      ( k4_subset_1(A_59,B_60,C_61) = k2_xboole_0(B_60,C_61)
      | ~ m1_subset_1(C_61,k1_zfmisc_1(A_59))
      | ~ m1_subset_1(B_60,k1_zfmisc_1(A_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_467,plain,(
    ! [B_60] :
      ( k4_subset_1('#skF_1',B_60,'#skF_3') = k2_xboole_0(B_60,'#skF_3')
      | ~ m1_subset_1(B_60,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_24,c_444])).

tff(c_3089,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k2_xboole_0(k3_subset_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_3075,c_467])).

tff(c_3110,plain,(
    k4_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2'),'#skF_3') = k2_xboole_0('#skF_3',k3_subset_1('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_3089])).

tff(c_3112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2527,c_3110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:59:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.58/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.91  
% 4.58/1.91  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.58/1.91  %$ m1_subset_1 > k7_subset_1 > k4_subset_1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_zfmisc_1 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > #skF_2 > #skF_3 > #skF_1
% 4.58/1.91  
% 4.58/1.91  %Foreground sorts:
% 4.58/1.91  
% 4.58/1.91  
% 4.58/1.91  %Background operators:
% 4.58/1.91  
% 4.58/1.91  
% 4.58/1.91  %Foreground operators:
% 4.58/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.58/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.58/1.91  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.58/1.91  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.58/1.91  tff('#skF_2', type, '#skF_2': $i).
% 4.58/1.91  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 4.58/1.91  tff('#skF_3', type, '#skF_3': $i).
% 4.58/1.91  tff('#skF_1', type, '#skF_1': $i).
% 4.58/1.91  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.58/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.58/1.91  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.58/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.58/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.58/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.58/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.58/1.91  
% 4.97/1.92  tff(f_69, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k3_subset_1(A, k7_subset_1(A, B, C)) = k4_subset_1(A, k3_subset_1(A, B), C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_subset_1)).
% 4.97/1.92  tff(f_39, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 4.97/1.92  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.97/1.92  tff(f_51, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 4.97/1.92  tff(f_43, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.97/1.92  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 4.97/1.92  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k7_subset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_subset_1)).
% 4.97/1.92  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 4.97/1.92  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(A, k4_xboole_0(B, C)) = k2_xboole_0(k4_xboole_0(A, B), k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_xboole_1)).
% 4.97/1.92  tff(f_57, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.97/1.92  tff(c_24, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.97/1.92  tff(c_107, plain, (![A_36, B_37]: (k4_xboole_0(A_36, B_37)=k3_subset_1(A_36, B_37) | ~m1_subset_1(B_37, k1_zfmisc_1(A_36)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.97/1.92  tff(c_118, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_24, c_107])).
% 4.97/1.92  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.97/1.92  tff(c_123, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_118, c_4])).
% 4.97/1.92  tff(c_81, plain, (![A_34, B_35]: (k3_subset_1(A_34, k3_subset_1(A_34, B_35))=B_35 | ~m1_subset_1(B_35, k1_zfmisc_1(A_34)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.97/1.92  tff(c_89, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_24, c_81])).
% 4.97/1.92  tff(c_12, plain, (![A_12, B_13]: (m1_subset_1(k3_subset_1(A_12, B_13), k1_zfmisc_1(A_12)) | ~m1_subset_1(B_13, k1_zfmisc_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.97/1.92  tff(c_1505, plain, (![A_111, B_112]: (k4_xboole_0(A_111, k3_subset_1(A_111, B_112))=k3_subset_1(A_111, k3_subset_1(A_111, B_112)) | ~m1_subset_1(B_112, k1_zfmisc_1(A_111)))), inference(resolution, [status(thm)], [c_12, c_107])).
% 4.97/1.92  tff(c_1535, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_3'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_24, c_1505])).
% 4.97/1.92  tff(c_1557, plain, (k3_xboole_0('#skF_1', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_123, c_89, c_1535])).
% 4.97/1.92  tff(c_26, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.97/1.92  tff(c_199, plain, (![A_43, B_44, C_45]: (k7_subset_1(A_43, B_44, C_45)=k4_xboole_0(B_44, C_45) | ~m1_subset_1(B_44, k1_zfmisc_1(A_43)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.97/1.92  tff(c_257, plain, (![C_49]: (k7_subset_1('#skF_1', '#skF_2', C_49)=k4_xboole_0('#skF_2', C_49))), inference(resolution, [status(thm)], [c_26, c_199])).
% 4.97/1.92  tff(c_14, plain, (![A_14, B_15, C_16]: (m1_subset_1(k7_subset_1(A_14, B_15, C_16), k1_zfmisc_1(A_14)) | ~m1_subset_1(B_15, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.97/1.92  tff(c_263, plain, (![C_49]: (m1_subset_1(k4_xboole_0('#skF_2', C_49), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_257, c_14])).
% 4.97/1.92  tff(c_316, plain, (![C_53]: (m1_subset_1(k4_xboole_0('#skF_2', C_53), k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_263])).
% 4.97/1.92  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=k3_subset_1(A_10, B_11) | ~m1_subset_1(B_11, k1_zfmisc_1(A_10)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.97/1.92  tff(c_333, plain, (![C_53]: (k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_53))=k3_subset_1('#skF_1', k4_xboole_0('#skF_2', C_53)))), inference(resolution, [status(thm)], [c_316, c_10])).
% 4.97/1.92  tff(c_119, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_26, c_107])).
% 4.97/1.92  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.97/1.92  tff(c_271, plain, (![A_50, B_51, C_52]: (k2_xboole_0(k4_xboole_0(A_50, B_51), k3_xboole_0(A_50, C_52))=k4_xboole_0(A_50, k4_xboole_0(B_51, C_52)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.97/1.92  tff(c_710, plain, (![A_73, C_74, B_75]: (k2_xboole_0(k3_xboole_0(A_73, C_74), k4_xboole_0(A_73, B_75))=k4_xboole_0(A_73, k4_xboole_0(B_75, C_74)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_271])).
% 4.97/1.92  tff(c_752, plain, (![C_74]: (k2_xboole_0(k3_xboole_0('#skF_1', C_74), k3_subset_1('#skF_1', '#skF_2'))=k4_xboole_0('#skF_1', k4_xboole_0('#skF_2', C_74)))), inference(superposition, [status(thm), theory('equality')], [c_119, c_710])).
% 4.97/1.92  tff(c_769, plain, (![C_74]: (k2_xboole_0(k3_xboole_0('#skF_1', C_74), k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k4_xboole_0('#skF_2', C_74)))), inference(demodulation, [status(thm), theory('equality')], [c_333, c_752])).
% 4.97/1.92  tff(c_1570, plain, (k3_subset_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1557, c_769])).
% 4.97/1.92  tff(c_211, plain, (![C_45]: (k7_subset_1('#skF_1', '#skF_2', C_45)=k4_xboole_0('#skF_2', C_45))), inference(resolution, [status(thm)], [c_26, c_199])).
% 4.97/1.92  tff(c_22, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k3_subset_1('#skF_1', k7_subset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.97/1.92  tff(c_256, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k3_subset_1('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_211, c_22])).
% 4.97/1.92  tff(c_2527, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')!=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_1570, c_256])).
% 4.97/1.92  tff(c_2387, plain, (![A_128, B_129, C_130]: (k7_subset_1(A_128, k3_subset_1(A_128, B_129), C_130)=k4_xboole_0(k3_subset_1(A_128, B_129), C_130) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(resolution, [status(thm)], [c_12, c_199])).
% 4.97/1.92  tff(c_2744, plain, (![C_137]: (k7_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), C_137)=k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_137))), inference(resolution, [status(thm)], [c_26, c_2387])).
% 4.97/1.92  tff(c_2753, plain, (![C_137]: (m1_subset_1(k4_xboole_0(k3_subset_1('#skF_1', '#skF_2'), C_137), k1_zfmisc_1('#skF_1')) | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_2744, c_14])).
% 4.97/1.92  tff(c_3066, plain, (~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_2753])).
% 4.97/1.92  tff(c_3069, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(resolution, [status(thm)], [c_12, c_3066])).
% 4.97/1.92  tff(c_3073, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_3069])).
% 4.97/1.92  tff(c_3075, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_2753])).
% 4.97/1.92  tff(c_444, plain, (![A_59, B_60, C_61]: (k4_subset_1(A_59, B_60, C_61)=k2_xboole_0(B_60, C_61) | ~m1_subset_1(C_61, k1_zfmisc_1(A_59)) | ~m1_subset_1(B_60, k1_zfmisc_1(A_59)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.97/1.92  tff(c_467, plain, (![B_60]: (k4_subset_1('#skF_1', B_60, '#skF_3')=k2_xboole_0(B_60, '#skF_3') | ~m1_subset_1(B_60, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_24, c_444])).
% 4.97/1.92  tff(c_3089, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')=k2_xboole_0(k3_subset_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_3075, c_467])).
% 4.97/1.92  tff(c_3110, plain, (k4_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'), '#skF_3')=k2_xboole_0('#skF_3', k3_subset_1('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_3089])).
% 4.97/1.92  tff(c_3112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2527, c_3110])).
% 4.97/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.92  
% 4.97/1.92  Inference rules
% 4.97/1.92  ----------------------
% 4.97/1.92  #Ref     : 1
% 4.97/1.92  #Sup     : 795
% 4.97/1.92  #Fact    : 0
% 4.97/1.92  #Define  : 0
% 4.97/1.92  #Split   : 1
% 4.97/1.92  #Chain   : 0
% 4.97/1.92  #Close   : 0
% 4.97/1.92  
% 4.97/1.92  Ordering : KBO
% 4.97/1.92  
% 4.97/1.92  Simplification rules
% 4.97/1.92  ----------------------
% 4.97/1.92  #Subsume      : 6
% 4.97/1.92  #Demod        : 453
% 4.97/1.92  #Tautology    : 294
% 4.97/1.92  #SimpNegUnit  : 1
% 4.97/1.92  #BackRed      : 10
% 4.97/1.92  
% 4.97/1.92  #Partial instantiations: 0
% 4.97/1.92  #Strategies tried      : 1
% 4.97/1.92  
% 4.97/1.92  Timing (in seconds)
% 4.97/1.92  ----------------------
% 4.97/1.93  Preprocessing        : 0.29
% 4.97/1.93  Parsing              : 0.16
% 4.97/1.93  CNF conversion       : 0.02
% 4.97/1.93  Main loop            : 0.86
% 4.97/1.93  Inferencing          : 0.27
% 4.97/1.93  Reduction            : 0.35
% 4.97/1.93  Demodulation         : 0.29
% 4.97/1.93  BG Simplification    : 0.04
% 4.97/1.93  Subsumption          : 0.14
% 4.97/1.93  Abstraction          : 0.05
% 4.97/1.93  MUC search           : 0.00
% 4.97/1.93  Cooper               : 0.00
% 4.97/1.93  Total                : 1.19
% 4.97/1.93  Index Insertion      : 0.00
% 4.97/1.93  Index Deletion       : 0.00
% 4.97/1.93  Index Matching       : 0.00
% 4.97/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------
