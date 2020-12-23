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
% DateTime   : Thu Dec  3 09:55:53 EST 2020

% Result     : Theorem 3.98s
% Output     : CNFRefutation 3.98s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 144 expanded)
%              Number of leaves         :   36 (  62 expanded)
%              Depth                    :   12
%              Number of atoms          :   89 ( 183 expanded)
%              Number of equality atoms :   45 (  85 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k7_subset_1,type,(
    k7_subset_1: ( $i * $i * $i ) > $i )).

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

tff(k9_subset_1,type,(
    k9_subset_1: ( $i * $i * $i ) > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_86,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => k7_subset_1(A,B,C) = k9_subset_1(A,B,k3_subset_1(A,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(f_51,axiom,(
    ! [A,B] : m1_subset_1(k6_subset_1(A,B),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_subset_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(A))
     => k9_subset_1(A,B,C) = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k7_subset_1(A,B,C) = k4_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_43,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_67,axiom,(
    ! [A] : k2_subset_1(A) = k3_subset_1(A,k1_subset_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

tff(f_76,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(A))
         => ( r1_tarski(B,C)
          <=> r1_tarski(k3_subset_1(A,C),k3_subset_1(A,B)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_subset_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(c_42,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_234,plain,(
    ! [A_56,B_57] :
      ( k4_xboole_0(A_56,B_57) = k3_subset_1(A_56,B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_255,plain,(
    k4_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_42,c_234])).

tff(c_26,plain,(
    ! [A_22,B_23] : k6_subset_1(A_22,B_23) = k4_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_18,B_19] : m1_subset_1(k6_subset_1(A_18,B_19),k1_zfmisc_1(A_18)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_45,plain,(
    ! [A_18,B_19] : m1_subset_1(k4_xboole_0(A_18,B_19),k1_zfmisc_1(A_18)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_22])).

tff(c_295,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_45])).

tff(c_30,plain,(
    ! [A_27,B_28,C_29] :
      ( k9_subset_1(A_27,B_28,C_29) = k3_xboole_0(B_28,C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(A_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_463,plain,(
    ! [B_28] : k9_subset_1('#skF_1',B_28,k3_subset_1('#skF_1','#skF_3')) = k3_xboole_0(B_28,k3_subset_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_295,c_30])).

tff(c_44,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_541,plain,(
    ! [A_77,B_78,C_79] :
      ( k7_subset_1(A_77,B_78,C_79) = k4_xboole_0(B_78,C_79)
      | ~ m1_subset_1(B_78,k1_zfmisc_1(A_77)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_559,plain,(
    ! [C_79] : k7_subset_1('#skF_1','#skF_2',C_79) = k4_xboole_0('#skF_2',C_79) ),
    inference(resolution,[status(thm)],[c_44,c_541])).

tff(c_40,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k7_subset_1('#skF_1','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_599,plain,(
    k9_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_559,c_40])).

tff(c_915,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) != k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_599])).

tff(c_309,plain,(
    ! [A_61,B_62] :
      ( k3_subset_1(A_61,k3_subset_1(A_61,B_62)) = B_62
      | ~ m1_subset_1(B_62,k1_zfmisc_1(A_61)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_325,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_3')) = '#skF_3' ),
    inference(resolution,[status(thm)],[c_42,c_309])).

tff(c_38,plain,(
    ! [A_35] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_35)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_12,plain,(
    ! [A_12] : r1_tarski(k1_xboole_0,A_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_13] : k1_subset_1(A_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_16,plain,(
    ! [A_14] : k2_subset_1(A_14) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_subset_1(A_30)) = k2_subset_1(A_30) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_47,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_subset_1(A_30)) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_32])).

tff(c_48,plain,(
    ! [A_30] : k3_subset_1(A_30,k1_xboole_0) = A_30 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_47])).

tff(c_1137,plain,(
    ! [A_106,C_107,B_108] :
      ( r1_tarski(k3_subset_1(A_106,C_107),k3_subset_1(A_106,B_108))
      | ~ r1_tarski(B_108,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_106))
      | ~ m1_subset_1(B_108,k1_zfmisc_1(A_106)) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1170,plain,(
    ! [A_30,C_107] :
      ( r1_tarski(k3_subset_1(A_30,C_107),A_30)
      | ~ r1_tarski(k1_xboole_0,C_107)
      | ~ m1_subset_1(C_107,k1_zfmisc_1(A_30))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_30)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_1137])).

tff(c_1192,plain,(
    ! [A_109,C_110] :
      ( r1_tarski(k3_subset_1(A_109,C_110),A_109)
      | ~ m1_subset_1(C_110,k1_zfmisc_1(A_109)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_12,c_1170])).

tff(c_1204,plain,
    ( r1_tarski('#skF_3','#skF_1')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_325,c_1192])).

tff(c_1218,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_295,c_1204])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1230,plain,(
    k3_xboole_0('#skF_3','#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1218,c_10])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_165,plain,(
    ! [A_53,B_54] : k5_xboole_0(A_53,k3_xboole_0(A_53,B_54)) = k4_xboole_0(A_53,B_54) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_180,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_165])).

tff(c_1299,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k4_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1230,c_180])).

tff(c_1319,plain,(
    k5_xboole_0('#skF_1','#skF_3') = k3_subset_1('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_1299])).

tff(c_251,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_234])).

tff(c_384,plain,(
    m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_45])).

tff(c_321,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_44,c_309])).

tff(c_1201,plain,
    ( r1_tarski('#skF_2','#skF_1')
    | ~ m1_subset_1(k3_subset_1('#skF_1','#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_321,c_1192])).

tff(c_1216,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_384,c_1201])).

tff(c_1226,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_1216,c_10])).

tff(c_752,plain,(
    ! [A_92,B_93,C_94] : k5_xboole_0(k3_xboole_0(A_92,B_93),k3_xboole_0(C_94,B_93)) = k3_xboole_0(k5_xboole_0(A_92,C_94),B_93) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2221,plain,(
    ! [A_133,B_134,C_135] : k5_xboole_0(k3_xboole_0(A_133,B_134),k3_xboole_0(C_135,A_133)) = k3_xboole_0(k5_xboole_0(B_134,C_135),A_133) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_752])).

tff(c_2297,plain,(
    ! [C_135] : k5_xboole_0('#skF_2',k3_xboole_0(C_135,'#skF_2')) = k3_xboole_0(k5_xboole_0('#skF_1',C_135),'#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1226,c_2221])).

tff(c_2583,plain,(
    ! [C_139] : k3_xboole_0('#skF_2',k5_xboole_0('#skF_1',C_139)) = k4_xboole_0('#skF_2',C_139) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_2,c_2297])).

tff(c_2622,plain,(
    k3_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_3')) = k4_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_2583])).

tff(c_2648,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_915,c_2622])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:03:11 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.98/1.73  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.74  
% 3.98/1.74  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.74  %$ r1_tarski > m1_subset_1 > k9_subset_1 > k7_subset_1 > k6_subset_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_subset_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.98/1.74  
% 3.98/1.74  %Foreground sorts:
% 3.98/1.74  
% 3.98/1.74  
% 3.98/1.74  %Background operators:
% 3.98/1.74  
% 3.98/1.74  
% 3.98/1.74  %Foreground operators:
% 3.98/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.98/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.98/1.74  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.98/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.98/1.74  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.98/1.74  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 3.98/1.74  tff('#skF_2', type, '#skF_2': $i).
% 3.98/1.74  tff(k7_subset_1, type, k7_subset_1: ($i * $i * $i) > $i).
% 3.98/1.74  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 3.98/1.74  tff('#skF_3', type, '#skF_3': $i).
% 3.98/1.74  tff('#skF_1', type, '#skF_1': $i).
% 3.98/1.74  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.98/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.98/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.98/1.74  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 3.98/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.98/1.74  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 3.98/1.74  tff(k9_subset_1, type, k9_subset_1: ($i * $i * $i) > $i).
% 3.98/1.74  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.98/1.74  
% 3.98/1.76  tff(f_86, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k9_subset_1(A, B, k3_subset_1(A, C))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t32_subset_1)).
% 3.98/1.76  tff(f_47, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 3.98/1.76  tff(f_57, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 3.98/1.76  tff(f_51, axiom, (![A, B]: m1_subset_1(k6_subset_1(A, B), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_subset_1)).
% 3.98/1.76  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (k9_subset_1(A, B, C) = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_subset_1)).
% 3.98/1.76  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k7_subset_1(A, B, C) = k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_subset_1)).
% 3.98/1.76  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 3.98/1.76  tff(f_78, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.98/1.76  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.98/1.76  tff(f_41, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_subset_1)).
% 3.98/1.76  tff(f_43, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 3.98/1.76  tff(f_67, axiom, (![A]: (k2_subset_1(A) = k3_subset_1(A, k1_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_subset_1)).
% 3.98/1.76  tff(f_76, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(B, C) <=> r1_tarski(k3_subset_1(A, C), k3_subset_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_subset_1)).
% 3.98/1.76  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.98/1.76  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.98/1.76  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.98/1.76  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 3.98/1.76  tff(c_42, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.76  tff(c_234, plain, (![A_56, B_57]: (k4_xboole_0(A_56, B_57)=k3_subset_1(A_56, B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_56)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.98/1.76  tff(c_255, plain, (k4_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_42, c_234])).
% 3.98/1.76  tff(c_26, plain, (![A_22, B_23]: (k6_subset_1(A_22, B_23)=k4_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.98/1.76  tff(c_22, plain, (![A_18, B_19]: (m1_subset_1(k6_subset_1(A_18, B_19), k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.98/1.76  tff(c_45, plain, (![A_18, B_19]: (m1_subset_1(k4_xboole_0(A_18, B_19), k1_zfmisc_1(A_18)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_22])).
% 3.98/1.76  tff(c_295, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_255, c_45])).
% 3.98/1.76  tff(c_30, plain, (![A_27, B_28, C_29]: (k9_subset_1(A_27, B_28, C_29)=k3_xboole_0(B_28, C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.98/1.76  tff(c_463, plain, (![B_28]: (k9_subset_1('#skF_1', B_28, k3_subset_1('#skF_1', '#skF_3'))=k3_xboole_0(B_28, k3_subset_1('#skF_1', '#skF_3')))), inference(resolution, [status(thm)], [c_295, c_30])).
% 3.98/1.76  tff(c_44, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.76  tff(c_541, plain, (![A_77, B_78, C_79]: (k7_subset_1(A_77, B_78, C_79)=k4_xboole_0(B_78, C_79) | ~m1_subset_1(B_78, k1_zfmisc_1(A_77)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.98/1.76  tff(c_559, plain, (![C_79]: (k7_subset_1('#skF_1', '#skF_2', C_79)=k4_xboole_0('#skF_2', C_79))), inference(resolution, [status(thm)], [c_44, c_541])).
% 3.98/1.76  tff(c_40, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k7_subset_1('#skF_1', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.98/1.76  tff(c_599, plain, (k9_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_559, c_40])).
% 3.98/1.76  tff(c_915, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))!=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_463, c_599])).
% 3.98/1.76  tff(c_309, plain, (![A_61, B_62]: (k3_subset_1(A_61, k3_subset_1(A_61, B_62))=B_62 | ~m1_subset_1(B_62, k1_zfmisc_1(A_61)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.98/1.76  tff(c_325, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_3'))='#skF_3'), inference(resolution, [status(thm)], [c_42, c_309])).
% 3.98/1.76  tff(c_38, plain, (![A_35]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_35)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.98/1.76  tff(c_12, plain, (![A_12]: (r1_tarski(k1_xboole_0, A_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.98/1.76  tff(c_14, plain, (![A_13]: (k1_subset_1(A_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.98/1.76  tff(c_16, plain, (![A_14]: (k2_subset_1(A_14)=A_14)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.98/1.76  tff(c_32, plain, (![A_30]: (k3_subset_1(A_30, k1_subset_1(A_30))=k2_subset_1(A_30))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.98/1.76  tff(c_47, plain, (![A_30]: (k3_subset_1(A_30, k1_subset_1(A_30))=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_32])).
% 3.98/1.76  tff(c_48, plain, (![A_30]: (k3_subset_1(A_30, k1_xboole_0)=A_30)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_47])).
% 3.98/1.76  tff(c_1137, plain, (![A_106, C_107, B_108]: (r1_tarski(k3_subset_1(A_106, C_107), k3_subset_1(A_106, B_108)) | ~r1_tarski(B_108, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(A_106)) | ~m1_subset_1(B_108, k1_zfmisc_1(A_106)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.98/1.76  tff(c_1170, plain, (![A_30, C_107]: (r1_tarski(k3_subset_1(A_30, C_107), A_30) | ~r1_tarski(k1_xboole_0, C_107) | ~m1_subset_1(C_107, k1_zfmisc_1(A_30)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_30)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_1137])).
% 3.98/1.76  tff(c_1192, plain, (![A_109, C_110]: (r1_tarski(k3_subset_1(A_109, C_110), A_109) | ~m1_subset_1(C_110, k1_zfmisc_1(A_109)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_12, c_1170])).
% 3.98/1.76  tff(c_1204, plain, (r1_tarski('#skF_3', '#skF_1') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_325, c_1192])).
% 3.98/1.76  tff(c_1218, plain, (r1_tarski('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_295, c_1204])).
% 3.98/1.76  tff(c_10, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.98/1.76  tff(c_1230, plain, (k3_xboole_0('#skF_3', '#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_1218, c_10])).
% 3.98/1.76  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.98/1.76  tff(c_165, plain, (![A_53, B_54]: (k5_xboole_0(A_53, k3_xboole_0(A_53, B_54))=k4_xboole_0(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.98/1.76  tff(c_180, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_165])).
% 3.98/1.76  tff(c_1299, plain, (k5_xboole_0('#skF_1', '#skF_3')=k4_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1230, c_180])).
% 3.98/1.76  tff(c_1319, plain, (k5_xboole_0('#skF_1', '#skF_3')=k3_subset_1('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_255, c_1299])).
% 3.98/1.76  tff(c_251, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_234])).
% 3.98/1.76  tff(c_384, plain, (m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_45])).
% 3.98/1.76  tff(c_321, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_44, c_309])).
% 3.98/1.76  tff(c_1201, plain, (r1_tarski('#skF_2', '#skF_1') | ~m1_subset_1(k3_subset_1('#skF_1', '#skF_2'), k1_zfmisc_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_321, c_1192])).
% 3.98/1.76  tff(c_1216, plain, (r1_tarski('#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_384, c_1201])).
% 3.98/1.76  tff(c_1226, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_1216, c_10])).
% 3.98/1.76  tff(c_752, plain, (![A_92, B_93, C_94]: (k5_xboole_0(k3_xboole_0(A_92, B_93), k3_xboole_0(C_94, B_93))=k3_xboole_0(k5_xboole_0(A_92, C_94), B_93))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.98/1.76  tff(c_2221, plain, (![A_133, B_134, C_135]: (k5_xboole_0(k3_xboole_0(A_133, B_134), k3_xboole_0(C_135, A_133))=k3_xboole_0(k5_xboole_0(B_134, C_135), A_133))), inference(superposition, [status(thm), theory('equality')], [c_2, c_752])).
% 3.98/1.76  tff(c_2297, plain, (![C_135]: (k5_xboole_0('#skF_2', k3_xboole_0(C_135, '#skF_2'))=k3_xboole_0(k5_xboole_0('#skF_1', C_135), '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_1226, c_2221])).
% 3.98/1.76  tff(c_2583, plain, (![C_139]: (k3_xboole_0('#skF_2', k5_xboole_0('#skF_1', C_139))=k4_xboole_0('#skF_2', C_139))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_2, c_2297])).
% 3.98/1.76  tff(c_2622, plain, (k3_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_3'))=k4_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1319, c_2583])).
% 3.98/1.76  tff(c_2648, plain, $false, inference(negUnitSimplification, [status(thm)], [c_915, c_2622])).
% 3.98/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.98/1.76  
% 3.98/1.76  Inference rules
% 3.98/1.76  ----------------------
% 3.98/1.76  #Ref     : 0
% 3.98/1.76  #Sup     : 659
% 3.98/1.76  #Fact    : 0
% 3.98/1.76  #Define  : 0
% 3.98/1.76  #Split   : 2
% 3.98/1.76  #Chain   : 0
% 3.98/1.76  #Close   : 0
% 3.98/1.76  
% 3.98/1.76  Ordering : KBO
% 3.98/1.76  
% 3.98/1.76  Simplification rules
% 3.98/1.76  ----------------------
% 3.98/1.76  #Subsume      : 1
% 3.98/1.76  #Demod        : 628
% 3.98/1.76  #Tautology    : 414
% 3.98/1.76  #SimpNegUnit  : 1
% 3.98/1.76  #BackRed      : 4
% 3.98/1.76  
% 3.98/1.76  #Partial instantiations: 0
% 3.98/1.76  #Strategies tried      : 1
% 3.98/1.76  
% 3.98/1.76  Timing (in seconds)
% 3.98/1.76  ----------------------
% 3.98/1.76  Preprocessing        : 0.32
% 3.98/1.76  Parsing              : 0.18
% 3.98/1.76  CNF conversion       : 0.02
% 3.98/1.76  Main loop            : 0.67
% 3.98/1.76  Inferencing          : 0.21
% 3.98/1.76  Reduction            : 0.29
% 3.98/1.76  Demodulation         : 0.24
% 3.98/1.76  BG Simplification    : 0.03
% 3.98/1.76  Subsumption          : 0.10
% 3.98/1.76  Abstraction          : 0.04
% 3.98/1.76  MUC search           : 0.00
% 3.98/1.76  Cooper               : 0.00
% 3.98/1.76  Total                : 1.02
% 3.98/1.76  Index Insertion      : 0.00
% 3.98/1.76  Index Deletion       : 0.00
% 3.98/1.76  Index Matching       : 0.00
% 3.98/1.76  BG Taut test         : 0.00
%------------------------------------------------------------------------------
