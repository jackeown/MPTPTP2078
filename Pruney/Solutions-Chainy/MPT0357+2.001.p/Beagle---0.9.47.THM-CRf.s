%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:58 EST 2020

% Result     : Theorem 6.68s
% Output     : CNFRefutation 6.77s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 129 expanded)
%              Number of leaves         :   37 (  59 expanded)
%              Depth                    :   13
%              Number of atoms          :   90 ( 171 expanded)
%              Number of equality atoms :   51 (  75 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => ! [C] :
            ( m1_subset_1(C,k1_zfmisc_1(A))
           => ( r1_tarski(k3_subset_1(A,B),C)
             => r1_tarski(k3_subset_1(A,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_58,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k3_xboole_0(A,k4_xboole_0(B,C)) = k4_xboole_0(k3_xboole_0(A,B),C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(c_149,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | k4_xboole_0(A_45,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ~ r1_tarski(k3_subset_1('#skF_3','#skF_5'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_153,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_149,c_52])).

tff(c_56,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1338,plain,(
    ! [A_104,B_105] :
      ( k4_xboole_0(A_104,B_105) = k3_subset_1(A_104,B_105)
      | ~ m1_subset_1(B_105,k1_zfmisc_1(A_104)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1350,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_56,c_1338])).

tff(c_22,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_342,plain,(
    ! [A_66,B_67] : k3_tarski(k2_tarski(A_66,B_67)) = k2_xboole_0(B_67,A_66) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_174])).

tff(c_38,plain,(
    ! [A_27,B_28] : k3_tarski(k2_tarski(A_27,B_28)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_348,plain,(
    ! [B_67,A_66] : k2_xboole_0(B_67,A_66) = k2_xboole_0(A_66,B_67) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_38])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_zfmisc_1(A_33)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_951,plain,(
    ! [B_91,A_92] :
      ( r2_hidden(B_91,A_92)
      | ~ m1_subset_1(B_91,A_92)
      | v1_xboole_0(A_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [C_26,A_22] :
      ( r1_tarski(C_26,A_22)
      | ~ r2_hidden(C_26,k1_zfmisc_1(A_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_958,plain,(
    ! [B_91,A_22] :
      ( r1_tarski(B_91,A_22)
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_22))
      | v1_xboole_0(k1_zfmisc_1(A_22)) ) ),
    inference(resolution,[status(thm)],[c_951,c_26])).

tff(c_1079,plain,(
    ! [B_99,A_100] :
      ( r1_tarski(B_99,A_100)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_100)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_958])).

tff(c_1092,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_1079])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = k1_xboole_0
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1188,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1092,c_6])).

tff(c_12,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1222,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1188,c_12])).

tff(c_1233,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_348,c_8,c_1222])).

tff(c_1351,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_1338])).

tff(c_1386,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_12])).

tff(c_1396,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1233,c_1386])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1091,plain,(
    r1_tarski('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_56,c_1079])).

tff(c_1184,plain,(
    k4_xboole_0('#skF_5','#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1091,c_6])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1195,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k3_xboole_0('#skF_5','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1184,c_18])).

tff(c_1208,plain,(
    k3_xboole_0('#skF_3','#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_1195])).

tff(c_54,plain,(
    r1_tarski(k3_subset_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_189,plain,(
    ! [A_57,B_58] :
      ( k4_xboole_0(A_57,B_58) = k1_xboole_0
      | ~ r1_tarski(A_57,B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_203,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_189])).

tff(c_541,plain,(
    ! [A_74,B_75] : k4_xboole_0(A_74,k4_xboole_0(A_74,B_75)) = k3_xboole_0(A_74,B_75) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_585,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_4'),k1_xboole_0) = k3_xboole_0(k3_subset_1('#skF_3','#skF_4'),'#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_203,c_541])).

tff(c_596,plain,(
    k3_xboole_0('#skF_5',k3_subset_1('#skF_3','#skF_4')) = k3_subset_1('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_14,c_585])).

tff(c_1093,plain,(
    ! [A_101,B_102,C_103] : k4_xboole_0(k3_xboole_0(A_101,B_102),C_103) = k3_xboole_0(A_101,k4_xboole_0(B_102,C_103)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_7181,plain,(
    ! [C_184,A_185,B_186] : k2_xboole_0(C_184,k3_xboole_0(A_185,k4_xboole_0(B_186,C_184))) = k2_xboole_0(C_184,k3_xboole_0(A_185,B_186)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1093,c_12])).

tff(c_7632,plain,(
    ! [A_190] : k2_xboole_0('#skF_4',k3_xboole_0(A_190,k3_subset_1('#skF_3','#skF_4'))) = k2_xboole_0('#skF_4',k3_xboole_0(A_190,'#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1351,c_7181])).

tff(c_7714,plain,(
    k2_xboole_0('#skF_4',k3_xboole_0('#skF_5','#skF_3')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_596,c_7632])).

tff(c_7749,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1396,c_1208,c_2,c_7714])).

tff(c_16,plain,(
    ! [A_11,B_12] : k4_xboole_0(k2_xboole_0(A_11,B_12),B_12) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_7799,plain,(
    k4_xboole_0('#skF_3','#skF_5') = k4_xboole_0('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7749,c_16])).

tff(c_7813,plain,(
    k4_xboole_0('#skF_4','#skF_5') = k3_subset_1('#skF_3','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1350,c_7799])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_205,plain,(
    ! [A_6,B_7] : k4_xboole_0(k4_xboole_0(A_6,B_7),A_6) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_10,c_189])).

tff(c_10112,plain,(
    k4_xboole_0(k3_subset_1('#skF_3','#skF_5'),'#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_7813,c_205])).

tff(c_10133,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_153,c_10112])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:46:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.68/2.41  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.42  
% 6.73/2.42  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.73/2.42  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_xboole_0 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 6.73/2.42  
% 6.73/2.42  %Foreground sorts:
% 6.73/2.42  
% 6.73/2.42  
% 6.73/2.42  %Background operators:
% 6.73/2.42  
% 6.73/2.42  
% 6.73/2.42  %Foreground operators:
% 6.73/2.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.73/2.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.73/2.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.73/2.42  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.73/2.42  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.73/2.42  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.73/2.42  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.73/2.42  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 6.73/2.42  tff('#skF_5', type, '#skF_5': $i).
% 6.73/2.42  tff('#skF_3', type, '#skF_3': $i).
% 6.73/2.42  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.73/2.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.73/2.42  tff(k3_tarski, type, k3_tarski: $i > $i).
% 6.73/2.42  tff('#skF_4', type, '#skF_4': $i).
% 6.73/2.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.73/2.42  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 6.73/2.42  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.73/2.42  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.73/2.42  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.73/2.42  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.73/2.42  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.73/2.42  
% 6.77/2.44  tff(f_31, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 6.77/2.44  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (![C]: (m1_subset_1(C, k1_zfmisc_1(A)) => (r1_tarski(k3_subset_1(A, B), C) => r1_tarski(k3_subset_1(A, C), B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_subset_1)).
% 6.77/2.44  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 6.77/2.44  tff(f_47, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 6.77/2.44  tff(f_58, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 6.77/2.44  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 6.77/2.44  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 6.77/2.44  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 6.77/2.44  tff(f_56, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 6.77/2.44  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 6.77/2.44  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.77/2.44  tff(f_39, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 6.77/2.44  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.77/2.44  tff(f_45, axiom, (![A, B, C]: (k3_xboole_0(A, k4_xboole_0(B, C)) = k4_xboole_0(k3_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_xboole_1)).
% 6.77/2.44  tff(f_41, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 6.77/2.44  tff(f_35, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.77/2.44  tff(c_149, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | k4_xboole_0(A_45, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.44  tff(c_52, plain, (~r1_tarski(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.77/2.44  tff(c_153, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')!=k1_xboole_0), inference(resolution, [status(thm)], [c_149, c_52])).
% 6.77/2.44  tff(c_56, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.77/2.44  tff(c_1338, plain, (![A_104, B_105]: (k4_xboole_0(A_104, B_105)=k3_subset_1(A_104, B_105) | ~m1_subset_1(B_105, k1_zfmisc_1(A_104)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.77/2.44  tff(c_1350, plain, (k4_xboole_0('#skF_3', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_56, c_1338])).
% 6.77/2.44  tff(c_22, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.77/2.44  tff(c_174, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.77/2.44  tff(c_342, plain, (![A_66, B_67]: (k3_tarski(k2_tarski(A_66, B_67))=k2_xboole_0(B_67, A_66))), inference(superposition, [status(thm), theory('equality')], [c_22, c_174])).
% 6.77/2.44  tff(c_38, plain, (![A_27, B_28]: (k3_tarski(k2_tarski(A_27, B_28))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_58])).
% 6.77/2.44  tff(c_348, plain, (![B_67, A_66]: (k2_xboole_0(B_67, A_66)=k2_xboole_0(A_66, B_67))), inference(superposition, [status(thm), theory('equality')], [c_342, c_38])).
% 6.77/2.44  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.77/2.44  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.77/2.44  tff(c_50, plain, (![A_33]: (~v1_xboole_0(k1_zfmisc_1(A_33)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 6.77/2.44  tff(c_951, plain, (![B_91, A_92]: (r2_hidden(B_91, A_92) | ~m1_subset_1(B_91, A_92) | v1_xboole_0(A_92))), inference(cnfTransformation, [status(thm)], [f_71])).
% 6.77/2.44  tff(c_26, plain, (![C_26, A_22]: (r1_tarski(C_26, A_22) | ~r2_hidden(C_26, k1_zfmisc_1(A_22)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 6.77/2.44  tff(c_958, plain, (![B_91, A_22]: (r1_tarski(B_91, A_22) | ~m1_subset_1(B_91, k1_zfmisc_1(A_22)) | v1_xboole_0(k1_zfmisc_1(A_22)))), inference(resolution, [status(thm)], [c_951, c_26])).
% 6.77/2.44  tff(c_1079, plain, (![B_99, A_100]: (r1_tarski(B_99, A_100) | ~m1_subset_1(B_99, k1_zfmisc_1(A_100)))), inference(negUnitSimplification, [status(thm)], [c_50, c_958])).
% 6.77/2.44  tff(c_1092, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_1079])).
% 6.77/2.44  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=k1_xboole_0 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.44  tff(c_1188, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1092, c_6])).
% 6.77/2.44  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.77/2.44  tff(c_1222, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1188, c_12])).
% 6.77/2.44  tff(c_1233, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_348, c_8, c_1222])).
% 6.77/2.44  tff(c_1351, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_1338])).
% 6.77/2.44  tff(c_1386, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1351, c_12])).
% 6.77/2.44  tff(c_1396, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1233, c_1386])).
% 6.77/2.44  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.77/2.44  tff(c_14, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.77/2.44  tff(c_1091, plain, (r1_tarski('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_56, c_1079])).
% 6.77/2.44  tff(c_1184, plain, (k4_xboole_0('#skF_5', '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_1091, c_6])).
% 6.77/2.44  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.77/2.44  tff(c_1195, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k3_xboole_0('#skF_5', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1184, c_18])).
% 6.77/2.44  tff(c_1208, plain, (k3_xboole_0('#skF_3', '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_1195])).
% 6.77/2.44  tff(c_54, plain, (r1_tarski(k3_subset_1('#skF_3', '#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_88])).
% 6.77/2.44  tff(c_189, plain, (![A_57, B_58]: (k4_xboole_0(A_57, B_58)=k1_xboole_0 | ~r1_tarski(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.77/2.44  tff(c_203, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_5')=k1_xboole_0), inference(resolution, [status(thm)], [c_54, c_189])).
% 6.77/2.44  tff(c_541, plain, (![A_74, B_75]: (k4_xboole_0(A_74, k4_xboole_0(A_74, B_75))=k3_xboole_0(A_74, B_75))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.77/2.44  tff(c_585, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_4'), k1_xboole_0)=k3_xboole_0(k3_subset_1('#skF_3', '#skF_4'), '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_203, c_541])).
% 6.77/2.44  tff(c_596, plain, (k3_xboole_0('#skF_5', k3_subset_1('#skF_3', '#skF_4'))=k3_subset_1('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_14, c_585])).
% 6.77/2.44  tff(c_1093, plain, (![A_101, B_102, C_103]: (k4_xboole_0(k3_xboole_0(A_101, B_102), C_103)=k3_xboole_0(A_101, k4_xboole_0(B_102, C_103)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.77/2.44  tff(c_7181, plain, (![C_184, A_185, B_186]: (k2_xboole_0(C_184, k3_xboole_0(A_185, k4_xboole_0(B_186, C_184)))=k2_xboole_0(C_184, k3_xboole_0(A_185, B_186)))), inference(superposition, [status(thm), theory('equality')], [c_1093, c_12])).
% 6.77/2.44  tff(c_7632, plain, (![A_190]: (k2_xboole_0('#skF_4', k3_xboole_0(A_190, k3_subset_1('#skF_3', '#skF_4')))=k2_xboole_0('#skF_4', k3_xboole_0(A_190, '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_1351, c_7181])).
% 6.77/2.44  tff(c_7714, plain, (k2_xboole_0('#skF_4', k3_xboole_0('#skF_5', '#skF_3'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_596, c_7632])).
% 6.77/2.44  tff(c_7749, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1396, c_1208, c_2, c_7714])).
% 6.77/2.44  tff(c_16, plain, (![A_11, B_12]: (k4_xboole_0(k2_xboole_0(A_11, B_12), B_12)=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.77/2.44  tff(c_7799, plain, (k4_xboole_0('#skF_3', '#skF_5')=k4_xboole_0('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7749, c_16])).
% 6.77/2.44  tff(c_7813, plain, (k4_xboole_0('#skF_4', '#skF_5')=k3_subset_1('#skF_3', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1350, c_7799])).
% 6.77/2.44  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.77/2.44  tff(c_205, plain, (![A_6, B_7]: (k4_xboole_0(k4_xboole_0(A_6, B_7), A_6)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_189])).
% 6.77/2.44  tff(c_10112, plain, (k4_xboole_0(k3_subset_1('#skF_3', '#skF_5'), '#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_7813, c_205])).
% 6.77/2.44  tff(c_10133, plain, $false, inference(negUnitSimplification, [status(thm)], [c_153, c_10112])).
% 6.77/2.44  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.77/2.44  
% 6.77/2.44  Inference rules
% 6.77/2.44  ----------------------
% 6.77/2.44  #Ref     : 0
% 6.77/2.44  #Sup     : 2516
% 6.77/2.44  #Fact    : 0
% 6.77/2.44  #Define  : 0
% 6.77/2.44  #Split   : 0
% 6.77/2.44  #Chain   : 0
% 6.77/2.44  #Close   : 0
% 6.77/2.44  
% 6.77/2.44  Ordering : KBO
% 6.77/2.44  
% 6.77/2.44  Simplification rules
% 6.77/2.44  ----------------------
% 6.77/2.44  #Subsume      : 11
% 6.77/2.44  #Demod        : 2708
% 6.77/2.44  #Tautology    : 1762
% 6.77/2.44  #SimpNegUnit  : 3
% 6.77/2.44  #BackRed      : 1
% 6.77/2.44  
% 6.77/2.44  #Partial instantiations: 0
% 6.77/2.44  #Strategies tried      : 1
% 6.77/2.44  
% 6.77/2.44  Timing (in seconds)
% 6.77/2.44  ----------------------
% 6.77/2.44  Preprocessing        : 0.33
% 6.77/2.44  Parsing              : 0.17
% 6.77/2.44  CNF conversion       : 0.02
% 6.77/2.44  Main loop            : 1.35
% 6.77/2.44  Inferencing          : 0.34
% 6.77/2.44  Reduction            : 0.69
% 6.77/2.44  Demodulation         : 0.58
% 6.77/2.44  BG Simplification    : 0.04
% 6.77/2.44  Subsumption          : 0.20
% 6.77/2.44  Abstraction          : 0.05
% 6.77/2.44  MUC search           : 0.00
% 6.77/2.44  Cooper               : 0.00
% 6.77/2.44  Total                : 1.71
% 6.77/2.44  Index Insertion      : 0.00
% 6.77/2.44  Index Deletion       : 0.00
% 6.77/2.44  Index Matching       : 0.00
% 6.77/2.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------
