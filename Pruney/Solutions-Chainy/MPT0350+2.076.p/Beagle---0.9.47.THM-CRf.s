%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:35 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.63s
% Verified   : 
% Statistics : Number of formulae       :   84 ( 118 expanded)
%              Number of leaves         :   37 (  55 expanded)
%              Depth                    :   14
%              Number of atoms          :   91 ( 146 expanded)
%              Number of equality atoms :   41 (  62 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_65,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_71,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_75,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_63,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_38,plain,(
    ! [A_24] : k2_subset_1(A_24) = A_24 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_50,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_54,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_50])).

tff(c_92,plain,(
    ! [B_42,A_43] : k3_xboole_0(B_42,A_43) = k3_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_8,plain,(
    ! [A_7,B_8] : k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_107,plain,(
    ! [A_43,B_42] : k2_xboole_0(A_43,k3_xboole_0(B_42,A_43)) = A_43 ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_8])).

tff(c_42,plain,(
    ! [A_27] : m1_subset_1(k2_subset_1(A_27),k1_zfmisc_1(A_27)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_53,plain,(
    ! [A_27] : m1_subset_1(A_27,k1_zfmisc_1(A_27)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_73,plain,(
    ! [A_39,B_40] : k2_xboole_0(A_39,k3_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k2_xboole_0(A_9,B_10)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_79,plain,(
    ! [A_39] : k4_xboole_0(A_39,A_39) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_10])).

tff(c_412,plain,(
    ! [A_81,B_82] :
      ( k4_xboole_0(A_81,B_82) = k3_subset_1(A_81,B_82)
      | ~ m1_subset_1(B_82,k1_zfmisc_1(A_81)) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_422,plain,(
    ! [A_27] : k4_xboole_0(A_27,A_27) = k3_subset_1(A_27,A_27) ),
    inference(resolution,[status(thm)],[c_53,c_412])).

tff(c_429,plain,(
    ! [A_27] : k3_subset_1(A_27,A_27) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_422])).

tff(c_578,plain,(
    ! [A_90,B_91] :
      ( m1_subset_1(k3_subset_1(A_90,B_91),k1_zfmisc_1(A_90))
      | ~ m1_subset_1(B_91,k1_zfmisc_1(A_90)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_590,plain,(
    ! [A_27] :
      ( m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_27))
      | ~ m1_subset_1(A_27,k1_zfmisc_1(A_27)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_429,c_578])).

tff(c_596,plain,(
    ! [A_92] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_92)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_53,c_590])).

tff(c_46,plain,(
    ! [A_30] : ~ v1_xboole_0(k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_299,plain,(
    ! [B_69,A_70] :
      ( r2_hidden(B_69,A_70)
      | ~ m1_subset_1(B_69,A_70)
      | v1_xboole_0(A_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_16,plain,(
    ! [C_19,A_15] :
      ( r1_tarski(C_19,A_15)
      | ~ r2_hidden(C_19,k1_zfmisc_1(A_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_303,plain,(
    ! [B_69,A_15] :
      ( r1_tarski(B_69,A_15)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_15))
      | v1_xboole_0(k1_zfmisc_1(A_15)) ) ),
    inference(resolution,[status(thm)],[c_299,c_16])).

tff(c_306,plain,(
    ! [B_69,A_15] :
      ( r1_tarski(B_69,A_15)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_15)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_303])).

tff(c_609,plain,(
    ! [A_93] : r1_tarski(k1_xboole_0,A_93) ),
    inference(resolution,[status(thm)],[c_596,c_306])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_618,plain,(
    ! [A_94] : k2_xboole_0(k1_xboole_0,A_94) = A_94 ),
    inference(resolution,[status(thm)],[c_609,c_6])).

tff(c_729,plain,(
    ! [B_96] : k3_xboole_0(B_96,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_107,c_618])).

tff(c_844,plain,(
    ! [B_100] : k2_xboole_0(B_100,k1_xboole_0) = B_100 ),
    inference(superposition,[status(thm),theory(equality)],[c_729,c_8])).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_318,plain,(
    ! [B_73,A_74] :
      ( r1_tarski(B_73,A_74)
      | ~ m1_subset_1(B_73,k1_zfmisc_1(A_74)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_303])).

tff(c_331,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_318])).

tff(c_340,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_331,c_6])).

tff(c_344,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_340,c_10])).

tff(c_12,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_364,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k1_xboole_0) = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_344,c_12])).

tff(c_863,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_844,c_364])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_430,plain,(
    k4_xboole_0('#skF_3','#skF_4') = k3_subset_1('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_52,c_412])).

tff(c_441,plain,(
    k2_xboole_0(k3_xboole_0('#skF_3','#skF_4'),k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_12])).

tff(c_444,plain,(
    k2_xboole_0(k3_xboole_0('#skF_4','#skF_3'),k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_441])).

tff(c_907,plain,(
    k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_863,c_444])).

tff(c_44,plain,(
    ! [A_28,B_29] :
      ( m1_subset_1(k3_subset_1(A_28,B_29),k1_zfmisc_1(A_28))
      | ~ m1_subset_1(B_29,k1_zfmisc_1(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1333,plain,(
    ! [A_115,B_116,C_117] :
      ( k4_subset_1(A_115,B_116,C_117) = k2_xboole_0(B_116,C_117)
      | ~ m1_subset_1(C_117,k1_zfmisc_1(A_115))
      | ~ m1_subset_1(B_116,k1_zfmisc_1(A_115)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_4063,plain,(
    ! [A_183,B_184,B_185] :
      ( k4_subset_1(A_183,B_184,k3_subset_1(A_183,B_185)) = k2_xboole_0(B_184,k3_subset_1(A_183,B_185))
      | ~ m1_subset_1(B_184,k1_zfmisc_1(A_183))
      | ~ m1_subset_1(B_185,k1_zfmisc_1(A_183)) ) ),
    inference(resolution,[status(thm)],[c_44,c_1333])).

tff(c_4251,plain,(
    ! [B_188] :
      ( k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3',B_188)) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3',B_188))
      | ~ m1_subset_1(B_188,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_52,c_4063])).

tff(c_4278,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = k2_xboole_0('#skF_4',k3_subset_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_52,c_4251])).

tff(c_4290,plain,(
    k4_subset_1('#skF_3','#skF_4',k3_subset_1('#skF_3','#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_907,c_4278])).

tff(c_4292,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_4290])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 21:05:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.81  
% 4.48/1.81  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.48/1.81  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 4.48/1.81  
% 4.48/1.81  %Foreground sorts:
% 4.48/1.81  
% 4.48/1.81  
% 4.48/1.81  %Background operators:
% 4.48/1.81  
% 4.48/1.81  
% 4.48/1.81  %Foreground operators:
% 4.48/1.81  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.81  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.48/1.81  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.48/1.81  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.48/1.81  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.48/1.81  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.81  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.48/1.81  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 4.48/1.81  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.48/1.81  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.48/1.81  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.81  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.81  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.81  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.48/1.81  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.81  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.81  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 4.48/1.81  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.48/1.81  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.48/1.81  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.48/1.81  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.48/1.81  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.48/1.81  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.81  
% 4.63/1.82  tff(f_65, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.63/1.82  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_subset_1)).
% 4.63/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.63/1.82  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 4.63/1.82  tff(f_71, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.63/1.82  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.63/1.82  tff(f_69, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 4.63/1.82  tff(f_75, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 4.63/1.82  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.63/1.82  tff(f_63, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.63/1.82  tff(f_48, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 4.63/1.82  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 4.63/1.82  tff(f_39, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 4.63/1.82  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.63/1.82  tff(c_38, plain, (![A_24]: (k2_subset_1(A_24)=A_24)), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.63/1.82  tff(c_50, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.63/1.82  tff(c_54, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_50])).
% 4.63/1.82  tff(c_92, plain, (![B_42, A_43]: (k3_xboole_0(B_42, A_43)=k3_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.82  tff(c_8, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.82  tff(c_107, plain, (![A_43, B_42]: (k2_xboole_0(A_43, k3_xboole_0(B_42, A_43))=A_43)), inference(superposition, [status(thm), theory('equality')], [c_92, c_8])).
% 4.63/1.82  tff(c_42, plain, (![A_27]: (m1_subset_1(k2_subset_1(A_27), k1_zfmisc_1(A_27)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.63/1.82  tff(c_53, plain, (![A_27]: (m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 4.63/1.82  tff(c_73, plain, (![A_39, B_40]: (k2_xboole_0(A_39, k3_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.63/1.82  tff(c_10, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k2_xboole_0(A_9, B_10))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.63/1.82  tff(c_79, plain, (![A_39]: (k4_xboole_0(A_39, A_39)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_10])).
% 4.63/1.82  tff(c_412, plain, (![A_81, B_82]: (k4_xboole_0(A_81, B_82)=k3_subset_1(A_81, B_82) | ~m1_subset_1(B_82, k1_zfmisc_1(A_81)))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.63/1.82  tff(c_422, plain, (![A_27]: (k4_xboole_0(A_27, A_27)=k3_subset_1(A_27, A_27))), inference(resolution, [status(thm)], [c_53, c_412])).
% 4.63/1.82  tff(c_429, plain, (![A_27]: (k3_subset_1(A_27, A_27)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_79, c_422])).
% 4.63/1.82  tff(c_578, plain, (![A_90, B_91]: (m1_subset_1(k3_subset_1(A_90, B_91), k1_zfmisc_1(A_90)) | ~m1_subset_1(B_91, k1_zfmisc_1(A_90)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.63/1.82  tff(c_590, plain, (![A_27]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_27)) | ~m1_subset_1(A_27, k1_zfmisc_1(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_429, c_578])).
% 4.63/1.82  tff(c_596, plain, (![A_92]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_92)))), inference(demodulation, [status(thm), theory('equality')], [c_53, c_590])).
% 4.63/1.82  tff(c_46, plain, (![A_30]: (~v1_xboole_0(k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.63/1.82  tff(c_299, plain, (![B_69, A_70]: (r2_hidden(B_69, A_70) | ~m1_subset_1(B_69, A_70) | v1_xboole_0(A_70))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.63/1.82  tff(c_16, plain, (![C_19, A_15]: (r1_tarski(C_19, A_15) | ~r2_hidden(C_19, k1_zfmisc_1(A_15)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.63/1.82  tff(c_303, plain, (![B_69, A_15]: (r1_tarski(B_69, A_15) | ~m1_subset_1(B_69, k1_zfmisc_1(A_15)) | v1_xboole_0(k1_zfmisc_1(A_15)))), inference(resolution, [status(thm)], [c_299, c_16])).
% 4.63/1.82  tff(c_306, plain, (![B_69, A_15]: (r1_tarski(B_69, A_15) | ~m1_subset_1(B_69, k1_zfmisc_1(A_15)))), inference(negUnitSimplification, [status(thm)], [c_46, c_303])).
% 4.63/1.82  tff(c_609, plain, (![A_93]: (r1_tarski(k1_xboole_0, A_93))), inference(resolution, [status(thm)], [c_596, c_306])).
% 4.63/1.82  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.63/1.82  tff(c_618, plain, (![A_94]: (k2_xboole_0(k1_xboole_0, A_94)=A_94)), inference(resolution, [status(thm)], [c_609, c_6])).
% 4.63/1.82  tff(c_729, plain, (![B_96]: (k3_xboole_0(B_96, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_107, c_618])).
% 4.63/1.82  tff(c_844, plain, (![B_100]: (k2_xboole_0(B_100, k1_xboole_0)=B_100)), inference(superposition, [status(thm), theory('equality')], [c_729, c_8])).
% 4.63/1.82  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.63/1.82  tff(c_318, plain, (![B_73, A_74]: (r1_tarski(B_73, A_74) | ~m1_subset_1(B_73, k1_zfmisc_1(A_74)))), inference(negUnitSimplification, [status(thm)], [c_46, c_303])).
% 4.63/1.82  tff(c_331, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_318])).
% 4.63/1.82  tff(c_340, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_331, c_6])).
% 4.63/1.82  tff(c_344, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_340, c_10])).
% 4.63/1.82  tff(c_12, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.63/1.82  tff(c_364, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k1_xboole_0)='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_344, c_12])).
% 4.63/1.82  tff(c_863, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_844, c_364])).
% 4.63/1.82  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.63/1.82  tff(c_430, plain, (k4_xboole_0('#skF_3', '#skF_4')=k3_subset_1('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_52, c_412])).
% 4.63/1.82  tff(c_441, plain, (k2_xboole_0(k3_xboole_0('#skF_3', '#skF_4'), k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_430, c_12])).
% 4.63/1.82  tff(c_444, plain, (k2_xboole_0(k3_xboole_0('#skF_4', '#skF_3'), k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_441])).
% 4.63/1.82  tff(c_907, plain, (k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_863, c_444])).
% 4.63/1.82  tff(c_44, plain, (![A_28, B_29]: (m1_subset_1(k3_subset_1(A_28, B_29), k1_zfmisc_1(A_28)) | ~m1_subset_1(B_29, k1_zfmisc_1(A_28)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.63/1.82  tff(c_1333, plain, (![A_115, B_116, C_117]: (k4_subset_1(A_115, B_116, C_117)=k2_xboole_0(B_116, C_117) | ~m1_subset_1(C_117, k1_zfmisc_1(A_115)) | ~m1_subset_1(B_116, k1_zfmisc_1(A_115)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.63/1.82  tff(c_4063, plain, (![A_183, B_184, B_185]: (k4_subset_1(A_183, B_184, k3_subset_1(A_183, B_185))=k2_xboole_0(B_184, k3_subset_1(A_183, B_185)) | ~m1_subset_1(B_184, k1_zfmisc_1(A_183)) | ~m1_subset_1(B_185, k1_zfmisc_1(A_183)))), inference(resolution, [status(thm)], [c_44, c_1333])).
% 4.63/1.82  tff(c_4251, plain, (![B_188]: (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', B_188))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', B_188)) | ~m1_subset_1(B_188, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_52, c_4063])).
% 4.63/1.82  tff(c_4278, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))=k2_xboole_0('#skF_4', k3_subset_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_52, c_4251])).
% 4.63/1.82  tff(c_4290, plain, (k4_subset_1('#skF_3', '#skF_4', k3_subset_1('#skF_3', '#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_907, c_4278])).
% 4.63/1.82  tff(c_4292, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_4290])).
% 4.63/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.63/1.82  
% 4.63/1.82  Inference rules
% 4.63/1.82  ----------------------
% 4.63/1.82  #Ref     : 0
% 4.63/1.82  #Sup     : 1020
% 4.63/1.82  #Fact    : 0
% 4.63/1.82  #Define  : 0
% 4.63/1.82  #Split   : 0
% 4.63/1.82  #Chain   : 0
% 4.63/1.82  #Close   : 0
% 4.63/1.83  
% 4.63/1.83  Ordering : KBO
% 4.63/1.83  
% 4.63/1.83  Simplification rules
% 4.63/1.83  ----------------------
% 4.63/1.83  #Subsume      : 48
% 4.63/1.83  #Demod        : 1060
% 4.63/1.83  #Tautology    : 781
% 4.63/1.83  #SimpNegUnit  : 17
% 4.63/1.83  #BackRed      : 7
% 4.63/1.83  
% 4.63/1.83  #Partial instantiations: 0
% 4.63/1.83  #Strategies tried      : 1
% 4.63/1.83  
% 4.63/1.83  Timing (in seconds)
% 4.63/1.83  ----------------------
% 4.63/1.83  Preprocessing        : 0.31
% 4.63/1.83  Parsing              : 0.16
% 4.63/1.83  CNF conversion       : 0.02
% 4.63/1.83  Main loop            : 0.76
% 4.63/1.83  Inferencing          : 0.24
% 4.63/1.83  Reduction            : 0.34
% 4.63/1.83  Demodulation         : 0.27
% 4.63/1.83  BG Simplification    : 0.03
% 4.63/1.83  Subsumption          : 0.11
% 4.63/1.83  Abstraction          : 0.04
% 4.63/1.83  MUC search           : 0.00
% 4.63/1.83  Cooper               : 0.00
% 4.63/1.83  Total                : 1.10
% 4.63/1.83  Index Insertion      : 0.00
% 4.63/1.83  Index Deletion       : 0.00
% 4.63/1.83  Index Matching       : 0.00
% 4.63/1.83  BG Taut test         : 0.00
%------------------------------------------------------------------------------
