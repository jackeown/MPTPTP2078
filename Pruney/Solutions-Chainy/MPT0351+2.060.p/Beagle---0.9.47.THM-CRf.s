%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:44 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 113 expanded)
%              Number of leaves         :   37 (  54 expanded)
%              Depth                    :   12
%              Number of atoms          :   80 ( 131 expanded)
%              Number of equality atoms :   40 (  64 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_73,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_75,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_84,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_78,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( B = k1_zfmisc_1(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k4_subset_1(A,C,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k4_subset_1)).

tff(c_52,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_42,plain,(
    ! [A_29] : k2_subset_1(A_29) = A_29 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_44,plain,(
    ! [A_30] : m1_subset_1(k2_subset_1(A_30),k1_zfmisc_1(A_30)) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [A_30] : m1_subset_1(A_30,k1_zfmisc_1(A_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_370,plain,(
    ! [A_85,B_86,C_87] :
      ( k4_subset_1(A_85,B_86,C_87) = k2_xboole_0(B_86,C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(A_85))
      | ~ m1_subset_1(B_86,k1_zfmisc_1(A_85)) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_384,plain,(
    ! [A_88,B_89] :
      ( k4_subset_1(A_88,B_89,A_88) = k2_xboole_0(B_89,A_88)
      | ~ m1_subset_1(B_89,k1_zfmisc_1(A_88)) ) ),
    inference(resolution,[status(thm)],[c_54,c_370])).

tff(c_398,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_384])).

tff(c_50,plain,(
    k4_subset_1('#skF_3','#skF_4',k2_subset_1('#skF_3')) != k2_subset_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_53,plain,(
    k4_subset_1('#skF_3','#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_50])).

tff(c_408,plain,(
    k2_xboole_0('#skF_4','#skF_3') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_398,c_53])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_84,plain,(
    ! [A_40,B_41] : k4_xboole_0(A_40,k2_xboole_0(A_40,B_41)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_91,plain,(
    ! [A_5] : k4_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_84])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_191,plain,(
    ! [A_62,B_63] : k5_xboole_0(A_62,k3_xboole_0(A_62,B_63)) = k4_xboole_0(A_62,B_63) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_200,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_191])).

tff(c_203,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_200])).

tff(c_46,plain,(
    ! [A_31] : ~ v1_xboole_0(k1_zfmisc_1(A_31)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_216,plain,(
    ! [B_67,A_68] :
      ( r2_hidden(B_67,A_68)
      | ~ m1_subset_1(B_67,A_68)
      | v1_xboole_0(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_18,plain,(
    ! [C_21,A_17] :
      ( r1_tarski(C_21,A_17)
      | ~ r2_hidden(C_21,k1_zfmisc_1(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_223,plain,(
    ! [B_67,A_17] :
      ( r1_tarski(B_67,A_17)
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_17))
      | v1_xboole_0(k1_zfmisc_1(A_17)) ) ),
    inference(resolution,[status(thm)],[c_216,c_18])).

tff(c_228,plain,(
    ! [B_69,A_70] :
      ( r1_tarski(B_69,A_70)
      | ~ m1_subset_1(B_69,k1_zfmisc_1(A_70)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_223])).

tff(c_245,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_228])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_264,plain,(
    k3_xboole_0('#skF_4','#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_245,c_8])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_268,plain,(
    k5_xboole_0('#skF_4','#skF_4') = k4_xboole_0('#skF_4','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_4])).

tff(c_271,plain,(
    k4_xboole_0('#skF_4','#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_268])).

tff(c_10,plain,(
    ! [A_8,B_9] : k2_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_276,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k2_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_10])).

tff(c_279,plain,(
    k2_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_276])).

tff(c_413,plain,(
    ! [B_91] :
      ( k4_subset_1('#skF_3',B_91,'#skF_4') = k2_xboole_0(B_91,'#skF_4')
      | ~ m1_subset_1(B_91,k1_zfmisc_1('#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_52,c_370])).

tff(c_425,plain,(
    k4_subset_1('#skF_3','#skF_3','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_54,c_413])).

tff(c_432,plain,(
    k4_subset_1('#skF_3','#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_279,c_425])).

tff(c_469,plain,(
    ! [A_95,C_96,B_97] :
      ( k4_subset_1(A_95,C_96,B_97) = k4_subset_1(A_95,B_97,C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(A_95))
      | ~ m1_subset_1(B_97,k1_zfmisc_1(A_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_483,plain,(
    ! [A_98,B_99] :
      ( k4_subset_1(A_98,B_99,A_98) = k4_subset_1(A_98,A_98,B_99)
      | ~ m1_subset_1(B_99,k1_zfmisc_1(A_98)) ) ),
    inference(resolution,[status(thm)],[c_54,c_469])).

tff(c_492,plain,(
    k4_subset_1('#skF_3','#skF_3','#skF_4') = k4_subset_1('#skF_3','#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_483])).

tff(c_498,plain,(
    k2_xboole_0('#skF_4','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_432,c_398,c_492])).

tff(c_500,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_408,c_498])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.08  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.08  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.07/0.27  % Computer   : n024.cluster.edu
% 0.07/0.27  % Model      : x86_64 x86_64
% 0.07/0.27  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.07/0.27  % Memory     : 8042.1875MB
% 0.07/0.27  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.07/0.27  % CPULimit   : 60
% 0.07/0.27  % DateTime   : Tue Dec  1 12:33:51 EST 2020
% 0.07/0.27  % CPUTime    : 
% 0.07/0.28  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.29  
% 2.30/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.29  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 2.30/1.29  
% 2.30/1.29  %Foreground sorts:
% 2.30/1.29  
% 2.30/1.29  
% 2.30/1.29  %Background operators:
% 2.30/1.29  
% 2.30/1.29  
% 2.30/1.29  %Foreground operators:
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.29  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.30/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.30/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.30/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.30/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.29  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.30/1.29  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.30/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.30/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.30/1.29  
% 2.30/1.31  tff(f_89, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.30/1.31  tff(f_73, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.30/1.31  tff(f_75, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.30/1.31  tff(f_84, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.30/1.31  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.30/1.31  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.30/1.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.30/1.31  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.30/1.31  tff(f_78, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.30/1.31  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.30/1.31  tff(f_50, axiom, (![A, B]: ((B = k1_zfmisc_1(A)) <=> (![C]: (r2_hidden(C, B) <=> r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_zfmisc_1)).
% 2.30/1.31  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.30/1.31  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.30/1.31  tff(f_58, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k4_subset_1(A, C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k4_subset_1)).
% 2.30/1.31  tff(c_52, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.30/1.31  tff(c_42, plain, (![A_29]: (k2_subset_1(A_29)=A_29)), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.30/1.31  tff(c_44, plain, (![A_30]: (m1_subset_1(k2_subset_1(A_30), k1_zfmisc_1(A_30)))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.30/1.31  tff(c_54, plain, (![A_30]: (m1_subset_1(A_30, k1_zfmisc_1(A_30)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 2.30/1.31  tff(c_370, plain, (![A_85, B_86, C_87]: (k4_subset_1(A_85, B_86, C_87)=k2_xboole_0(B_86, C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(A_85)) | ~m1_subset_1(B_86, k1_zfmisc_1(A_85)))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.30/1.31  tff(c_384, plain, (![A_88, B_89]: (k4_subset_1(A_88, B_89, A_88)=k2_xboole_0(B_89, A_88) | ~m1_subset_1(B_89, k1_zfmisc_1(A_88)))), inference(resolution, [status(thm)], [c_54, c_370])).
% 2.30/1.31  tff(c_398, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')=k2_xboole_0('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_384])).
% 2.30/1.31  tff(c_50, plain, (k4_subset_1('#skF_3', '#skF_4', k2_subset_1('#skF_3'))!=k2_subset_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.30/1.31  tff(c_53, plain, (k4_subset_1('#skF_3', '#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_50])).
% 2.30/1.31  tff(c_408, plain, (k2_xboole_0('#skF_4', '#skF_3')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_398, c_53])).
% 2.30/1.31  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.31  tff(c_84, plain, (![A_40, B_41]: (k4_xboole_0(A_40, k2_xboole_0(A_40, B_41))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.31  tff(c_91, plain, (![A_5]: (k4_xboole_0(A_5, A_5)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_84])).
% 2.30/1.31  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.30/1.31  tff(c_191, plain, (![A_62, B_63]: (k5_xboole_0(A_62, k3_xboole_0(A_62, B_63))=k4_xboole_0(A_62, B_63))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.31  tff(c_200, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_191])).
% 2.30/1.31  tff(c_203, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_91, c_200])).
% 2.30/1.31  tff(c_46, plain, (![A_31]: (~v1_xboole_0(k1_zfmisc_1(A_31)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.30/1.31  tff(c_216, plain, (![B_67, A_68]: (r2_hidden(B_67, A_68) | ~m1_subset_1(B_67, A_68) | v1_xboole_0(A_68))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.30/1.31  tff(c_18, plain, (![C_21, A_17]: (r1_tarski(C_21, A_17) | ~r2_hidden(C_21, k1_zfmisc_1(A_17)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.30/1.31  tff(c_223, plain, (![B_67, A_17]: (r1_tarski(B_67, A_17) | ~m1_subset_1(B_67, k1_zfmisc_1(A_17)) | v1_xboole_0(k1_zfmisc_1(A_17)))), inference(resolution, [status(thm)], [c_216, c_18])).
% 2.30/1.31  tff(c_228, plain, (![B_69, A_70]: (r1_tarski(B_69, A_70) | ~m1_subset_1(B_69, k1_zfmisc_1(A_70)))), inference(negUnitSimplification, [status(thm)], [c_46, c_223])).
% 2.30/1.31  tff(c_245, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_228])).
% 2.30/1.31  tff(c_8, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.30/1.31  tff(c_264, plain, (k3_xboole_0('#skF_4', '#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_245, c_8])).
% 2.30/1.31  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.30/1.31  tff(c_268, plain, (k5_xboole_0('#skF_4', '#skF_4')=k4_xboole_0('#skF_4', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_264, c_4])).
% 2.30/1.31  tff(c_271, plain, (k4_xboole_0('#skF_4', '#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_203, c_268])).
% 2.30/1.31  tff(c_10, plain, (![A_8, B_9]: (k2_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.30/1.31  tff(c_276, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k2_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_271, c_10])).
% 2.30/1.31  tff(c_279, plain, (k2_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_276])).
% 2.30/1.31  tff(c_413, plain, (![B_91]: (k4_subset_1('#skF_3', B_91, '#skF_4')=k2_xboole_0(B_91, '#skF_4') | ~m1_subset_1(B_91, k1_zfmisc_1('#skF_3')))), inference(resolution, [status(thm)], [c_52, c_370])).
% 2.30/1.31  tff(c_425, plain, (k4_subset_1('#skF_3', '#skF_3', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_54, c_413])).
% 2.30/1.31  tff(c_432, plain, (k4_subset_1('#skF_3', '#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_279, c_425])).
% 2.30/1.31  tff(c_469, plain, (![A_95, C_96, B_97]: (k4_subset_1(A_95, C_96, B_97)=k4_subset_1(A_95, B_97, C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(A_95)) | ~m1_subset_1(B_97, k1_zfmisc_1(A_95)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.30/1.31  tff(c_483, plain, (![A_98, B_99]: (k4_subset_1(A_98, B_99, A_98)=k4_subset_1(A_98, A_98, B_99) | ~m1_subset_1(B_99, k1_zfmisc_1(A_98)))), inference(resolution, [status(thm)], [c_54, c_469])).
% 2.30/1.31  tff(c_492, plain, (k4_subset_1('#skF_3', '#skF_3', '#skF_4')=k4_subset_1('#skF_3', '#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_52, c_483])).
% 2.30/1.31  tff(c_498, plain, (k2_xboole_0('#skF_4', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_432, c_398, c_492])).
% 2.30/1.31  tff(c_500, plain, $false, inference(negUnitSimplification, [status(thm)], [c_408, c_498])).
% 2.30/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.30/1.31  
% 2.30/1.31  Inference rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Ref     : 0
% 2.30/1.31  #Sup     : 106
% 2.30/1.31  #Fact    : 0
% 2.30/1.31  #Define  : 0
% 2.30/1.31  #Split   : 0
% 2.30/1.31  #Chain   : 0
% 2.30/1.31  #Close   : 0
% 2.30/1.31  
% 2.30/1.31  Ordering : KBO
% 2.30/1.31  
% 2.30/1.31  Simplification rules
% 2.30/1.31  ----------------------
% 2.30/1.31  #Subsume      : 9
% 2.30/1.31  #Demod        : 40
% 2.30/1.31  #Tautology    : 64
% 2.30/1.31  #SimpNegUnit  : 3
% 2.30/1.31  #BackRed      : 1
% 2.30/1.31  
% 2.30/1.31  #Partial instantiations: 0
% 2.30/1.31  #Strategies tried      : 1
% 2.30/1.31  
% 2.30/1.31  Timing (in seconds)
% 2.30/1.31  ----------------------
% 2.30/1.31  Preprocessing        : 0.37
% 2.30/1.31  Parsing              : 0.19
% 2.30/1.31  CNF conversion       : 0.03
% 2.30/1.31  Main loop            : 0.24
% 2.30/1.31  Inferencing          : 0.09
% 2.30/1.31  Reduction            : 0.08
% 2.30/1.31  Demodulation         : 0.06
% 2.30/1.31  BG Simplification    : 0.02
% 2.30/1.31  Subsumption          : 0.04
% 2.30/1.31  Abstraction          : 0.02
% 2.30/1.31  MUC search           : 0.00
% 2.30/1.31  Cooper               : 0.00
% 2.30/1.31  Total                : 0.65
% 2.30/1.31  Index Insertion      : 0.00
% 2.30/1.31  Index Deletion       : 0.00
% 2.30/1.31  Index Matching       : 0.00
% 2.30/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
