%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:40 EST 2020

% Result     : Theorem 2.80s
% Output     : CNFRefutation 2.80s
% Verified   : 
% Statistics : Number of formulae       :   73 (  81 expanded)
%              Number of leaves         :   39 (  44 expanded)
%              Depth                    :   12
%              Number of atoms          :   70 (  80 expanded)
%              Number of equality atoms :   34 (  41 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_72,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_29,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_77,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_57,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_74,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_38,plain,(
    ! [A_38] : k2_subset_1(A_38) = A_38 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_46,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_49,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_38,c_46])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,A_8) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_48,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_42,plain,(
    ! [A_40] : ~ v1_xboole_0(k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_32,plain,(
    ! [B_37,A_36] :
      ( r2_hidden(B_37,A_36)
      | ~ m1_subset_1(B_37,A_36)
      | v1_xboole_0(A_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_28,plain,(
    ! [A_35] : k3_tarski(k1_zfmisc_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_120,plain,(
    ! [A_52,B_53] :
      ( r1_tarski(A_52,k3_tarski(B_53))
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_171,plain,(
    ! [A_66,A_67] :
      ( r1_tarski(A_66,A_67)
      | ~ r2_hidden(A_66,k1_zfmisc_1(A_67)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_120])).

tff(c_175,plain,(
    ! [B_37,A_67] :
      ( r1_tarski(B_37,A_67)
      | ~ m1_subset_1(B_37,k1_zfmisc_1(A_67))
      | v1_xboole_0(k1_zfmisc_1(A_67)) ) ),
    inference(resolution,[status(thm)],[c_32,c_171])).

tff(c_340,plain,(
    ! [B_80,A_81] :
      ( r1_tarski(B_80,A_81)
      | ~ m1_subset_1(B_80,k1_zfmisc_1(A_81)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_175])).

tff(c_353,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_340])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( k3_xboole_0(A_4,B_5) = A_4
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_362,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_353,c_6])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_379,plain,(
    k5_xboole_0('#skF_2','#skF_2') = k4_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_362,c_2])).

tff(c_382,plain,(
    k4_xboole_0('#skF_2','#skF_1') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_379])).

tff(c_8,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_417,plain,(
    k2_xboole_0('#skF_1',k1_xboole_0) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_8])).

tff(c_420,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_417])).

tff(c_12,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_138,plain,(
    ! [A_58,B_59] : k3_tarski(k2_tarski(A_58,B_59)) = k2_xboole_0(A_58,B_59) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_179,plain,(
    ! [B_68,A_69] : k3_tarski(k2_tarski(B_68,A_69)) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_138])).

tff(c_26,plain,(
    ! [A_33,B_34] : k3_tarski(k2_tarski(A_33,B_34)) = k2_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_185,plain,(
    ! [B_68,A_69] : k2_xboole_0(B_68,A_69) = k2_xboole_0(A_69,B_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_179,c_26])).

tff(c_40,plain,(
    ! [A_39] : m1_subset_1(k2_subset_1(A_39),k1_zfmisc_1(A_39)) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_50,plain,(
    ! [A_39] : m1_subset_1(A_39,k1_zfmisc_1(A_39)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_40])).

tff(c_787,plain,(
    ! [A_128,B_129,C_130] :
      ( k4_subset_1(A_128,B_129,C_130) = k2_xboole_0(B_129,C_130)
      | ~ m1_subset_1(C_130,k1_zfmisc_1(A_128))
      | ~ m1_subset_1(B_129,k1_zfmisc_1(A_128)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_839,plain,(
    ! [A_138,B_139] :
      ( k4_subset_1(A_138,B_139,A_138) = k2_xboole_0(B_139,A_138)
      | ~ m1_subset_1(B_139,k1_zfmisc_1(A_138)) ) ),
    inference(resolution,[status(thm)],[c_50,c_787])).

tff(c_846,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_48,c_839])).

tff(c_851,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_420,c_185,c_846])).

tff(c_853,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_851])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n004.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:49:08 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.80/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.39  
% 2.80/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.39  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 2.80/1.39  
% 2.80/1.39  %Foreground sorts:
% 2.80/1.39  
% 2.80/1.39  
% 2.80/1.39  %Background operators:
% 2.80/1.39  
% 2.80/1.39  
% 2.80/1.39  %Foreground operators:
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.80/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.80/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.80/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.80/1.39  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.80/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.80/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.80/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.80/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.80/1.39  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.80/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.80/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.80/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.80/1.39  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.80/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.80/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.80/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.80/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.80/1.39  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.80/1.39  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.80/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.80/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.80/1.39  
% 2.80/1.40  tff(f_72, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.80/1.40  tff(f_88, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_subset_1)).
% 2.80/1.40  tff(f_29, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.80/1.40  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 2.80/1.40  tff(f_77, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.80/1.40  tff(f_70, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_subset_1)).
% 2.80/1.40  tff(f_57, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.80/1.40  tff(f_53, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 2.80/1.40  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.80/1.40  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.80/1.40  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.80/1.40  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.80/1.40  tff(f_55, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.80/1.40  tff(f_74, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 2.80/1.40  tff(f_83, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.80/1.40  tff(c_38, plain, (![A_38]: (k2_subset_1(A_38)=A_38)), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.80/1.40  tff(c_46, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.80/1.40  tff(c_49, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_38, c_46])).
% 2.80/1.40  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.80/1.40  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, A_8)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.80/1.40  tff(c_48, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.80/1.40  tff(c_42, plain, (![A_40]: (~v1_xboole_0(k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 2.80/1.40  tff(c_32, plain, (![B_37, A_36]: (r2_hidden(B_37, A_36) | ~m1_subset_1(B_37, A_36) | v1_xboole_0(A_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.80/1.40  tff(c_28, plain, (![A_35]: (k3_tarski(k1_zfmisc_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.80/1.40  tff(c_120, plain, (![A_52, B_53]: (r1_tarski(A_52, k3_tarski(B_53)) | ~r2_hidden(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.80/1.40  tff(c_171, plain, (![A_66, A_67]: (r1_tarski(A_66, A_67) | ~r2_hidden(A_66, k1_zfmisc_1(A_67)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_120])).
% 2.80/1.40  tff(c_175, plain, (![B_37, A_67]: (r1_tarski(B_37, A_67) | ~m1_subset_1(B_37, k1_zfmisc_1(A_67)) | v1_xboole_0(k1_zfmisc_1(A_67)))), inference(resolution, [status(thm)], [c_32, c_171])).
% 2.80/1.40  tff(c_340, plain, (![B_80, A_81]: (r1_tarski(B_80, A_81) | ~m1_subset_1(B_80, k1_zfmisc_1(A_81)))), inference(negUnitSimplification, [status(thm)], [c_42, c_175])).
% 2.80/1.40  tff(c_353, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_340])).
% 2.80/1.40  tff(c_6, plain, (![A_4, B_5]: (k3_xboole_0(A_4, B_5)=A_4 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.80/1.40  tff(c_362, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_353, c_6])).
% 2.80/1.40  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.80/1.40  tff(c_379, plain, (k5_xboole_0('#skF_2', '#skF_2')=k4_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_362, c_2])).
% 2.80/1.40  tff(c_382, plain, (k4_xboole_0('#skF_2', '#skF_1')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_10, c_379])).
% 2.80/1.40  tff(c_8, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.80/1.40  tff(c_417, plain, (k2_xboole_0('#skF_1', k1_xboole_0)=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_382, c_8])).
% 2.80/1.40  tff(c_420, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4, c_417])).
% 2.80/1.40  tff(c_12, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.80/1.40  tff(c_138, plain, (![A_58, B_59]: (k3_tarski(k2_tarski(A_58, B_59))=k2_xboole_0(A_58, B_59))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.40  tff(c_179, plain, (![B_68, A_69]: (k3_tarski(k2_tarski(B_68, A_69))=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_12, c_138])).
% 2.80/1.40  tff(c_26, plain, (![A_33, B_34]: (k3_tarski(k2_tarski(A_33, B_34))=k2_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.80/1.40  tff(c_185, plain, (![B_68, A_69]: (k2_xboole_0(B_68, A_69)=k2_xboole_0(A_69, B_68))), inference(superposition, [status(thm), theory('equality')], [c_179, c_26])).
% 2.80/1.40  tff(c_40, plain, (![A_39]: (m1_subset_1(k2_subset_1(A_39), k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.80/1.40  tff(c_50, plain, (![A_39]: (m1_subset_1(A_39, k1_zfmisc_1(A_39)))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_40])).
% 2.80/1.40  tff(c_787, plain, (![A_128, B_129, C_130]: (k4_subset_1(A_128, B_129, C_130)=k2_xboole_0(B_129, C_130) | ~m1_subset_1(C_130, k1_zfmisc_1(A_128)) | ~m1_subset_1(B_129, k1_zfmisc_1(A_128)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.80/1.40  tff(c_839, plain, (![A_138, B_139]: (k4_subset_1(A_138, B_139, A_138)=k2_xboole_0(B_139, A_138) | ~m1_subset_1(B_139, k1_zfmisc_1(A_138)))), inference(resolution, [status(thm)], [c_50, c_787])).
% 2.80/1.40  tff(c_846, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_48, c_839])).
% 2.80/1.40  tff(c_851, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_420, c_185, c_846])).
% 2.80/1.40  tff(c_853, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_851])).
% 2.80/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.80/1.40  
% 2.80/1.40  Inference rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Ref     : 0
% 2.80/1.40  #Sup     : 184
% 2.80/1.40  #Fact    : 0
% 2.80/1.40  #Define  : 0
% 2.80/1.40  #Split   : 0
% 2.80/1.40  #Chain   : 0
% 2.80/1.40  #Close   : 0
% 2.80/1.40  
% 2.80/1.40  Ordering : KBO
% 2.80/1.40  
% 2.80/1.40  Simplification rules
% 2.80/1.40  ----------------------
% 2.80/1.40  #Subsume      : 22
% 2.80/1.40  #Demod        : 46
% 2.80/1.40  #Tautology    : 113
% 2.80/1.40  #SimpNegUnit  : 6
% 2.80/1.40  #BackRed      : 0
% 2.80/1.40  
% 2.80/1.40  #Partial instantiations: 0
% 2.80/1.40  #Strategies tried      : 1
% 2.80/1.40  
% 2.80/1.40  Timing (in seconds)
% 2.80/1.40  ----------------------
% 2.80/1.41  Preprocessing        : 0.33
% 2.80/1.41  Parsing              : 0.18
% 2.80/1.41  CNF conversion       : 0.02
% 2.80/1.41  Main loop            : 0.32
% 2.80/1.41  Inferencing          : 0.12
% 2.80/1.41  Reduction            : 0.11
% 2.80/1.41  Demodulation         : 0.08
% 2.80/1.41  BG Simplification    : 0.02
% 2.80/1.41  Subsumption          : 0.05
% 2.80/1.41  Abstraction          : 0.02
% 2.80/1.41  MUC search           : 0.00
% 2.80/1.41  Cooper               : 0.00
% 2.80/1.41  Total                : 0.68
% 2.80/1.41  Index Insertion      : 0.00
% 2.80/1.41  Index Deletion       : 0.00
% 2.80/1.41  Index Matching       : 0.00
% 2.80/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
