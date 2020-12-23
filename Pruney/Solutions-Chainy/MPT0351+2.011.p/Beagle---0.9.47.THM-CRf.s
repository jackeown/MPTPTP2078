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
% DateTime   : Thu Dec  3 09:55:38 EST 2020

% Result     : Theorem 4.68s
% Output     : CNFRefutation 4.68s
% Verified   : 
% Statistics : Number of formulae       :   75 (  83 expanded)
%              Number of leaves         :   40 (  45 expanded)
%              Depth                    :   12
%              Number of atoms          :   72 (  82 expanded)
%              Number of equality atoms :   36 (  43 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_76,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k2_subset_1(A)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_subset_1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_81,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_74,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> r2_hidden(B,A) ) )
      & ( v1_xboole_0(A)
       => ( m1_subset_1(B,A)
        <=> v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_subset_1)).

tff(f_61,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => r1_tarski(A,k3_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_78,axiom,(
    ! [A] : m1_subset_1(k2_subset_1(A),k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_42,plain,(
    ! [A_48] : k2_subset_1(A_48) = A_48 ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_50,plain,(
    k4_subset_1('#skF_1','#skF_2',k2_subset_1('#skF_1')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_53,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_42,c_50])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_46,plain,(
    ! [A_50] : ~ v1_xboole_0(k1_zfmisc_1(A_50)) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_36,plain,(
    ! [B_47,A_46] :
      ( r2_hidden(B_47,A_46)
      | ~ m1_subset_1(B_47,A_46)
      | v1_xboole_0(A_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,(
    ! [A_45] : k3_tarski(k1_zfmisc_1(A_45)) = A_45 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_185,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(A_68,k3_tarski(B_69))
      | ~ r2_hidden(A_68,B_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_277,plain,(
    ! [A_82,A_83] :
      ( r1_tarski(A_82,A_83)
      | ~ r2_hidden(A_82,k1_zfmisc_1(A_83)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_185])).

tff(c_281,plain,(
    ! [B_47,A_83] :
      ( r1_tarski(B_47,A_83)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_83))
      | v1_xboole_0(k1_zfmisc_1(A_83)) ) ),
    inference(resolution,[status(thm)],[c_36,c_277])).

tff(c_286,plain,(
    ! [B_84,A_85] :
      ( r1_tarski(B_84,A_85)
      | ~ m1_subset_1(B_84,k1_zfmisc_1(A_85)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_281])).

tff(c_299,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_286])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k3_xboole_0(A_3,B_4) = A_3
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_308,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_299,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_326,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_308,c_2])).

tff(c_455,plain,(
    ! [A_99,B_100] : k5_xboole_0(k5_xboole_0(A_99,B_100),k3_xboole_0(A_99,B_100)) = k2_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_476,plain,(
    k5_xboole_0(k5_xboole_0('#skF_1','#skF_2'),'#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_326,c_455])).

tff(c_8,plain,(
    ! [A_6,B_7,C_8] : k5_xboole_0(k5_xboole_0(A_6,B_7),C_8) = k5_xboole_0(A_6,k5_xboole_0(B_7,C_8)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_1222,plain,(
    k5_xboole_0('#skF_1',k5_xboole_0('#skF_2','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_476,c_8])).

tff(c_1232,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10,c_1222])).

tff(c_14,plain,(
    ! [B_13,A_12] : k2_tarski(B_13,A_12) = k2_tarski(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_194,plain,(
    ! [A_72,B_73] : k3_tarski(k2_tarski(A_72,B_73)) = k2_xboole_0(A_72,B_73) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_217,plain,(
    ! [B_76,A_77] : k3_tarski(k2_tarski(B_76,A_77)) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_194])).

tff(c_30,plain,(
    ! [A_43,B_44] : k3_tarski(k2_tarski(A_43,B_44)) = k2_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_223,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_217,c_30])).

tff(c_44,plain,(
    ! [A_49] : m1_subset_1(k2_subset_1(A_49),k1_zfmisc_1(A_49)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_54,plain,(
    ! [A_49] : m1_subset_1(A_49,k1_zfmisc_1(A_49)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_44])).

tff(c_1960,plain,(
    ! [A_144,B_145,C_146] :
      ( k4_subset_1(A_144,B_145,C_146) = k2_xboole_0(B_145,C_146)
      | ~ m1_subset_1(C_146,k1_zfmisc_1(A_144))
      | ~ m1_subset_1(B_145,k1_zfmisc_1(A_144)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_4583,plain,(
    ! [A_193,B_194] :
      ( k4_subset_1(A_193,B_194,A_193) = k2_xboole_0(B_194,A_193)
      | ~ m1_subset_1(B_194,k1_zfmisc_1(A_193)) ) ),
    inference(resolution,[status(thm)],[c_54,c_1960])).

tff(c_4590,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = k2_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_52,c_4583])).

tff(c_4595,plain,(
    k4_subset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1232,c_223,c_4590])).

tff(c_4597,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_4595])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:24:26 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.68/1.91  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.92  
% 4.68/1.92  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.92  %$ r2_hidden > r1_tarski > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_1
% 4.68/1.92  
% 4.68/1.92  %Foreground sorts:
% 4.68/1.92  
% 4.68/1.92  
% 4.68/1.92  %Background operators:
% 4.68/1.92  
% 4.68/1.92  
% 4.68/1.92  %Foreground operators:
% 4.68/1.92  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.68/1.92  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.68/1.92  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.68/1.92  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.68/1.92  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.68/1.92  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.68/1.92  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.68/1.92  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.68/1.92  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 4.68/1.92  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.68/1.92  tff('#skF_2', type, '#skF_2': $i).
% 4.68/1.92  tff('#skF_1', type, '#skF_1': $i).
% 4.68/1.92  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.92  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.68/1.92  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.92  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.68/1.92  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.68/1.92  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.68/1.92  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.68/1.92  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.68/1.92  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.68/1.92  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 4.68/1.92  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 4.68/1.92  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.68/1.92  
% 4.68/1.93  tff(f_76, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 4.68/1.93  tff(f_92, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k2_subset_1(A)) = k2_subset_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_subset_1)).
% 4.68/1.93  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.68/1.93  tff(f_37, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 4.68/1.93  tff(f_81, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 4.68/1.93  tff(f_74, axiom, (![A, B]: ((~v1_xboole_0(A) => (m1_subset_1(B, A) <=> r2_hidden(B, A))) & (v1_xboole_0(A) => (m1_subset_1(B, A) <=> v1_xboole_0(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_subset_1)).
% 4.68/1.93  tff(f_61, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 4.68/1.93  tff(f_57, axiom, (![A, B]: (r2_hidden(A, B) => r1_tarski(A, k3_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l49_zfmisc_1)).
% 4.68/1.93  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.68/1.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.68/1.93  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 4.68/1.93  tff(f_35, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.68/1.93  tff(f_41, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 4.68/1.93  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 4.68/1.93  tff(f_78, axiom, (![A]: m1_subset_1(k2_subset_1(A), k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_subset_1)).
% 4.68/1.93  tff(f_87, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 4.68/1.93  tff(c_42, plain, (![A_48]: (k2_subset_1(A_48)=A_48)), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.68/1.93  tff(c_50, plain, (k4_subset_1('#skF_1', '#skF_2', k2_subset_1('#skF_1'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.68/1.93  tff(c_53, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_42, c_50])).
% 4.68/1.93  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.68/1.93  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.68/1.93  tff(c_52, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.68/1.93  tff(c_46, plain, (![A_50]: (~v1_xboole_0(k1_zfmisc_1(A_50)))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.68/1.93  tff(c_36, plain, (![B_47, A_46]: (r2_hidden(B_47, A_46) | ~m1_subset_1(B_47, A_46) | v1_xboole_0(A_46))), inference(cnfTransformation, [status(thm)], [f_74])).
% 4.68/1.93  tff(c_32, plain, (![A_45]: (k3_tarski(k1_zfmisc_1(A_45))=A_45)), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.68/1.93  tff(c_185, plain, (![A_68, B_69]: (r1_tarski(A_68, k3_tarski(B_69)) | ~r2_hidden(A_68, B_69))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.68/1.93  tff(c_277, plain, (![A_82, A_83]: (r1_tarski(A_82, A_83) | ~r2_hidden(A_82, k1_zfmisc_1(A_83)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_185])).
% 4.68/1.93  tff(c_281, plain, (![B_47, A_83]: (r1_tarski(B_47, A_83) | ~m1_subset_1(B_47, k1_zfmisc_1(A_83)) | v1_xboole_0(k1_zfmisc_1(A_83)))), inference(resolution, [status(thm)], [c_36, c_277])).
% 4.68/1.93  tff(c_286, plain, (![B_84, A_85]: (r1_tarski(B_84, A_85) | ~m1_subset_1(B_84, k1_zfmisc_1(A_85)))), inference(negUnitSimplification, [status(thm)], [c_46, c_281])).
% 4.68/1.93  tff(c_299, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_286])).
% 4.68/1.93  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, B_4)=A_3 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.68/1.93  tff(c_308, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_299, c_4])).
% 4.68/1.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.68/1.93  tff(c_326, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_308, c_2])).
% 4.68/1.93  tff(c_455, plain, (![A_99, B_100]: (k5_xboole_0(k5_xboole_0(A_99, B_100), k3_xboole_0(A_99, B_100))=k2_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.68/1.93  tff(c_476, plain, (k5_xboole_0(k5_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_326, c_455])).
% 4.68/1.93  tff(c_8, plain, (![A_6, B_7, C_8]: (k5_xboole_0(k5_xboole_0(A_6, B_7), C_8)=k5_xboole_0(A_6, k5_xboole_0(B_7, C_8)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.68/1.93  tff(c_1222, plain, (k5_xboole_0('#skF_1', k5_xboole_0('#skF_2', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_476, c_8])).
% 4.68/1.93  tff(c_1232, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_10, c_1222])).
% 4.68/1.93  tff(c_14, plain, (![B_13, A_12]: (k2_tarski(B_13, A_12)=k2_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.68/1.93  tff(c_194, plain, (![A_72, B_73]: (k3_tarski(k2_tarski(A_72, B_73))=k2_xboole_0(A_72, B_73))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.68/1.93  tff(c_217, plain, (![B_76, A_77]: (k3_tarski(k2_tarski(B_76, A_77))=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_14, c_194])).
% 4.68/1.93  tff(c_30, plain, (![A_43, B_44]: (k3_tarski(k2_tarski(A_43, B_44))=k2_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.68/1.93  tff(c_223, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_217, c_30])).
% 4.68/1.93  tff(c_44, plain, (![A_49]: (m1_subset_1(k2_subset_1(A_49), k1_zfmisc_1(A_49)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 4.68/1.93  tff(c_54, plain, (![A_49]: (m1_subset_1(A_49, k1_zfmisc_1(A_49)))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_44])).
% 4.68/1.93  tff(c_1960, plain, (![A_144, B_145, C_146]: (k4_subset_1(A_144, B_145, C_146)=k2_xboole_0(B_145, C_146) | ~m1_subset_1(C_146, k1_zfmisc_1(A_144)) | ~m1_subset_1(B_145, k1_zfmisc_1(A_144)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.68/1.93  tff(c_4583, plain, (![A_193, B_194]: (k4_subset_1(A_193, B_194, A_193)=k2_xboole_0(B_194, A_193) | ~m1_subset_1(B_194, k1_zfmisc_1(A_193)))), inference(resolution, [status(thm)], [c_54, c_1960])).
% 4.68/1.93  tff(c_4590, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')=k2_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_52, c_4583])).
% 4.68/1.93  tff(c_4595, plain, (k4_subset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1232, c_223, c_4590])).
% 4.68/1.93  tff(c_4597, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_4595])).
% 4.68/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.68/1.93  
% 4.68/1.93  Inference rules
% 4.68/1.93  ----------------------
% 4.68/1.93  #Ref     : 0
% 4.68/1.93  #Sup     : 1083
% 4.68/1.93  #Fact    : 0
% 4.68/1.93  #Define  : 0
% 4.68/1.93  #Split   : 0
% 4.68/1.93  #Chain   : 0
% 4.68/1.93  #Close   : 0
% 4.68/1.93  
% 4.68/1.93  Ordering : KBO
% 4.68/1.93  
% 4.68/1.93  Simplification rules
% 4.68/1.93  ----------------------
% 4.68/1.93  #Subsume      : 40
% 4.68/1.93  #Demod        : 896
% 4.68/1.93  #Tautology    : 687
% 4.68/1.93  #SimpNegUnit  : 4
% 4.68/1.93  #BackRed      : 9
% 4.68/1.93  
% 4.68/1.93  #Partial instantiations: 0
% 4.68/1.93  #Strategies tried      : 1
% 4.68/1.93  
% 4.68/1.93  Timing (in seconds)
% 4.68/1.93  ----------------------
% 4.68/1.93  Preprocessing        : 0.35
% 4.68/1.93  Parsing              : 0.19
% 4.68/1.93  CNF conversion       : 0.02
% 4.68/1.93  Main loop            : 0.76
% 4.68/1.93  Inferencing          : 0.24
% 4.68/1.93  Reduction            : 0.34
% 4.68/1.93  Demodulation         : 0.28
% 4.68/1.93  BG Simplification    : 0.03
% 4.68/1.93  Subsumption          : 0.10
% 4.68/1.93  Abstraction          : 0.04
% 4.68/1.93  MUC search           : 0.00
% 4.68/1.93  Cooper               : 0.00
% 4.68/1.93  Total                : 1.14
% 4.68/1.93  Index Insertion      : 0.00
% 4.68/1.94  Index Deletion       : 0.00
% 4.68/1.94  Index Matching       : 0.00
% 4.68/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
