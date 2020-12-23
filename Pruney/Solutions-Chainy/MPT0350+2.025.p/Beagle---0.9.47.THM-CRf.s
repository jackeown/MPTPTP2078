%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:55:29 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.69s
% Verified   : 
% Statistics : Number of formulae       :   61 (  78 expanded)
%              Number of leaves         :   28 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   61 (  88 expanded)
%              Number of equality atoms :   39 (  50 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k4_subset_1,type,(
    k4_subset_1: ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_41,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k4_subset_1(A,B,k3_subset_1(A,B)) = k2_subset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_subset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,k3_subset_1(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( ( m1_subset_1(B,k1_zfmisc_1(A))
        & m1_subset_1(C,k1_zfmisc_1(A)) )
     => k4_subset_1(A,B,C) = k2_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

tff(c_16,plain,(
    ! [A_15] : k2_subset_1(A_15) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != k2_subset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_29,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_26])).

tff(c_28,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_203,plain,(
    ! [A_46,B_47] :
      ( k4_xboole_0(A_46,B_47) = k3_subset_1(A_46,B_47)
      | ~ m1_subset_1(B_47,k1_zfmisc_1(A_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_207,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k3_subset_1('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_28,c_203])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_215,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_8])).

tff(c_199,plain,(
    ! [A_44,B_45] :
      ( k3_subset_1(A_44,k3_subset_1(A_44,B_45)) = B_45
      | ~ m1_subset_1(B_45,k1_zfmisc_1(A_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_202,plain,(
    k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_28,c_199])).

tff(c_238,plain,(
    ! [A_48,B_49] :
      ( m1_subset_1(k3_subset_1(A_48,B_49),k1_zfmisc_1(A_48))
      | ~ m1_subset_1(B_49,k1_zfmisc_1(A_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_18,plain,(
    ! [A_16,B_17] :
      ( k4_xboole_0(A_16,B_17) = k3_subset_1(A_16,B_17)
      | ~ m1_subset_1(B_17,k1_zfmisc_1(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_505,plain,(
    ! [A_66,B_67] :
      ( k4_xboole_0(A_66,k3_subset_1(A_66,B_67)) = k3_subset_1(A_66,k3_subset_1(A_66,B_67))
      | ~ m1_subset_1(B_67,k1_zfmisc_1(A_66)) ) ),
    inference(resolution,[status(thm)],[c_238,c_18])).

tff(c_509,plain,(
    k4_xboole_0('#skF_1',k3_subset_1('#skF_1','#skF_2')) = k3_subset_1('#skF_1',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_505])).

tff(c_512,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_202,c_509])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_539,plain,(
    k2_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_512,c_4])).

tff(c_10,plain,(
    ! [B_10,A_9] : k2_tarski(B_10,A_9) = k2_tarski(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_90,plain,(
    ! [A_32,B_33] : k3_tarski(k2_tarski(A_32,B_33)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [B_34,A_35] : k3_tarski(k2_tarski(B_34,A_35)) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_90])).

tff(c_14,plain,(
    ! [A_13,B_14] : k3_tarski(k2_tarski(A_13,B_14)) = k2_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_111,plain,(
    ! [B_34,A_35] : k2_xboole_0(B_34,A_35) = k2_xboole_0(A_35,B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_14])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = k2_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_218,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_6])).

tff(c_221,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_111,c_218])).

tff(c_549,plain,(
    k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_539,c_221])).

tff(c_20,plain,(
    ! [A_18,B_19] :
      ( m1_subset_1(k3_subset_1(A_18,B_19),k1_zfmisc_1(A_18))
      | ~ m1_subset_1(B_19,k1_zfmisc_1(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_310,plain,(
    ! [A_54,B_55,C_56] :
      ( k4_subset_1(A_54,B_55,C_56) = k2_xboole_0(B_55,C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(A_54))
      | ~ m1_subset_1(B_55,k1_zfmisc_1(A_54)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_730,plain,(
    ! [A_70,B_71,B_72] :
      ( k4_subset_1(A_70,B_71,k3_subset_1(A_70,B_72)) = k2_xboole_0(B_71,k3_subset_1(A_70,B_72))
      | ~ m1_subset_1(B_71,k1_zfmisc_1(A_70))
      | ~ m1_subset_1(B_72,k1_zfmisc_1(A_70)) ) ),
    inference(resolution,[status(thm)],[c_20,c_310])).

tff(c_740,plain,(
    ! [B_73] :
      ( k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1',B_73)) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1',B_73))
      | ~ m1_subset_1(B_73,k1_zfmisc_1('#skF_1')) ) ),
    inference(resolution,[status(thm)],[c_28,c_730])).

tff(c_747,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = k2_xboole_0('#skF_2',k3_subset_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_28,c_740])).

tff(c_750,plain,(
    k4_subset_1('#skF_1','#skF_2',k3_subset_1('#skF_1','#skF_2')) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_549,c_747])).

tff(c_752,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_29,c_750])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:41:35 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.44  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.45  
% 2.69/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.45  %$ m1_subset_1 > k4_subset_1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > #skF_2 > #skF_1
% 2.69/1.45  
% 2.69/1.45  %Foreground sorts:
% 2.69/1.45  
% 2.69/1.45  
% 2.69/1.45  %Background operators:
% 2.69/1.45  
% 2.69/1.45  
% 2.69/1.45  %Foreground operators:
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.45  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.45  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.69/1.45  tff(k4_subset_1, type, k4_subset_1: ($i * $i * $i) > $i).
% 2.69/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.69/1.45  tff('#skF_1', type, '#skF_1': $i).
% 2.69/1.45  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.45  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.69/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.45  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.69/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.69/1.45  
% 2.69/1.46  tff(f_41, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.69/1.46  tff(f_64, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k4_subset_1(A, B, k3_subset_1(A, B)) = k2_subset_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_subset_1)).
% 2.69/1.46  tff(f_45, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.69/1.46  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.69/1.46  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, k3_subset_1(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', involutiveness_k3_subset_1)).
% 2.69/1.46  tff(f_49, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.69/1.46  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.69/1.46  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.69/1.46  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.69/1.46  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.69/1.46  tff(f_59, axiom, (![A, B, C]: ((m1_subset_1(B, k1_zfmisc_1(A)) & m1_subset_1(C, k1_zfmisc_1(A))) => (k4_subset_1(A, B, C) = k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_subset_1)).
% 2.69/1.46  tff(c_16, plain, (![A_15]: (k2_subset_1(A_15)=A_15)), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.69/1.46  tff(c_26, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!=k2_subset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.46  tff(c_29, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_26])).
% 2.69/1.46  tff(c_28, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.69/1.46  tff(c_203, plain, (![A_46, B_47]: (k4_xboole_0(A_46, B_47)=k3_subset_1(A_46, B_47) | ~m1_subset_1(B_47, k1_zfmisc_1(A_46)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.46  tff(c_207, plain, (k4_xboole_0('#skF_1', '#skF_2')=k3_subset_1('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_28, c_203])).
% 2.69/1.46  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.69/1.46  tff(c_215, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_207, c_8])).
% 2.69/1.46  tff(c_199, plain, (![A_44, B_45]: (k3_subset_1(A_44, k3_subset_1(A_44, B_45))=B_45 | ~m1_subset_1(B_45, k1_zfmisc_1(A_44)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.69/1.46  tff(c_202, plain, (k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))='#skF_2'), inference(resolution, [status(thm)], [c_28, c_199])).
% 2.69/1.46  tff(c_238, plain, (![A_48, B_49]: (m1_subset_1(k3_subset_1(A_48, B_49), k1_zfmisc_1(A_48)) | ~m1_subset_1(B_49, k1_zfmisc_1(A_48)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.46  tff(c_18, plain, (![A_16, B_17]: (k4_xboole_0(A_16, B_17)=k3_subset_1(A_16, B_17) | ~m1_subset_1(B_17, k1_zfmisc_1(A_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.69/1.46  tff(c_505, plain, (![A_66, B_67]: (k4_xboole_0(A_66, k3_subset_1(A_66, B_67))=k3_subset_1(A_66, k3_subset_1(A_66, B_67)) | ~m1_subset_1(B_67, k1_zfmisc_1(A_66)))), inference(resolution, [status(thm)], [c_238, c_18])).
% 2.69/1.46  tff(c_509, plain, (k4_xboole_0('#skF_1', k3_subset_1('#skF_1', '#skF_2'))=k3_subset_1('#skF_1', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_505])).
% 2.69/1.46  tff(c_512, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_215, c_202, c_509])).
% 2.69/1.46  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.69/1.46  tff(c_539, plain, (k2_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_512, c_4])).
% 2.69/1.46  tff(c_10, plain, (![B_10, A_9]: (k2_tarski(B_10, A_9)=k2_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.69/1.46  tff(c_90, plain, (![A_32, B_33]: (k3_tarski(k2_tarski(A_32, B_33))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.46  tff(c_105, plain, (![B_34, A_35]: (k3_tarski(k2_tarski(B_34, A_35))=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_10, c_90])).
% 2.69/1.46  tff(c_14, plain, (![A_13, B_14]: (k3_tarski(k2_tarski(A_13, B_14))=k2_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.69/1.46  tff(c_111, plain, (![B_34, A_35]: (k2_xboole_0(B_34, A_35)=k2_xboole_0(A_35, B_34))), inference(superposition, [status(thm), theory('equality')], [c_105, c_14])).
% 2.69/1.46  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=k2_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.69/1.46  tff(c_218, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_207, c_6])).
% 2.69/1.46  tff(c_221, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_111, c_218])).
% 2.69/1.46  tff(c_549, plain, (k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_539, c_221])).
% 2.69/1.46  tff(c_20, plain, (![A_18, B_19]: (m1_subset_1(k3_subset_1(A_18, B_19), k1_zfmisc_1(A_18)) | ~m1_subset_1(B_19, k1_zfmisc_1(A_18)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.69/1.46  tff(c_310, plain, (![A_54, B_55, C_56]: (k4_subset_1(A_54, B_55, C_56)=k2_xboole_0(B_55, C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(A_54)) | ~m1_subset_1(B_55, k1_zfmisc_1(A_54)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.69/1.46  tff(c_730, plain, (![A_70, B_71, B_72]: (k4_subset_1(A_70, B_71, k3_subset_1(A_70, B_72))=k2_xboole_0(B_71, k3_subset_1(A_70, B_72)) | ~m1_subset_1(B_71, k1_zfmisc_1(A_70)) | ~m1_subset_1(B_72, k1_zfmisc_1(A_70)))), inference(resolution, [status(thm)], [c_20, c_310])).
% 2.69/1.46  tff(c_740, plain, (![B_73]: (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', B_73))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', B_73)) | ~m1_subset_1(B_73, k1_zfmisc_1('#skF_1')))), inference(resolution, [status(thm)], [c_28, c_730])).
% 2.69/1.46  tff(c_747, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))=k2_xboole_0('#skF_2', k3_subset_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_28, c_740])).
% 2.69/1.46  tff(c_750, plain, (k4_subset_1('#skF_1', '#skF_2', k3_subset_1('#skF_1', '#skF_2'))='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_549, c_747])).
% 2.69/1.46  tff(c_752, plain, $false, inference(negUnitSimplification, [status(thm)], [c_29, c_750])).
% 2.69/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.69/1.46  
% 2.69/1.46  Inference rules
% 2.69/1.46  ----------------------
% 2.69/1.46  #Ref     : 0
% 2.69/1.46  #Sup     : 196
% 2.69/1.46  #Fact    : 0
% 2.69/1.46  #Define  : 0
% 2.69/1.46  #Split   : 0
% 2.69/1.46  #Chain   : 0
% 2.69/1.46  #Close   : 0
% 2.69/1.46  
% 2.69/1.46  Ordering : KBO
% 2.69/1.46  
% 2.69/1.46  Simplification rules
% 2.69/1.46  ----------------------
% 2.69/1.46  #Subsume      : 4
% 2.69/1.46  #Demod        : 151
% 2.69/1.46  #Tautology    : 119
% 2.69/1.46  #SimpNegUnit  : 1
% 2.69/1.46  #BackRed      : 7
% 2.69/1.46  
% 2.69/1.46  #Partial instantiations: 0
% 2.69/1.46  #Strategies tried      : 1
% 2.69/1.46  
% 2.69/1.47  Timing (in seconds)
% 2.69/1.47  ----------------------
% 2.69/1.47  Preprocessing        : 0.31
% 2.98/1.47  Parsing              : 0.18
% 2.98/1.47  CNF conversion       : 0.02
% 2.98/1.47  Main loop            : 0.35
% 2.98/1.47  Inferencing          : 0.12
% 2.98/1.47  Reduction            : 0.14
% 2.98/1.47  Demodulation         : 0.11
% 2.98/1.47  BG Simplification    : 0.02
% 2.98/1.47  Subsumption          : 0.05
% 2.98/1.47  Abstraction          : 0.02
% 2.98/1.47  MUC search           : 0.00
% 2.98/1.47  Cooper               : 0.00
% 2.98/1.47  Total                : 0.69
% 2.98/1.47  Index Insertion      : 0.00
% 2.98/1.47  Index Deletion       : 0.00
% 2.98/1.47  Index Matching       : 0.00
% 2.98/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
