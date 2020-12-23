%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 2.34s
% Output     : CNFRefutation 2.34s
% Verified   : 
% Statistics : Number of formulae       :   67 (  73 expanded)
%              Number of leaves         :   40 (  43 expanded)
%              Depth                    :    9
%              Number of atoms          :   61 (  67 expanded)
%              Number of equality atoms :   29 (  31 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k3_yellow_1,type,(
    k3_yellow_1: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_yellow_1,type,(
    k2_yellow_1: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k9_setfam_1,type,(
    k9_setfam_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k3_subset_1,type,(
    k3_subset_1: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(k4_yellow_0,type,(
    k4_yellow_0: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_62,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_64,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_subset)).

tff(f_80,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_89,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_51,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_87,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_92,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_30,plain,(
    ! [A_41] : ~ v1_xboole_0(k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [A_42] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_42)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_10,plain,(
    ! [A_8] : k5_xboole_0(A_8,k1_xboole_0) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7] : k3_xboole_0(A_7,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_117,plain,(
    ! [A_67,B_68] : k5_xboole_0(A_67,k3_xboole_0(A_67,B_68)) = k4_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_126,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = k4_xboole_0(A_7,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_117])).

tff(c_129,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_126])).

tff(c_170,plain,(
    ! [A_82,B_83] :
      ( k4_xboole_0(A_82,B_83) = k3_subset_1(A_82,B_83)
      | ~ m1_subset_1(B_83,k1_zfmisc_1(A_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_176,plain,(
    ! [A_42] : k4_xboole_0(A_42,k1_xboole_0) = k3_subset_1(A_42,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_32,c_170])).

tff(c_180,plain,(
    ! [A_84] : k3_subset_1(A_84,k1_xboole_0) = A_84 ),
    inference(demodulation,[status(thm),theory(equality)],[c_129,c_176])).

tff(c_28,plain,(
    ! [A_39,B_40] :
      ( m1_subset_1(k3_subset_1(A_39,B_40),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(B_40,k1_zfmisc_1(A_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_186,plain,(
    ! [A_84] :
      ( m1_subset_1(A_84,k1_zfmisc_1(A_84))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_84)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_180,c_28])).

tff(c_192,plain,(
    ! [A_84] : m1_subset_1(A_84,k1_zfmisc_1(A_84)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_186])).

tff(c_36,plain,(
    ! [A_45,B_46] :
      ( r2_hidden(A_45,B_46)
      | v1_xboole_0(B_46)
      | ~ m1_subset_1(A_45,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_40,plain,(
    ! [A_50] : k9_setfam_1(A_50) = k1_zfmisc_1(A_50) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_44,plain,(
    ! [A_52] : k2_yellow_1(k9_setfam_1(A_52)) = k3_yellow_1(A_52) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_47,plain,(
    ! [A_52] : k2_yellow_1(k1_zfmisc_1(A_52)) = k3_yellow_1(A_52) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_44])).

tff(c_24,plain,(
    ! [A_36] : k3_tarski(k1_zfmisc_1(A_36)) = A_36 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_222,plain,(
    ! [A_87] :
      ( k4_yellow_0(k2_yellow_1(A_87)) = k3_tarski(A_87)
      | ~ r2_hidden(k3_tarski(A_87),A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_229,plain,(
    ! [A_36] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_36))) = k3_tarski(k1_zfmisc_1(A_36))
      | ~ r2_hidden(A_36,k1_zfmisc_1(A_36))
      | v1_xboole_0(k1_zfmisc_1(A_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_222])).

tff(c_231,plain,(
    ! [A_36] :
      ( k4_yellow_0(k3_yellow_1(A_36)) = A_36
      | ~ r2_hidden(A_36,k1_zfmisc_1(A_36))
      | v1_xboole_0(k1_zfmisc_1(A_36)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_47,c_24,c_229])).

tff(c_256,plain,(
    ! [A_91] :
      ( k4_yellow_0(k3_yellow_1(A_91)) = A_91
      | ~ r2_hidden(A_91,k1_zfmisc_1(A_91)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_231])).

tff(c_260,plain,(
    ! [A_45] :
      ( k4_yellow_0(k3_yellow_1(A_45)) = A_45
      | v1_xboole_0(k1_zfmisc_1(A_45))
      | ~ m1_subset_1(A_45,k1_zfmisc_1(A_45)) ) ),
    inference(resolution,[status(thm)],[c_36,c_256])).

tff(c_263,plain,(
    ! [A_45] :
      ( k4_yellow_0(k3_yellow_1(A_45)) = A_45
      | v1_xboole_0(k1_zfmisc_1(A_45)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_192,c_260])).

tff(c_264,plain,(
    ! [A_45] : k4_yellow_0(k3_yellow_1(A_45)) = A_45 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_263])).

tff(c_46,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_277,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_46])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:32:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.34/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.27  
% 2.34/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.27  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2
% 2.34/1.27  
% 2.34/1.27  %Foreground sorts:
% 2.34/1.27  
% 2.34/1.27  
% 2.34/1.27  %Background operators:
% 2.34/1.27  
% 2.34/1.27  
% 2.34/1.27  %Foreground operators:
% 2.34/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.34/1.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.34/1.27  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.34/1.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.34/1.27  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.34/1.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.34/1.27  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.34/1.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.34/1.27  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.34/1.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.34/1.27  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.34/1.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.34/1.27  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.34/1.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.34/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.34/1.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.34/1.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.34/1.27  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.34/1.27  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.34/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.34/1.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.34/1.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.34/1.27  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.34/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.34/1.27  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.34/1.27  
% 2.34/1.28  tff(f_62, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.34/1.28  tff(f_64, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.34/1.28  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.34/1.28  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 2.34/1.28  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.34/1.28  tff(f_55, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_subset_1)).
% 2.34/1.28  tff(f_59, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.34/1.28  tff(f_72, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_subset)).
% 2.34/1.28  tff(f_80, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.34/1.28  tff(f_89, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.34/1.28  tff(f_51, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.34/1.28  tff(f_87, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.34/1.28  tff(f_92, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.34/1.28  tff(c_30, plain, (![A_41]: (~v1_xboole_0(k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.34/1.28  tff(c_32, plain, (![A_42]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_42)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.34/1.28  tff(c_10, plain, (![A_8]: (k5_xboole_0(A_8, k1_xboole_0)=A_8)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.34/1.28  tff(c_8, plain, (![A_7]: (k3_xboole_0(A_7, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.34/1.28  tff(c_117, plain, (![A_67, B_68]: (k5_xboole_0(A_67, k3_xboole_0(A_67, B_68))=k4_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.34/1.28  tff(c_126, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=k4_xboole_0(A_7, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_117])).
% 2.34/1.28  tff(c_129, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_126])).
% 2.34/1.28  tff(c_170, plain, (![A_82, B_83]: (k4_xboole_0(A_82, B_83)=k3_subset_1(A_82, B_83) | ~m1_subset_1(B_83, k1_zfmisc_1(A_82)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.34/1.28  tff(c_176, plain, (![A_42]: (k4_xboole_0(A_42, k1_xboole_0)=k3_subset_1(A_42, k1_xboole_0))), inference(resolution, [status(thm)], [c_32, c_170])).
% 2.34/1.28  tff(c_180, plain, (![A_84]: (k3_subset_1(A_84, k1_xboole_0)=A_84)), inference(demodulation, [status(thm), theory('equality')], [c_129, c_176])).
% 2.34/1.28  tff(c_28, plain, (![A_39, B_40]: (m1_subset_1(k3_subset_1(A_39, B_40), k1_zfmisc_1(A_39)) | ~m1_subset_1(B_40, k1_zfmisc_1(A_39)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.34/1.28  tff(c_186, plain, (![A_84]: (m1_subset_1(A_84, k1_zfmisc_1(A_84)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_84)))), inference(superposition, [status(thm), theory('equality')], [c_180, c_28])).
% 2.34/1.28  tff(c_192, plain, (![A_84]: (m1_subset_1(A_84, k1_zfmisc_1(A_84)))), inference(demodulation, [status(thm), theory('equality')], [c_32, c_186])).
% 2.34/1.28  tff(c_36, plain, (![A_45, B_46]: (r2_hidden(A_45, B_46) | v1_xboole_0(B_46) | ~m1_subset_1(A_45, B_46))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.34/1.28  tff(c_40, plain, (![A_50]: (k9_setfam_1(A_50)=k1_zfmisc_1(A_50))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.34/1.28  tff(c_44, plain, (![A_52]: (k2_yellow_1(k9_setfam_1(A_52))=k3_yellow_1(A_52))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.34/1.28  tff(c_47, plain, (![A_52]: (k2_yellow_1(k1_zfmisc_1(A_52))=k3_yellow_1(A_52))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_44])).
% 2.34/1.28  tff(c_24, plain, (![A_36]: (k3_tarski(k1_zfmisc_1(A_36))=A_36)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.34/1.28  tff(c_222, plain, (![A_87]: (k4_yellow_0(k2_yellow_1(A_87))=k3_tarski(A_87) | ~r2_hidden(k3_tarski(A_87), A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.34/1.28  tff(c_229, plain, (![A_36]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_36)))=k3_tarski(k1_zfmisc_1(A_36)) | ~r2_hidden(A_36, k1_zfmisc_1(A_36)) | v1_xboole_0(k1_zfmisc_1(A_36)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_222])).
% 2.34/1.28  tff(c_231, plain, (![A_36]: (k4_yellow_0(k3_yellow_1(A_36))=A_36 | ~r2_hidden(A_36, k1_zfmisc_1(A_36)) | v1_xboole_0(k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_47, c_24, c_229])).
% 2.34/1.28  tff(c_256, plain, (![A_91]: (k4_yellow_0(k3_yellow_1(A_91))=A_91 | ~r2_hidden(A_91, k1_zfmisc_1(A_91)))), inference(negUnitSimplification, [status(thm)], [c_30, c_231])).
% 2.34/1.28  tff(c_260, plain, (![A_45]: (k4_yellow_0(k3_yellow_1(A_45))=A_45 | v1_xboole_0(k1_zfmisc_1(A_45)) | ~m1_subset_1(A_45, k1_zfmisc_1(A_45)))), inference(resolution, [status(thm)], [c_36, c_256])).
% 2.34/1.28  tff(c_263, plain, (![A_45]: (k4_yellow_0(k3_yellow_1(A_45))=A_45 | v1_xboole_0(k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_192, c_260])).
% 2.34/1.28  tff(c_264, plain, (![A_45]: (k4_yellow_0(k3_yellow_1(A_45))=A_45)), inference(negUnitSimplification, [status(thm)], [c_30, c_263])).
% 2.34/1.28  tff(c_46, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.34/1.28  tff(c_277, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_264, c_46])).
% 2.34/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.34/1.28  
% 2.34/1.28  Inference rules
% 2.34/1.28  ----------------------
% 2.34/1.28  #Ref     : 0
% 2.34/1.28  #Sup     : 47
% 2.34/1.28  #Fact    : 0
% 2.34/1.28  #Define  : 0
% 2.34/1.28  #Split   : 1
% 2.34/1.28  #Chain   : 0
% 2.34/1.28  #Close   : 0
% 2.34/1.28  
% 2.34/1.28  Ordering : KBO
% 2.34/1.28  
% 2.34/1.28  Simplification rules
% 2.34/1.28  ----------------------
% 2.34/1.28  #Subsume      : 0
% 2.34/1.28  #Demod        : 11
% 2.34/1.28  #Tautology    : 32
% 2.34/1.28  #SimpNegUnit  : 4
% 2.34/1.28  #BackRed      : 1
% 2.34/1.28  
% 2.34/1.28  #Partial instantiations: 0
% 2.34/1.28  #Strategies tried      : 1
% 2.34/1.28  
% 2.34/1.28  Timing (in seconds)
% 2.34/1.28  ----------------------
% 2.34/1.29  Preprocessing        : 0.33
% 2.34/1.29  Parsing              : 0.18
% 2.34/1.29  CNF conversion       : 0.02
% 2.34/1.29  Main loop            : 0.19
% 2.34/1.29  Inferencing          : 0.07
% 2.34/1.29  Reduction            : 0.06
% 2.34/1.29  Demodulation         : 0.04
% 2.34/1.29  BG Simplification    : 0.02
% 2.34/1.29  Subsumption          : 0.02
% 2.34/1.29  Abstraction          : 0.01
% 2.34/1.29  MUC search           : 0.00
% 2.34/1.29  Cooper               : 0.00
% 2.34/1.29  Total                : 0.55
% 2.34/1.29  Index Insertion      : 0.00
% 2.34/1.29  Index Deletion       : 0.00
% 2.34/1.29  Index Matching       : 0.00
% 2.34/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
