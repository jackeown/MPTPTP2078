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
% DateTime   : Thu Dec  3 10:25:33 EST 2020

% Result     : Theorem 2.13s
% Output     : CNFRefutation 2.13s
% Verified   : 
% Statistics : Number of formulae       :   61 (  67 expanded)
%              Number of leaves         :   38 (  41 expanded)
%              Depth                    :    8
%              Number of atoms          :   55 (  61 expanded)
%              Number of equality atoms :   23 (  25 expanded)
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

tff(f_60,axiom,(
    ! [A] : ~ v1_xboole_0(k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_subset_1)).

tff(f_62,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_35,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => k3_subset_1(A,B) = k4_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
     => m1_subset_1(k3_subset_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,B)
     => ( v1_xboole_0(B)
        | r2_hidden(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

tff(f_78,axiom,(
    ! [A] : k9_setfam_1(A) = k1_zfmisc_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_setfam_1)).

tff(f_87,axiom,(
    ! [A] : k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_yellow_1)).

tff(f_49,axiom,(
    ! [A] : k3_tarski(k1_zfmisc_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_zfmisc_1)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( r2_hidden(k3_tarski(A),A)
       => k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_yellow_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] : k4_yellow_0(k3_yellow_1(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_yellow_1)).

tff(c_28,plain,(
    ! [A_40] : ~ v1_xboole_0(k1_zfmisc_1(A_40)) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_30,plain,(
    ! [A_41] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_41)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_132,plain,(
    ! [A_74,B_75] :
      ( k4_xboole_0(A_74,B_75) = k3_subset_1(A_74,B_75)
      | ~ m1_subset_1(B_75,k1_zfmisc_1(A_74)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_138,plain,(
    ! [A_41] : k4_xboole_0(A_41,k1_xboole_0) = k3_subset_1(A_41,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_132])).

tff(c_142,plain,(
    ! [A_76] : k3_subset_1(A_76,k1_xboole_0) = A_76 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_138])).

tff(c_26,plain,(
    ! [A_38,B_39] :
      ( m1_subset_1(k3_subset_1(A_38,B_39),k1_zfmisc_1(A_38))
      | ~ m1_subset_1(B_39,k1_zfmisc_1(A_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_148,plain,(
    ! [A_76] :
      ( m1_subset_1(A_76,k1_zfmisc_1(A_76))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_76)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_26])).

tff(c_154,plain,(
    ! [A_76] : m1_subset_1(A_76,k1_zfmisc_1(A_76)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_148])).

tff(c_34,plain,(
    ! [A_44,B_45] :
      ( r2_hidden(A_44,B_45)
      | v1_xboole_0(B_45)
      | ~ m1_subset_1(A_44,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_38,plain,(
    ! [A_49] : k9_setfam_1(A_49) = k1_zfmisc_1(A_49) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_42,plain,(
    ! [A_51] : k2_yellow_1(k9_setfam_1(A_51)) = k3_yellow_1(A_51) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_45,plain,(
    ! [A_51] : k2_yellow_1(k1_zfmisc_1(A_51)) = k3_yellow_1(A_51) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_42])).

tff(c_22,plain,(
    ! [A_35] : k3_tarski(k1_zfmisc_1(A_35)) = A_35 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_223,plain,(
    ! [A_87] :
      ( k4_yellow_0(k2_yellow_1(A_87)) = k3_tarski(A_87)
      | ~ r2_hidden(k3_tarski(A_87),A_87)
      | v1_xboole_0(A_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_230,plain,(
    ! [A_35] :
      ( k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_35))) = k3_tarski(k1_zfmisc_1(A_35))
      | ~ r2_hidden(A_35,k1_zfmisc_1(A_35))
      | v1_xboole_0(k1_zfmisc_1(A_35)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_223])).

tff(c_232,plain,(
    ! [A_35] :
      ( k4_yellow_0(k3_yellow_1(A_35)) = A_35
      | ~ r2_hidden(A_35,k1_zfmisc_1(A_35))
      | v1_xboole_0(k1_zfmisc_1(A_35)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_22,c_230])).

tff(c_234,plain,(
    ! [A_88] :
      ( k4_yellow_0(k3_yellow_1(A_88)) = A_88
      | ~ r2_hidden(A_88,k1_zfmisc_1(A_88)) ) ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_232])).

tff(c_238,plain,(
    ! [A_44] :
      ( k4_yellow_0(k3_yellow_1(A_44)) = A_44
      | v1_xboole_0(k1_zfmisc_1(A_44))
      | ~ m1_subset_1(A_44,k1_zfmisc_1(A_44)) ) ),
    inference(resolution,[status(thm)],[c_34,c_234])).

tff(c_241,plain,(
    ! [A_44] :
      ( k4_yellow_0(k3_yellow_1(A_44)) = A_44
      | v1_xboole_0(k1_zfmisc_1(A_44)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_238])).

tff(c_242,plain,(
    ! [A_44] : k4_yellow_0(k3_yellow_1(A_44)) = A_44 ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_241])).

tff(c_44,plain,(
    k4_yellow_0(k3_yellow_1('#skF_2')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_246,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_242,c_44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n024.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:05:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.13/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  
% 2.13/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.26  %$ r2_hidden > m1_subset_1 > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k3_subset_1 > k2_tarski > #nlpp > k9_setfam_1 > k4_yellow_0 > k3_yellow_1 > k3_tarski > k2_yellow_1 > k1_zfmisc_1 > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2
% 2.13/1.26  
% 2.13/1.26  %Foreground sorts:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Background operators:
% 2.13/1.26  
% 2.13/1.26  
% 2.13/1.26  %Foreground operators:
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.13/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.13/1.26  tff(k3_yellow_1, type, k3_yellow_1: $i > $i).
% 2.13/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.13/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.13/1.26  tff(k2_yellow_1, type, k2_yellow_1: $i > $i).
% 2.13/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.13/1.26  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.13/1.26  tff(k9_setfam_1, type, k9_setfam_1: $i > $i).
% 2.13/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.13/1.26  tff(k3_subset_1, type, k3_subset_1: ($i * $i) > $i).
% 2.13/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.13/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.13/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.13/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.13/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.13/1.26  tff(k4_yellow_0, type, k4_yellow_0: $i > $i).
% 2.13/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.13/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.13/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.13/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.13/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.13/1.26  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.13/1.26  
% 2.13/1.27  tff(f_60, axiom, (![A]: ~v1_xboole_0(k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_subset_1)).
% 2.13/1.27  tff(f_62, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.13/1.27  tff(f_35, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.13/1.27  tff(f_53, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k3_subset_1(A, B) = k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_subset_1)).
% 2.13/1.27  tff(f_57, axiom, (![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => m1_subset_1(k3_subset_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k3_subset_1)).
% 2.13/1.27  tff(f_70, axiom, (![A, B]: (m1_subset_1(A, B) => (v1_xboole_0(B) | r2_hidden(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_subset)).
% 2.13/1.27  tff(f_78, axiom, (![A]: (k9_setfam_1(A) = k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k9_setfam_1)).
% 2.13/1.27  tff(f_87, axiom, (![A]: (k3_yellow_1(A) = k2_yellow_1(k9_setfam_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_yellow_1)).
% 2.13/1.27  tff(f_49, axiom, (![A]: (k3_tarski(k1_zfmisc_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_zfmisc_1)).
% 2.13/1.27  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (r2_hidden(k3_tarski(A), A) => (k4_yellow_0(k2_yellow_1(A)) = k3_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_yellow_1)).
% 2.13/1.27  tff(f_90, negated_conjecture, ~(![A]: (k4_yellow_0(k3_yellow_1(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_yellow_1)).
% 2.13/1.27  tff(c_28, plain, (![A_40]: (~v1_xboole_0(k1_zfmisc_1(A_40)))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.13/1.27  tff(c_30, plain, (![A_41]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_41)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.13/1.27  tff(c_8, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.13/1.27  tff(c_132, plain, (![A_74, B_75]: (k4_xboole_0(A_74, B_75)=k3_subset_1(A_74, B_75) | ~m1_subset_1(B_75, k1_zfmisc_1(A_74)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.13/1.27  tff(c_138, plain, (![A_41]: (k4_xboole_0(A_41, k1_xboole_0)=k3_subset_1(A_41, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_132])).
% 2.13/1.27  tff(c_142, plain, (![A_76]: (k3_subset_1(A_76, k1_xboole_0)=A_76)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_138])).
% 2.13/1.27  tff(c_26, plain, (![A_38, B_39]: (m1_subset_1(k3_subset_1(A_38, B_39), k1_zfmisc_1(A_38)) | ~m1_subset_1(B_39, k1_zfmisc_1(A_38)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.13/1.27  tff(c_148, plain, (![A_76]: (m1_subset_1(A_76, k1_zfmisc_1(A_76)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_76)))), inference(superposition, [status(thm), theory('equality')], [c_142, c_26])).
% 2.13/1.27  tff(c_154, plain, (![A_76]: (m1_subset_1(A_76, k1_zfmisc_1(A_76)))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_148])).
% 2.13/1.27  tff(c_34, plain, (![A_44, B_45]: (r2_hidden(A_44, B_45) | v1_xboole_0(B_45) | ~m1_subset_1(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.13/1.27  tff(c_38, plain, (![A_49]: (k9_setfam_1(A_49)=k1_zfmisc_1(A_49))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.13/1.27  tff(c_42, plain, (![A_51]: (k2_yellow_1(k9_setfam_1(A_51))=k3_yellow_1(A_51))), inference(cnfTransformation, [status(thm)], [f_87])).
% 2.13/1.27  tff(c_45, plain, (![A_51]: (k2_yellow_1(k1_zfmisc_1(A_51))=k3_yellow_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_42])).
% 2.13/1.27  tff(c_22, plain, (![A_35]: (k3_tarski(k1_zfmisc_1(A_35))=A_35)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.13/1.27  tff(c_223, plain, (![A_87]: (k4_yellow_0(k2_yellow_1(A_87))=k3_tarski(A_87) | ~r2_hidden(k3_tarski(A_87), A_87) | v1_xboole_0(A_87))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.13/1.27  tff(c_230, plain, (![A_35]: (k4_yellow_0(k2_yellow_1(k1_zfmisc_1(A_35)))=k3_tarski(k1_zfmisc_1(A_35)) | ~r2_hidden(A_35, k1_zfmisc_1(A_35)) | v1_xboole_0(k1_zfmisc_1(A_35)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_223])).
% 2.13/1.27  tff(c_232, plain, (![A_35]: (k4_yellow_0(k3_yellow_1(A_35))=A_35 | ~r2_hidden(A_35, k1_zfmisc_1(A_35)) | v1_xboole_0(k1_zfmisc_1(A_35)))), inference(demodulation, [status(thm), theory('equality')], [c_45, c_22, c_230])).
% 2.13/1.27  tff(c_234, plain, (![A_88]: (k4_yellow_0(k3_yellow_1(A_88))=A_88 | ~r2_hidden(A_88, k1_zfmisc_1(A_88)))), inference(negUnitSimplification, [status(thm)], [c_28, c_232])).
% 2.13/1.27  tff(c_238, plain, (![A_44]: (k4_yellow_0(k3_yellow_1(A_44))=A_44 | v1_xboole_0(k1_zfmisc_1(A_44)) | ~m1_subset_1(A_44, k1_zfmisc_1(A_44)))), inference(resolution, [status(thm)], [c_34, c_234])).
% 2.13/1.27  tff(c_241, plain, (![A_44]: (k4_yellow_0(k3_yellow_1(A_44))=A_44 | v1_xboole_0(k1_zfmisc_1(A_44)))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_238])).
% 2.13/1.27  tff(c_242, plain, (![A_44]: (k4_yellow_0(k3_yellow_1(A_44))=A_44)), inference(negUnitSimplification, [status(thm)], [c_28, c_241])).
% 2.13/1.27  tff(c_44, plain, (k4_yellow_0(k3_yellow_1('#skF_2'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.13/1.27  tff(c_246, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_242, c_44])).
% 2.13/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.13/1.27  
% 2.13/1.27  Inference rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Ref     : 0
% 2.13/1.27  #Sup     : 40
% 2.13/1.27  #Fact    : 0
% 2.13/1.27  #Define  : 0
% 2.13/1.27  #Split   : 1
% 2.13/1.27  #Chain   : 0
% 2.13/1.27  #Close   : 0
% 2.13/1.27  
% 2.13/1.27  Ordering : KBO
% 2.13/1.27  
% 2.13/1.27  Simplification rules
% 2.13/1.27  ----------------------
% 2.13/1.27  #Subsume      : 0
% 2.13/1.27  #Demod        : 10
% 2.13/1.27  #Tautology    : 26
% 2.13/1.27  #SimpNegUnit  : 4
% 2.13/1.27  #BackRed      : 1
% 2.13/1.27  
% 2.13/1.27  #Partial instantiations: 0
% 2.13/1.27  #Strategies tried      : 1
% 2.13/1.27  
% 2.13/1.27  Timing (in seconds)
% 2.13/1.27  ----------------------
% 2.13/1.28  Preprocessing        : 0.34
% 2.13/1.28  Parsing              : 0.18
% 2.13/1.28  CNF conversion       : 0.02
% 2.13/1.28  Main loop            : 0.17
% 2.13/1.28  Inferencing          : 0.07
% 2.13/1.28  Reduction            : 0.05
% 2.13/1.28  Demodulation         : 0.04
% 2.13/1.28  BG Simplification    : 0.02
% 2.13/1.28  Subsumption          : 0.02
% 2.13/1.28  Abstraction          : 0.01
% 2.13/1.28  MUC search           : 0.00
% 2.13/1.28  Cooper               : 0.00
% 2.13/1.28  Total                : 0.54
% 2.13/1.28  Index Insertion      : 0.00
% 2.13/1.28  Index Deletion       : 0.00
% 2.13/1.28  Index Matching       : 0.00
% 2.13/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------
