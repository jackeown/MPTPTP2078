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
% DateTime   : Thu Dec  3 10:05:20 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   70 (  90 expanded)
%              Number of leaves         :   36 (  47 expanded)
%              Depth                    :   10
%              Number of atoms          :   78 ( 102 expanded)
%              Number of equality atoms :   33 (  50 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_57,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_75,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_79,axiom,(
    ! [A,B] : k5_relat_1(k6_relat_1(B),k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_funct_1)).

tff(f_64,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t160_relat_1)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] :
        ( m1_subset_1(B,k1_zfmisc_1(A))
       => k9_relat_1(k6_relat_1(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t162_funct_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_77,axiom,(
    ! [A] : k4_relat_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

tff(f_71,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k4_relat_1(k5_relat_1(A,B)) = k5_relat_1(k4_relat_1(B),k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

tff(c_26,plain,(
    ! [A_25] : v1_relat_1(k6_relat_1(A_25)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    ! [A_32] : k2_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_38,plain,(
    ! [B_35,A_34] : k5_relat_1(k6_relat_1(B_35),k6_relat_1(A_34)) = k6_relat_1(k3_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_469,plain,(
    ! [B_100,A_101] :
      ( k9_relat_1(B_100,k2_relat_1(A_101)) = k2_relat_1(k5_relat_1(A_101,B_100))
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_478,plain,(
    ! [A_32,B_100] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_32),B_100)) = k9_relat_1(B_100,A_32)
      | ~ v1_relat_1(B_100)
      | ~ v1_relat_1(k6_relat_1(A_32)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_469])).

tff(c_904,plain,(
    ! [A_120,B_121] :
      ( k2_relat_1(k5_relat_1(k6_relat_1(A_120),B_121)) = k9_relat_1(B_121,A_120)
      | ~ v1_relat_1(B_121) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_478])).

tff(c_916,plain,(
    ! [A_34,B_35] :
      ( k2_relat_1(k6_relat_1(k3_xboole_0(A_34,B_35))) = k9_relat_1(k6_relat_1(A_34),B_35)
      | ~ v1_relat_1(k6_relat_1(A_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_904])).

tff(c_920,plain,(
    ! [A_34,B_35] : k9_relat_1(k6_relat_1(A_34),B_35) = k3_xboole_0(A_34,B_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_34,c_916])).

tff(c_40,plain,(
    k9_relat_1(k6_relat_1('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_921,plain,(
    k3_xboole_0('#skF_1','#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_40])).

tff(c_32,plain,(
    ! [A_32] : k1_relat_1(k6_relat_1(A_32)) = A_32 ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    m1_subset_1('#skF_2',k1_zfmisc_1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_140,plain,(
    ! [A_58,B_59] :
      ( r1_tarski(A_58,B_59)
      | ~ m1_subset_1(A_58,k1_zfmisc_1(B_59)) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_148,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_42,c_140])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_72,plain,(
    ! [B_42,A_43] :
      ( r1_xboole_0(B_42,A_43)
      | ~ r1_xboole_0(A_43,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_75,plain,(
    ! [B_9,A_8] : r1_xboole_0(B_9,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_8,c_72])).

tff(c_192,plain,(
    ! [A_64,C_65,B_66] :
      ( r1_xboole_0(A_64,C_65)
      | ~ r1_xboole_0(B_66,C_65)
      | ~ r1_tarski(A_64,B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_377,plain,(
    ! [A_86,A_87,B_88] :
      ( r1_xboole_0(A_86,k4_xboole_0(A_87,B_88))
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(resolution,[status(thm)],[c_75,c_192])).

tff(c_10,plain,(
    ! [A_10,B_11] :
      ( k4_xboole_0(A_10,B_11) = A_10
      | ~ r1_xboole_0(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_656,plain,(
    ! [A_115,A_116,B_117] :
      ( k4_xboole_0(A_115,k4_xboole_0(A_116,B_117)) = A_115
      | ~ r1_tarski(A_115,B_117) ) ),
    inference(resolution,[status(thm)],[c_377,c_10])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k4_xboole_0(A_3,B_4)) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_768,plain,(
    ! [A_118,B_119] :
      ( k3_xboole_0(A_118,B_119) = A_118
      | ~ r1_tarski(A_118,B_119) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_656,c_4])).

tff(c_772,plain,(
    k3_xboole_0('#skF_2','#skF_1') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_148,c_768])).

tff(c_36,plain,(
    ! [A_33] : k4_relat_1(k6_relat_1(A_33)) = k6_relat_1(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_565,plain,(
    ! [B_109,A_110] :
      ( k5_relat_1(k4_relat_1(B_109),k4_relat_1(A_110)) = k4_relat_1(k5_relat_1(A_110,B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(A_110) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_577,plain,(
    ! [B_109,A_33] :
      ( k5_relat_1(k4_relat_1(B_109),k6_relat_1(A_33)) = k4_relat_1(k5_relat_1(k6_relat_1(A_33),B_109))
      | ~ v1_relat_1(B_109)
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_565])).

tff(c_1596,plain,(
    ! [B_141,A_142] :
      ( k5_relat_1(k4_relat_1(B_141),k6_relat_1(A_142)) = k4_relat_1(k5_relat_1(k6_relat_1(A_142),B_141))
      | ~ v1_relat_1(B_141) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_577])).

tff(c_1605,plain,(
    ! [A_142,A_33] :
      ( k4_relat_1(k5_relat_1(k6_relat_1(A_142),k6_relat_1(A_33))) = k5_relat_1(k6_relat_1(A_33),k6_relat_1(A_142))
      | ~ v1_relat_1(k6_relat_1(A_33)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_1596])).

tff(c_1614,plain,(
    ! [A_144,A_143] : k6_relat_1(k3_xboole_0(A_144,A_143)) = k6_relat_1(k3_xboole_0(A_143,A_144)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_38,c_36,c_38,c_1605])).

tff(c_1693,plain,(
    k6_relat_1(k3_xboole_0('#skF_1','#skF_2')) = k6_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_772,c_1614])).

tff(c_1728,plain,(
    k1_relat_1(k6_relat_1('#skF_2')) = k3_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1693,c_32])).

tff(c_1741,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_1728])).

tff(c_1743,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_921,c_1741])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  
% 3.46/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  %$ r1_xboole_0 > r1_tarski > m1_subset_1 > v1_relat_1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k9_relat_1 > k5_relat_1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k6_relat_1 > k4_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 3.46/1.54  
% 3.46/1.54  %Foreground sorts:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Background operators:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Foreground operators:
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 3.46/1.54  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.46/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.46/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.46/1.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.46/1.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.46/1.54  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.46/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.46/1.54  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 3.46/1.54  tff('#skF_1', type, '#skF_1': $i).
% 3.46/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.46/1.54  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.46/1.54  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 3.46/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.46/1.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.46/1.54  
% 3.46/1.56  tff(f_57, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 3.46/1.56  tff(f_75, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 3.46/1.56  tff(f_79, axiom, (![A, B]: (k5_relat_1(k6_relat_1(B), k6_relat_1(A)) = k6_relat_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_funct_1)).
% 3.46/1.56  tff(f_64, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t160_relat_1)).
% 3.46/1.56  tff(f_84, negated_conjecture, ~(![A, B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (k9_relat_1(k6_relat_1(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t162_funct_1)).
% 3.46/1.56  tff(f_55, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 3.46/1.56  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.46/1.56  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 3.46/1.56  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 3.46/1.56  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.46/1.56  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.46/1.56  tff(f_77, axiom, (![A]: (k4_relat_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t72_relat_1)).
% 3.46/1.56  tff(f_71, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k4_relat_1(k5_relat_1(A, B)) = k5_relat_1(k4_relat_1(B), k4_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_relat_1)).
% 3.46/1.56  tff(c_26, plain, (![A_25]: (v1_relat_1(k6_relat_1(A_25)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.46/1.56  tff(c_34, plain, (![A_32]: (k2_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.46/1.56  tff(c_38, plain, (![B_35, A_34]: (k5_relat_1(k6_relat_1(B_35), k6_relat_1(A_34))=k6_relat_1(k3_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.46/1.56  tff(c_469, plain, (![B_100, A_101]: (k9_relat_1(B_100, k2_relat_1(A_101))=k2_relat_1(k5_relat_1(A_101, B_100)) | ~v1_relat_1(B_100) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.46/1.56  tff(c_478, plain, (![A_32, B_100]: (k2_relat_1(k5_relat_1(k6_relat_1(A_32), B_100))=k9_relat_1(B_100, A_32) | ~v1_relat_1(B_100) | ~v1_relat_1(k6_relat_1(A_32)))), inference(superposition, [status(thm), theory('equality')], [c_34, c_469])).
% 3.46/1.56  tff(c_904, plain, (![A_120, B_121]: (k2_relat_1(k5_relat_1(k6_relat_1(A_120), B_121))=k9_relat_1(B_121, A_120) | ~v1_relat_1(B_121))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_478])).
% 3.46/1.56  tff(c_916, plain, (![A_34, B_35]: (k2_relat_1(k6_relat_1(k3_xboole_0(A_34, B_35)))=k9_relat_1(k6_relat_1(A_34), B_35) | ~v1_relat_1(k6_relat_1(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_904])).
% 3.46/1.56  tff(c_920, plain, (![A_34, B_35]: (k9_relat_1(k6_relat_1(A_34), B_35)=k3_xboole_0(A_34, B_35))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_34, c_916])).
% 3.46/1.56  tff(c_40, plain, (k9_relat_1(k6_relat_1('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.46/1.56  tff(c_921, plain, (k3_xboole_0('#skF_1', '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_920, c_40])).
% 3.46/1.56  tff(c_32, plain, (![A_32]: (k1_relat_1(k6_relat_1(A_32))=A_32)), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.46/1.56  tff(c_42, plain, (m1_subset_1('#skF_2', k1_zfmisc_1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.46/1.56  tff(c_140, plain, (![A_58, B_59]: (r1_tarski(A_58, B_59) | ~m1_subset_1(A_58, k1_zfmisc_1(B_59)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.56  tff(c_148, plain, (r1_tarski('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_42, c_140])).
% 3.46/1.56  tff(c_8, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.46/1.56  tff(c_72, plain, (![B_42, A_43]: (r1_xboole_0(B_42, A_43) | ~r1_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.56  tff(c_75, plain, (![B_9, A_8]: (r1_xboole_0(B_9, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_8, c_72])).
% 3.46/1.56  tff(c_192, plain, (![A_64, C_65, B_66]: (r1_xboole_0(A_64, C_65) | ~r1_xboole_0(B_66, C_65) | ~r1_tarski(A_64, B_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.46/1.56  tff(c_377, plain, (![A_86, A_87, B_88]: (r1_xboole_0(A_86, k4_xboole_0(A_87, B_88)) | ~r1_tarski(A_86, B_88))), inference(resolution, [status(thm)], [c_75, c_192])).
% 3.46/1.56  tff(c_10, plain, (![A_10, B_11]: (k4_xboole_0(A_10, B_11)=A_10 | ~r1_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.56  tff(c_656, plain, (![A_115, A_116, B_117]: (k4_xboole_0(A_115, k4_xboole_0(A_116, B_117))=A_115 | ~r1_tarski(A_115, B_117))), inference(resolution, [status(thm)], [c_377, c_10])).
% 3.46/1.56  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k4_xboole_0(A_3, B_4))=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.56  tff(c_768, plain, (![A_118, B_119]: (k3_xboole_0(A_118, B_119)=A_118 | ~r1_tarski(A_118, B_119))), inference(superposition, [status(thm), theory('equality')], [c_656, c_4])).
% 3.46/1.56  tff(c_772, plain, (k3_xboole_0('#skF_2', '#skF_1')='#skF_2'), inference(resolution, [status(thm)], [c_148, c_768])).
% 3.46/1.56  tff(c_36, plain, (![A_33]: (k4_relat_1(k6_relat_1(A_33))=k6_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.46/1.56  tff(c_565, plain, (![B_109, A_110]: (k5_relat_1(k4_relat_1(B_109), k4_relat_1(A_110))=k4_relat_1(k5_relat_1(A_110, B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(A_110))), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.46/1.56  tff(c_577, plain, (![B_109, A_33]: (k5_relat_1(k4_relat_1(B_109), k6_relat_1(A_33))=k4_relat_1(k5_relat_1(k6_relat_1(A_33), B_109)) | ~v1_relat_1(B_109) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_565])).
% 3.46/1.56  tff(c_1596, plain, (![B_141, A_142]: (k5_relat_1(k4_relat_1(B_141), k6_relat_1(A_142))=k4_relat_1(k5_relat_1(k6_relat_1(A_142), B_141)) | ~v1_relat_1(B_141))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_577])).
% 3.46/1.56  tff(c_1605, plain, (![A_142, A_33]: (k4_relat_1(k5_relat_1(k6_relat_1(A_142), k6_relat_1(A_33)))=k5_relat_1(k6_relat_1(A_33), k6_relat_1(A_142)) | ~v1_relat_1(k6_relat_1(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_1596])).
% 3.46/1.56  tff(c_1614, plain, (![A_144, A_143]: (k6_relat_1(k3_xboole_0(A_144, A_143))=k6_relat_1(k3_xboole_0(A_143, A_144)))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_38, c_36, c_38, c_1605])).
% 3.46/1.56  tff(c_1693, plain, (k6_relat_1(k3_xboole_0('#skF_1', '#skF_2'))=k6_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_772, c_1614])).
% 3.46/1.56  tff(c_1728, plain, (k1_relat_1(k6_relat_1('#skF_2'))=k3_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1693, c_32])).
% 3.46/1.56  tff(c_1741, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_1728])).
% 3.46/1.56  tff(c_1743, plain, $false, inference(negUnitSimplification, [status(thm)], [c_921, c_1741])).
% 3.46/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.56  
% 3.46/1.56  Inference rules
% 3.46/1.56  ----------------------
% 3.46/1.56  #Ref     : 0
% 3.46/1.56  #Sup     : 444
% 3.46/1.56  #Fact    : 0
% 3.46/1.56  #Define  : 0
% 3.46/1.56  #Split   : 1
% 3.46/1.56  #Chain   : 0
% 3.46/1.56  #Close   : 0
% 3.46/1.56  
% 3.46/1.56  Ordering : KBO
% 3.46/1.56  
% 3.46/1.56  Simplification rules
% 3.46/1.56  ----------------------
% 3.46/1.56  #Subsume      : 29
% 3.46/1.56  #Demod        : 237
% 3.46/1.56  #Tautology    : 201
% 3.46/1.56  #SimpNegUnit  : 1
% 3.46/1.56  #BackRed      : 5
% 3.46/1.56  
% 3.46/1.56  #Partial instantiations: 0
% 3.46/1.56  #Strategies tried      : 1
% 3.46/1.56  
% 3.46/1.56  Timing (in seconds)
% 3.46/1.56  ----------------------
% 3.46/1.56  Preprocessing        : 0.30
% 3.46/1.56  Parsing              : 0.17
% 3.46/1.56  CNF conversion       : 0.02
% 3.46/1.56  Main loop            : 0.48
% 3.46/1.56  Inferencing          : 0.16
% 3.46/1.56  Reduction            : 0.17
% 3.46/1.56  Demodulation         : 0.13
% 3.46/1.56  BG Simplification    : 0.02
% 3.46/1.56  Subsumption          : 0.10
% 3.46/1.56  Abstraction          : 0.03
% 3.46/1.56  MUC search           : 0.00
% 3.46/1.56  Cooper               : 0.00
% 3.46/1.56  Total                : 0.82
% 3.46/1.56  Index Insertion      : 0.00
% 3.46/1.56  Index Deletion       : 0.00
% 3.46/1.56  Index Matching       : 0.00
% 3.46/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
