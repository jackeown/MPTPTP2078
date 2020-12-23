%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:14 EST 2020

% Result     : Theorem 24.87s
% Output     : CNFRefutation 24.87s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 157 expanded)
%              Number of leaves         :   27 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :  101 ( 264 expanded)
%              Number of equality atoms :   14 (  54 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_66,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_73,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(c_34,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_16,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_101,plain,(
    ! [A_42,B_43] : k1_setfam_1(k2_tarski(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_446,plain,(
    ! [B_80,A_81] : k1_setfam_1(k2_tarski(B_80,A_81)) = k3_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_101])).

tff(c_22,plain,(
    ! [A_19,B_20] : k1_setfam_1(k2_tarski(A_19,B_20)) = k3_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_469,plain,(
    ! [B_82,A_83] : k3_xboole_0(B_82,A_83) = k3_xboole_0(A_83,B_82) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_22])).

tff(c_12,plain,(
    ! [A_8,B_9] : r1_tarski(k3_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( m1_subset_1(A_21,k1_zfmisc_1(B_22))
      | ~ r1_tarski(A_21,B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_322,plain,(
    ! [B_65,A_66] :
      ( v1_relat_1(B_65)
      | ~ m1_subset_1(B_65,k1_zfmisc_1(A_66))
      | ~ v1_relat_1(A_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_329,plain,(
    ! [A_67,B_68] :
      ( v1_relat_1(A_67)
      | ~ v1_relat_1(B_68)
      | ~ r1_tarski(A_67,B_68) ) ),
    inference(resolution,[status(thm)],[c_26,c_322])).

tff(c_344,plain,(
    ! [A_8,B_9] :
      ( v1_relat_1(k3_xboole_0(A_8,B_9))
      | ~ v1_relat_1(A_8) ) ),
    inference(resolution,[status(thm)],[c_12,c_329])).

tff(c_487,plain,(
    ! [A_83,B_82] :
      ( v1_relat_1(k3_xboole_0(A_83,B_82))
      | ~ v1_relat_1(B_82) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_344])).

tff(c_36,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_73,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_80,plain,(
    ! [A_8,B_9] : k2_xboole_0(k3_xboole_0(A_8,B_9),A_8) = A_8 ),
    inference(resolution,[status(thm)],[c_12,c_73])).

tff(c_400,plain,(
    ! [A_78,B_79] :
      ( k2_xboole_0(k1_relat_1(A_78),k1_relat_1(B_79)) = k1_relat_1(k2_xboole_0(A_78,B_79))
      | ~ v1_relat_1(B_79)
      | ~ v1_relat_1(A_78) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(k2_xboole_0(A_3,B_4),C_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10414,plain,(
    ! [A_318,C_319,B_320] :
      ( r1_tarski(k1_relat_1(A_318),C_319)
      | ~ r1_tarski(k1_relat_1(k2_xboole_0(A_318,B_320)),C_319)
      | ~ v1_relat_1(B_320)
      | ~ v1_relat_1(A_318) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_8])).

tff(c_17131,plain,(
    ! [A_450,B_451,C_452] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_450,B_451)),C_452)
      | ~ r1_tarski(k1_relat_1(A_450),C_452)
      | ~ v1_relat_1(A_450)
      | ~ v1_relat_1(k3_xboole_0(A_450,B_451)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_10414])).

tff(c_32,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_17152,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_17131,c_32])).

tff(c_17223,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2')))
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_17152])).

tff(c_17526,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_17223])).

tff(c_17529,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_487,c_17526])).

tff(c_17536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_17529])).

tff(c_17538,plain,(
    v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_17223])).

tff(c_452,plain,(
    ! [B_80,A_81] : k3_xboole_0(B_80,A_81) = k3_xboole_0(A_81,B_80) ),
    inference(superposition,[status(thm),theory(equality)],[c_446,c_22])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_95057,plain,(
    ! [A_1117,B_1118,C_1119] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_1117,B_1118)),C_1119)
      | ~ r1_tarski(k1_relat_1(B_1118),C_1119)
      | ~ v1_relat_1(B_1118)
      | ~ v1_relat_1(k3_xboole_0(B_1118,A_1117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_452,c_17131])).

tff(c_1539,plain,(
    ! [A_125,C_126,B_127] :
      ( r1_tarski(k1_relat_1(A_125),C_126)
      | ~ r1_tarski(k1_relat_1(k2_xboole_0(A_125,B_127)),C_126)
      | ~ v1_relat_1(B_127)
      | ~ v1_relat_1(A_125) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_400,c_8])).

tff(c_9006,plain,(
    ! [A_270,B_271,C_272] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_270,B_271)),C_272)
      | ~ r1_tarski(k1_relat_1(A_270),C_272)
      | ~ v1_relat_1(A_270)
      | ~ v1_relat_1(k3_xboole_0(A_270,B_271)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_1539])).

tff(c_346,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(A_69,k3_xboole_0(B_70,C_71))
      | ~ r1_tarski(A_69,C_71)
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_365,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_346,c_32])).

tff(c_552,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_365])).

tff(c_9019,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_9006,c_552])).

tff(c_9090,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_6,c_9019])).

tff(c_9115,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_487,c_9090])).

tff(c_9122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_9115])).

tff(c_9123,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_365])).

tff(c_95126,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_2'),k1_relat_1('#skF_2'))
    | ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_95057,c_9123])).

tff(c_95273,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_17538,c_452,c_34,c_6,c_95126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:40:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 24.87/15.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.87/15.99  
% 24.87/15.99  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.87/16.00  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 24.87/16.00  
% 24.87/16.00  %Foreground sorts:
% 24.87/16.00  
% 24.87/16.00  
% 24.87/16.00  %Background operators:
% 24.87/16.00  
% 24.87/16.00  
% 24.87/16.00  %Foreground operators:
% 24.87/16.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 24.87/16.00  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 24.87/16.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 24.87/16.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 24.87/16.00  tff('#skF_2', type, '#skF_2': $i).
% 24.87/16.00  tff('#skF_1', type, '#skF_1': $i).
% 24.87/16.00  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 24.87/16.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 24.87/16.00  tff(k3_tarski, type, k3_tarski: $i > $i).
% 24.87/16.00  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 24.87/16.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 24.87/16.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 24.87/16.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 24.87/16.00  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 24.87/16.00  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 24.87/16.00  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 24.87/16.00  
% 24.87/16.01  tff(f_81, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 24.87/16.01  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 24.87/16.01  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_setfam_1)).
% 24.87/16.01  tff(f_41, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 24.87/16.01  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 24.87/16.01  tff(f_66, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 24.87/16.01  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 24.87/16.01  tff(f_73, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 24.87/16.01  tff(f_35, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 24.87/16.01  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 24.87/16.01  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 24.87/16.01  tff(c_34, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.87/16.01  tff(c_16, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_49])).
% 24.87/16.01  tff(c_101, plain, (![A_42, B_43]: (k1_setfam_1(k2_tarski(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.87/16.01  tff(c_446, plain, (![B_80, A_81]: (k1_setfam_1(k2_tarski(B_80, A_81))=k3_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_16, c_101])).
% 24.87/16.01  tff(c_22, plain, (![A_19, B_20]: (k1_setfam_1(k2_tarski(A_19, B_20))=k3_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 24.87/16.01  tff(c_469, plain, (![B_82, A_83]: (k3_xboole_0(B_82, A_83)=k3_xboole_0(A_83, B_82))), inference(superposition, [status(thm), theory('equality')], [c_446, c_22])).
% 24.87/16.01  tff(c_12, plain, (![A_8, B_9]: (r1_tarski(k3_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_41])).
% 24.87/16.01  tff(c_26, plain, (![A_21, B_22]: (m1_subset_1(A_21, k1_zfmisc_1(B_22)) | ~r1_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_59])).
% 24.87/16.01  tff(c_322, plain, (![B_65, A_66]: (v1_relat_1(B_65) | ~m1_subset_1(B_65, k1_zfmisc_1(A_66)) | ~v1_relat_1(A_66))), inference(cnfTransformation, [status(thm)], [f_66])).
% 24.87/16.01  tff(c_329, plain, (![A_67, B_68]: (v1_relat_1(A_67) | ~v1_relat_1(B_68) | ~r1_tarski(A_67, B_68))), inference(resolution, [status(thm)], [c_26, c_322])).
% 24.87/16.01  tff(c_344, plain, (![A_8, B_9]: (v1_relat_1(k3_xboole_0(A_8, B_9)) | ~v1_relat_1(A_8))), inference(resolution, [status(thm)], [c_12, c_329])).
% 24.87/16.01  tff(c_487, plain, (![A_83, B_82]: (v1_relat_1(k3_xboole_0(A_83, B_82)) | ~v1_relat_1(B_82))), inference(superposition, [status(thm), theory('equality')], [c_469, c_344])).
% 24.87/16.01  tff(c_36, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.87/16.01  tff(c_73, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_39])).
% 24.87/16.01  tff(c_80, plain, (![A_8, B_9]: (k2_xboole_0(k3_xboole_0(A_8, B_9), A_8)=A_8)), inference(resolution, [status(thm)], [c_12, c_73])).
% 24.87/16.01  tff(c_400, plain, (![A_78, B_79]: (k2_xboole_0(k1_relat_1(A_78), k1_relat_1(B_79))=k1_relat_1(k2_xboole_0(A_78, B_79)) | ~v1_relat_1(B_79) | ~v1_relat_1(A_78))), inference(cnfTransformation, [status(thm)], [f_73])).
% 24.87/16.01  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(k2_xboole_0(A_3, B_4), C_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 24.87/16.01  tff(c_10414, plain, (![A_318, C_319, B_320]: (r1_tarski(k1_relat_1(A_318), C_319) | ~r1_tarski(k1_relat_1(k2_xboole_0(A_318, B_320)), C_319) | ~v1_relat_1(B_320) | ~v1_relat_1(A_318))), inference(superposition, [status(thm), theory('equality')], [c_400, c_8])).
% 24.87/16.01  tff(c_17131, plain, (![A_450, B_451, C_452]: (r1_tarski(k1_relat_1(k3_xboole_0(A_450, B_451)), C_452) | ~r1_tarski(k1_relat_1(A_450), C_452) | ~v1_relat_1(A_450) | ~v1_relat_1(k3_xboole_0(A_450, B_451)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_10414])).
% 24.87/16.01  tff(c_32, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_81])).
% 24.87/16.01  tff(c_17152, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_17131, c_32])).
% 24.87/16.01  tff(c_17223, plain, (~r1_tarski(k1_relat_1('#skF_1'), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2'))) | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_17152])).
% 24.87/16.01  tff(c_17526, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_17223])).
% 24.87/16.01  tff(c_17529, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_487, c_17526])).
% 24.87/16.01  tff(c_17536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_17529])).
% 24.87/16.01  tff(c_17538, plain, (v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_17223])).
% 24.87/16.01  tff(c_452, plain, (![B_80, A_81]: (k3_xboole_0(B_80, A_81)=k3_xboole_0(A_81, B_80))), inference(superposition, [status(thm), theory('equality')], [c_446, c_22])).
% 24.87/16.01  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 24.87/16.01  tff(c_95057, plain, (![A_1117, B_1118, C_1119]: (r1_tarski(k1_relat_1(k3_xboole_0(A_1117, B_1118)), C_1119) | ~r1_tarski(k1_relat_1(B_1118), C_1119) | ~v1_relat_1(B_1118) | ~v1_relat_1(k3_xboole_0(B_1118, A_1117)))), inference(superposition, [status(thm), theory('equality')], [c_452, c_17131])).
% 24.87/16.01  tff(c_1539, plain, (![A_125, C_126, B_127]: (r1_tarski(k1_relat_1(A_125), C_126) | ~r1_tarski(k1_relat_1(k2_xboole_0(A_125, B_127)), C_126) | ~v1_relat_1(B_127) | ~v1_relat_1(A_125))), inference(superposition, [status(thm), theory('equality')], [c_400, c_8])).
% 24.87/16.01  tff(c_9006, plain, (![A_270, B_271, C_272]: (r1_tarski(k1_relat_1(k3_xboole_0(A_270, B_271)), C_272) | ~r1_tarski(k1_relat_1(A_270), C_272) | ~v1_relat_1(A_270) | ~v1_relat_1(k3_xboole_0(A_270, B_271)))), inference(superposition, [status(thm), theory('equality')], [c_80, c_1539])).
% 24.87/16.01  tff(c_346, plain, (![A_69, B_70, C_71]: (r1_tarski(A_69, k3_xboole_0(B_70, C_71)) | ~r1_tarski(A_69, C_71) | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_47])).
% 24.87/16.01  tff(c_365, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_346, c_32])).
% 24.87/16.01  tff(c_552, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_365])).
% 24.87/16.01  tff(c_9019, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_9006, c_552])).
% 24.87/16.01  tff(c_9090, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_6, c_9019])).
% 24.87/16.01  tff(c_9115, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_487, c_9090])).
% 24.87/16.01  tff(c_9122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_9115])).
% 24.87/16.01  tff(c_9123, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_365])).
% 24.87/16.01  tff(c_95126, plain, (~r1_tarski(k1_relat_1('#skF_2'), k1_relat_1('#skF_2')) | ~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_95057, c_9123])).
% 24.87/16.01  tff(c_95273, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_17538, c_452, c_34, c_6, c_95126])).
% 24.87/16.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 24.87/16.01  
% 24.87/16.01  Inference rules
% 24.87/16.01  ----------------------
% 24.87/16.01  #Ref     : 0
% 24.87/16.01  #Sup     : 23812
% 24.87/16.01  #Fact    : 0
% 24.87/16.01  #Define  : 0
% 24.87/16.01  #Split   : 7
% 24.87/16.01  #Chain   : 0
% 24.87/16.01  #Close   : 0
% 24.87/16.01  
% 24.87/16.01  Ordering : KBO
% 24.87/16.01  
% 24.87/16.01  Simplification rules
% 24.87/16.01  ----------------------
% 24.87/16.01  #Subsume      : 5182
% 24.87/16.01  #Demod        : 13373
% 24.87/16.01  #Tautology    : 9181
% 24.87/16.01  #SimpNegUnit  : 50
% 24.87/16.01  #BackRed      : 0
% 24.87/16.01  
% 24.87/16.01  #Partial instantiations: 0
% 24.87/16.01  #Strategies tried      : 1
% 24.87/16.01  
% 24.87/16.01  Timing (in seconds)
% 24.87/16.01  ----------------------
% 24.87/16.01  Preprocessing        : 0.32
% 24.87/16.01  Parsing              : 0.17
% 24.87/16.01  CNF conversion       : 0.02
% 24.87/16.02  Main loop            : 14.93
% 24.87/16.02  Inferencing          : 1.64
% 24.87/16.02  Reduction            : 7.89
% 24.87/16.02  Demodulation         : 7.12
% 24.87/16.02  BG Simplification    : 0.21
% 24.87/16.02  Subsumption          : 4.52
% 24.87/16.02  Abstraction          : 0.32
% 24.87/16.02  MUC search           : 0.00
% 24.87/16.02  Cooper               : 0.00
% 24.87/16.02  Total                : 15.28
% 24.87/16.02  Index Insertion      : 0.00
% 24.87/16.02  Index Deletion       : 0.00
% 24.87/16.02  Index Matching       : 0.00
% 24.87/16.02  BG Taut test         : 0.00
%------------------------------------------------------------------------------
