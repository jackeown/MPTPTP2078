%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:58:15 EST 2020

% Result     : Theorem 13.17s
% Output     : CNFRefutation 13.17s
% Verified   : 
% Statistics : Number of formulae       :   69 ( 129 expanded)
%              Number of leaves         :   27 (  54 expanded)
%              Depth                    :    7
%              Number of atoms          :  107 ( 251 expanded)
%              Number of equality atoms :   11 (  24 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_83,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => r1_tarski(k1_relat_1(k3_xboole_0(A,B)),k3_xboole_0(k1_relat_1(A),k1_relat_1(B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relat_1)).

tff(f_43,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_68,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_75,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k1_relat_1(k2_xboole_0(A,B)) = k2_xboole_0(k1_relat_1(A),k1_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relat_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C) )
     => r1_tarski(A,k3_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_38,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_14,plain,(
    ! [A_10,B_11] : r1_tarski(k3_xboole_0(A_10,B_11),A_10) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( m1_subset_1(A_24,k1_zfmisc_1(B_25))
      | ~ r1_tarski(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_190,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_195,plain,(
    ! [A_59,B_60] :
      ( v1_relat_1(A_59)
      | ~ v1_relat_1(B_60)
      | ~ r1_tarski(A_59,B_60) ) ),
    inference(resolution,[status(thm)],[c_28,c_190])).

tff(c_206,plain,(
    ! [A_10,B_11] :
      ( v1_relat_1(k3_xboole_0(A_10,B_11))
      | ~ v1_relat_1(A_10) ) ),
    inference(resolution,[status(thm)],[c_14,c_195])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_106,plain,(
    ! [A_46,B_47] :
      ( k2_xboole_0(A_46,B_47) = B_47
      | ~ r1_tarski(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_117,plain,(
    ! [A_10,B_11] : k2_xboole_0(k3_xboole_0(A_10,B_11),A_10) = A_10 ),
    inference(resolution,[status(thm)],[c_14,c_106])).

tff(c_534,plain,(
    ! [A_101,B_102] :
      ( k2_xboole_0(k1_relat_1(A_101),k1_relat_1(B_102)) = k1_relat_1(k2_xboole_0(A_101,B_102))
      | ~ v1_relat_1(B_102)
      | ~ v1_relat_1(A_101) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_5,C_7,B_6] :
      ( r1_tarski(A_5,C_7)
      | ~ r1_tarski(k2_xboole_0(A_5,B_6),C_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1462,plain,(
    ! [A_130,C_131,B_132] :
      ( r1_tarski(k1_relat_1(A_130),C_131)
      | ~ r1_tarski(k1_relat_1(k2_xboole_0(A_130,B_132)),C_131)
      | ~ v1_relat_1(B_132)
      | ~ v1_relat_1(A_130) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_10])).

tff(c_10773,plain,(
    ! [A_326,B_327,C_328] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(A_326,B_327)),C_328)
      | ~ r1_tarski(k1_relat_1(A_326),C_328)
      | ~ v1_relat_1(A_326)
      | ~ v1_relat_1(k3_xboole_0(A_326,B_327)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_117,c_1462])).

tff(c_502,plain,(
    ! [A_98,B_99,C_100] :
      ( r1_tarski(A_98,k3_xboole_0(B_99,C_100))
      | ~ r1_tarski(A_98,C_100)
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_34,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k3_xboole_0(k1_relat_1('#skF_1'),k1_relat_1('#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_528,plain,
    ( ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2'))
    | ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(resolution,[status(thm)],[c_502,c_34])).

tff(c_574,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_528])).

tff(c_10806,plain,
    ( ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10773,c_574])).

tff(c_10874,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_8,c_10806])).

tff(c_10896,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_10874])).

tff(c_10903,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_10896])).

tff(c_10905,plain,(
    r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( k2_xboole_0(A_8,B_9) = B_9
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_527,plain,(
    ! [A_98,B_99,C_100] :
      ( k2_xboole_0(A_98,k3_xboole_0(B_99,C_100)) = k3_xboole_0(B_99,C_100)
      | ~ r1_tarski(A_98,C_100)
      | ~ r1_tarski(A_98,B_99) ) ),
    inference(resolution,[status(thm)],[c_502,c_12])).

tff(c_12519,plain,(
    ! [A_368,C_369,B_370] :
      ( r1_tarski(k1_relat_1(A_368),C_369)
      | ~ r1_tarski(k1_relat_1(k2_xboole_0(A_368,B_370)),C_369)
      | ~ v1_relat_1(B_370)
      | ~ v1_relat_1(A_368) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_10])).

tff(c_22252,plain,(
    ! [A_563,C_564,B_565,C_566] :
      ( r1_tarski(k1_relat_1(A_563),C_564)
      | ~ r1_tarski(k1_relat_1(k3_xboole_0(B_565,C_566)),C_564)
      | ~ v1_relat_1(k3_xboole_0(B_565,C_566))
      | ~ v1_relat_1(A_563)
      | ~ r1_tarski(A_563,C_566)
      | ~ r1_tarski(A_563,B_565) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_527,c_12519])).

tff(c_22356,plain,(
    ! [A_563] :
      ( r1_tarski(k1_relat_1(A_563),k1_relat_1('#skF_1'))
      | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2'))
      | ~ v1_relat_1(A_563)
      | ~ r1_tarski(A_563,'#skF_2')
      | ~ r1_tarski(A_563,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_10905,c_22252])).

tff(c_22363,plain,(
    ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_22356])).

tff(c_22366,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_206,c_22363])).

tff(c_22373,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_22366])).

tff(c_22375,plain,(
    v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(splitRight,[status(thm)],[c_22356])).

tff(c_36,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_42,plain,(
    ! [B_36,A_37] : k3_xboole_0(B_36,A_37) = k3_xboole_0(A_37,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_57,plain,(
    ! [B_36,A_37] : r1_tarski(k3_xboole_0(B_36,A_37),A_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_14])).

tff(c_116,plain,(
    ! [B_36,A_37] : k2_xboole_0(k3_xboole_0(B_36,A_37),A_37) = A_37 ),
    inference(resolution,[status(thm)],[c_57,c_106])).

tff(c_222,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(A_65,C_66)
      | ~ r1_tarski(k2_xboole_0(A_65,B_67),C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_236,plain,(
    ! [A_65,B_67] : r1_tarski(A_65,k2_xboole_0(A_65,B_67)) ),
    inference(resolution,[status(thm)],[c_8,c_222])).

tff(c_15634,plain,(
    ! [A_429,B_430] :
      ( r1_tarski(k1_relat_1(A_429),k1_relat_1(k2_xboole_0(A_429,B_430)))
      | ~ v1_relat_1(B_430)
      | ~ v1_relat_1(A_429) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_534,c_236])).

tff(c_36507,plain,(
    ! [B_762,A_763] :
      ( r1_tarski(k1_relat_1(k3_xboole_0(B_762,A_763)),k1_relat_1(A_763))
      | ~ v1_relat_1(A_763)
      | ~ v1_relat_1(k3_xboole_0(B_762,A_763)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_15634])).

tff(c_10904,plain,(
    ~ r1_tarski(k1_relat_1(k3_xboole_0('#skF_1','#skF_2')),k1_relat_1('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_528])).

tff(c_36526,plain,
    ( ~ v1_relat_1('#skF_2')
    | ~ v1_relat_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36507,c_10904])).

tff(c_36612,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22375,c_36,c_36526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.06  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.07  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.06/0.25  % Computer   : n008.cluster.edu
% 0.06/0.25  % Model      : x86_64 x86_64
% 0.06/0.25  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.06/0.25  % Memory     : 8042.1875MB
% 0.06/0.25  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.06/0.25  % CPULimit   : 60
% 0.06/0.25  % DateTime   : Tue Dec  1 18:44:29 EST 2020
% 0.06/0.26  % CPUTime    : 
% 0.06/0.26  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.17/5.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.17/5.54  
% 13.17/5.54  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.17/5.54  %$ r1_tarski > m1_subset_1 > v1_relat_1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > k1_setfam_1 > k1_relat_1 > #skF_2 > #skF_1
% 13.17/5.54  
% 13.17/5.54  %Foreground sorts:
% 13.17/5.54  
% 13.17/5.54  
% 13.17/5.54  %Background operators:
% 13.17/5.54  
% 13.17/5.54  
% 13.17/5.54  %Foreground operators:
% 13.17/5.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.17/5.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.17/5.54  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.17/5.54  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.17/5.54  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.17/5.54  tff('#skF_2', type, '#skF_2': $i).
% 13.17/5.54  tff('#skF_1', type, '#skF_1': $i).
% 13.17/5.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 13.17/5.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.17/5.54  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.17/5.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 13.17/5.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.17/5.54  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.17/5.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.17/5.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 13.17/5.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.17/5.54  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.17/5.54  
% 13.17/5.55  tff(f_83, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k3_xboole_0(A, B)), k3_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relat_1)).
% 13.17/5.55  tff(f_43, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.17/5.55  tff(f_61, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 13.17/5.55  tff(f_68, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 13.17/5.55  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 13.17/5.55  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 13.17/5.55  tff(f_75, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k1_relat_1(k2_xboole_0(A, B)) = k2_xboole_0(k1_relat_1(A), k1_relat_1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relat_1)).
% 13.17/5.55  tff(f_37, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 13.17/5.55  tff(f_49, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(A, C)) => r1_tarski(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_xboole_1)).
% 13.17/5.55  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.17/5.55  tff(c_38, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.17/5.55  tff(c_14, plain, (![A_10, B_11]: (r1_tarski(k3_xboole_0(A_10, B_11), A_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.17/5.55  tff(c_28, plain, (![A_24, B_25]: (m1_subset_1(A_24, k1_zfmisc_1(B_25)) | ~r1_tarski(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_61])).
% 13.17/5.55  tff(c_190, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_68])).
% 13.17/5.55  tff(c_195, plain, (![A_59, B_60]: (v1_relat_1(A_59) | ~v1_relat_1(B_60) | ~r1_tarski(A_59, B_60))), inference(resolution, [status(thm)], [c_28, c_190])).
% 13.17/5.55  tff(c_206, plain, (![A_10, B_11]: (v1_relat_1(k3_xboole_0(A_10, B_11)) | ~v1_relat_1(A_10))), inference(resolution, [status(thm)], [c_14, c_195])).
% 13.17/5.55  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 13.17/5.55  tff(c_106, plain, (![A_46, B_47]: (k2_xboole_0(A_46, B_47)=B_47 | ~r1_tarski(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.17/5.55  tff(c_117, plain, (![A_10, B_11]: (k2_xboole_0(k3_xboole_0(A_10, B_11), A_10)=A_10)), inference(resolution, [status(thm)], [c_14, c_106])).
% 13.17/5.55  tff(c_534, plain, (![A_101, B_102]: (k2_xboole_0(k1_relat_1(A_101), k1_relat_1(B_102))=k1_relat_1(k2_xboole_0(A_101, B_102)) | ~v1_relat_1(B_102) | ~v1_relat_1(A_101))), inference(cnfTransformation, [status(thm)], [f_75])).
% 13.17/5.55  tff(c_10, plain, (![A_5, C_7, B_6]: (r1_tarski(A_5, C_7) | ~r1_tarski(k2_xboole_0(A_5, B_6), C_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.17/5.55  tff(c_1462, plain, (![A_130, C_131, B_132]: (r1_tarski(k1_relat_1(A_130), C_131) | ~r1_tarski(k1_relat_1(k2_xboole_0(A_130, B_132)), C_131) | ~v1_relat_1(B_132) | ~v1_relat_1(A_130))), inference(superposition, [status(thm), theory('equality')], [c_534, c_10])).
% 13.17/5.55  tff(c_10773, plain, (![A_326, B_327, C_328]: (r1_tarski(k1_relat_1(k3_xboole_0(A_326, B_327)), C_328) | ~r1_tarski(k1_relat_1(A_326), C_328) | ~v1_relat_1(A_326) | ~v1_relat_1(k3_xboole_0(A_326, B_327)))), inference(superposition, [status(thm), theory('equality')], [c_117, c_1462])).
% 13.17/5.55  tff(c_502, plain, (![A_98, B_99, C_100]: (r1_tarski(A_98, k3_xboole_0(B_99, C_100)) | ~r1_tarski(A_98, C_100) | ~r1_tarski(A_98, B_99))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.17/5.55  tff(c_34, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k3_xboole_0(k1_relat_1('#skF_1'), k1_relat_1('#skF_2')))), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.17/5.55  tff(c_528, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2')) | ~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_502, c_34])).
% 13.17/5.55  tff(c_574, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_528])).
% 13.17/5.55  tff(c_10806, plain, (~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_10773, c_574])).
% 13.17/5.55  tff(c_10874, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_8, c_10806])).
% 13.17/5.55  tff(c_10896, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_206, c_10874])).
% 13.17/5.55  tff(c_10903, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_10896])).
% 13.17/5.55  tff(c_10905, plain, (r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_1'))), inference(splitRight, [status(thm)], [c_528])).
% 13.17/5.55  tff(c_12, plain, (![A_8, B_9]: (k2_xboole_0(A_8, B_9)=B_9 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 13.17/5.55  tff(c_527, plain, (![A_98, B_99, C_100]: (k2_xboole_0(A_98, k3_xboole_0(B_99, C_100))=k3_xboole_0(B_99, C_100) | ~r1_tarski(A_98, C_100) | ~r1_tarski(A_98, B_99))), inference(resolution, [status(thm)], [c_502, c_12])).
% 13.17/5.55  tff(c_12519, plain, (![A_368, C_369, B_370]: (r1_tarski(k1_relat_1(A_368), C_369) | ~r1_tarski(k1_relat_1(k2_xboole_0(A_368, B_370)), C_369) | ~v1_relat_1(B_370) | ~v1_relat_1(A_368))), inference(superposition, [status(thm), theory('equality')], [c_534, c_10])).
% 13.17/5.55  tff(c_22252, plain, (![A_563, C_564, B_565, C_566]: (r1_tarski(k1_relat_1(A_563), C_564) | ~r1_tarski(k1_relat_1(k3_xboole_0(B_565, C_566)), C_564) | ~v1_relat_1(k3_xboole_0(B_565, C_566)) | ~v1_relat_1(A_563) | ~r1_tarski(A_563, C_566) | ~r1_tarski(A_563, B_565))), inference(superposition, [status(thm), theory('equality')], [c_527, c_12519])).
% 13.17/5.55  tff(c_22356, plain, (![A_563]: (r1_tarski(k1_relat_1(A_563), k1_relat_1('#skF_1')) | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2')) | ~v1_relat_1(A_563) | ~r1_tarski(A_563, '#skF_2') | ~r1_tarski(A_563, '#skF_1'))), inference(resolution, [status(thm)], [c_10905, c_22252])).
% 13.17/5.55  tff(c_22363, plain, (~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitLeft, [status(thm)], [c_22356])).
% 13.17/5.55  tff(c_22366, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_206, c_22363])).
% 13.17/5.55  tff(c_22373, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_22366])).
% 13.17/5.55  tff(c_22375, plain, (v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(splitRight, [status(thm)], [c_22356])).
% 13.17/5.55  tff(c_36, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_83])).
% 13.17/5.55  tff(c_42, plain, (![B_36, A_37]: (k3_xboole_0(B_36, A_37)=k3_xboole_0(A_37, B_36))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.17/5.55  tff(c_57, plain, (![B_36, A_37]: (r1_tarski(k3_xboole_0(B_36, A_37), A_37))), inference(superposition, [status(thm), theory('equality')], [c_42, c_14])).
% 13.17/5.55  tff(c_116, plain, (![B_36, A_37]: (k2_xboole_0(k3_xboole_0(B_36, A_37), A_37)=A_37)), inference(resolution, [status(thm)], [c_57, c_106])).
% 13.17/5.55  tff(c_222, plain, (![A_65, C_66, B_67]: (r1_tarski(A_65, C_66) | ~r1_tarski(k2_xboole_0(A_65, B_67), C_66))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.17/5.55  tff(c_236, plain, (![A_65, B_67]: (r1_tarski(A_65, k2_xboole_0(A_65, B_67)))), inference(resolution, [status(thm)], [c_8, c_222])).
% 13.17/5.55  tff(c_15634, plain, (![A_429, B_430]: (r1_tarski(k1_relat_1(A_429), k1_relat_1(k2_xboole_0(A_429, B_430))) | ~v1_relat_1(B_430) | ~v1_relat_1(A_429))), inference(superposition, [status(thm), theory('equality')], [c_534, c_236])).
% 13.17/5.55  tff(c_36507, plain, (![B_762, A_763]: (r1_tarski(k1_relat_1(k3_xboole_0(B_762, A_763)), k1_relat_1(A_763)) | ~v1_relat_1(A_763) | ~v1_relat_1(k3_xboole_0(B_762, A_763)))), inference(superposition, [status(thm), theory('equality')], [c_116, c_15634])).
% 13.17/5.55  tff(c_10904, plain, (~r1_tarski(k1_relat_1(k3_xboole_0('#skF_1', '#skF_2')), k1_relat_1('#skF_2'))), inference(splitRight, [status(thm)], [c_528])).
% 13.17/5.55  tff(c_36526, plain, (~v1_relat_1('#skF_2') | ~v1_relat_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36507, c_10904])).
% 13.17/5.55  tff(c_36612, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22375, c_36, c_36526])).
% 13.17/5.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 13.17/5.55  
% 13.17/5.55  Inference rules
% 13.17/5.55  ----------------------
% 13.17/5.55  #Ref     : 0
% 13.17/5.55  #Sup     : 9303
% 13.17/5.55  #Fact    : 0
% 13.17/5.55  #Define  : 0
% 13.17/5.55  #Split   : 10
% 13.17/5.55  #Chain   : 0
% 13.17/5.55  #Close   : 0
% 13.17/5.55  
% 13.17/5.55  Ordering : KBO
% 13.17/5.55  
% 13.17/5.55  Simplification rules
% 13.17/5.55  ----------------------
% 13.17/5.55  #Subsume      : 1899
% 13.17/5.55  #Demod        : 5015
% 13.17/5.55  #Tautology    : 3619
% 13.17/5.55  #SimpNegUnit  : 4
% 13.17/5.55  #BackRed      : 0
% 13.17/5.55  
% 13.17/5.55  #Partial instantiations: 0
% 13.17/5.55  #Strategies tried      : 1
% 13.17/5.55  
% 13.17/5.55  Timing (in seconds)
% 13.17/5.55  ----------------------
% 13.17/5.56  Preprocessing        : 0.31
% 13.17/5.56  Parsing              : 0.17
% 13.17/5.56  CNF conversion       : 0.02
% 13.17/5.56  Main loop            : 4.63
% 13.17/5.56  Inferencing          : 0.79
% 13.17/5.56  Reduction            : 2.27
% 13.17/5.56  Demodulation         : 1.99
% 13.17/5.56  BG Simplification    : 0.10
% 13.17/5.56  Subsumption          : 1.21
% 13.17/5.56  Abstraction          : 0.15
% 13.17/5.56  MUC search           : 0.00
% 13.17/5.56  Cooper               : 0.00
% 13.17/5.56  Total                : 4.97
% 13.17/5.56  Index Insertion      : 0.00
% 13.17/5.56  Index Deletion       : 0.00
% 13.17/5.56  Index Matching       : 0.00
% 13.17/5.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
