%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:21 EST 2020

% Result     : Theorem 2.51s
% Output     : CNFRefutation 2.88s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 103 expanded)
%              Number of leaves         :   29 (  47 expanded)
%              Depth                    :   13
%              Number of atoms          :  102 ( 174 expanded)
%              Number of equality atoms :   51 (  74 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_zfmisc_1,type,(
    v1_zfmisc_1: $i > $o )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_84,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_72,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_62,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_34,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_30,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_36,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_55,axiom,(
    ! [A,B] : k1_setfam_1(k2_tarski(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_setfam_1)).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_26,plain,(
    ! [A_19] :
      ( m1_subset_1('#skF_1'(A_19),A_19)
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_380,plain,(
    ! [A_54,B_55] :
      ( k6_domain_1(A_54,B_55) = k1_tarski(B_55)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_406,plain,(
    ! [A_61] :
      ( k6_domain_1(A_61,'#skF_1'(A_61)) = k1_tarski('#skF_1'(A_61))
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61) ) ),
    inference(resolution,[status(thm)],[c_26,c_380])).

tff(c_24,plain,(
    ! [A_19] :
      ( k6_domain_1(A_19,'#skF_1'(A_19)) = A_19
      | ~ v1_zfmisc_1(A_19)
      | v1_xboole_0(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_421,plain,(
    ! [A_62] :
      ( k1_tarski('#skF_1'(A_62)) = A_62
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62)
      | ~ v1_zfmisc_1(A_62)
      | v1_xboole_0(A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_24])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_44,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_48,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_437,plain,(
    ! [A_63] :
      ( k1_xboole_0 != A_63
      | ~ v1_zfmisc_1(A_63)
      | v1_xboole_0(A_63)
      | ~ v1_zfmisc_1(A_63)
      | v1_xboole_0(A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_421,c_48])).

tff(c_439,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_437])).

tff(c_442,plain,
    ( k1_xboole_0 != '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_439])).

tff(c_443,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_442])).

tff(c_412,plain,(
    ! [A_61] :
      ( k1_tarski('#skF_1'(A_61)) = A_61
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61)
      | ~ v1_zfmisc_1(A_61)
      | v1_xboole_0(A_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_24])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_99,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_103,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_6,c_99])).

tff(c_391,plain,(
    ! [C_58,B_59,A_60] :
      ( k1_xboole_0 = C_58
      | k1_xboole_0 = B_59
      | C_58 = B_59
      | k2_xboole_0(B_59,C_58) != k1_tarski(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_459,plain,(
    ! [A_66,B_67,A_68] :
      ( k1_xboole_0 = A_66
      | k3_xboole_0(A_66,B_67) = k1_xboole_0
      | k3_xboole_0(A_66,B_67) = A_66
      | k1_tarski(A_68) != A_66 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_391])).

tff(c_743,plain,(
    ! [A_79,B_80] :
      ( k1_xboole_0 = A_79
      | k3_xboole_0(A_79,B_80) = k1_xboole_0
      | k3_xboole_0(A_79,B_80) = A_79
      | ~ v1_zfmisc_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_412,c_459])).

tff(c_745,plain,(
    ! [B_80] :
      ( k1_xboole_0 = '#skF_2'
      | k3_xboole_0('#skF_2',B_80) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_80) = '#skF_2'
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_32,c_743])).

tff(c_753,plain,(
    ! [B_81] :
      ( k3_xboole_0('#skF_2',B_81) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_81) = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_443,c_745])).

tff(c_10,plain,(
    ! [B_7,A_6] : k2_tarski(B_7,A_6) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_84,plain,(
    ! [A_32,B_33] : k1_setfam_1(k2_tarski(A_32,B_33)) = k3_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_150,plain,(
    ! [A_41,B_42] : k1_setfam_1(k2_tarski(A_41,B_42)) = k3_xboole_0(B_42,A_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_18,plain,(
    ! [A_15,B_16] : k1_setfam_1(k2_tarski(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_156,plain,(
    ! [B_42,A_41] : k3_xboole_0(B_42,A_41) = k3_xboole_0(A_41,B_42) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_18])).

tff(c_816,plain,(
    ! [B_82] :
      ( k3_xboole_0(B_82,'#skF_2') = k1_xboole_0
      | k3_xboole_0('#skF_2',B_82) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_753,c_156])).

tff(c_174,plain,(
    ! [B_43,A_44] : k3_xboole_0(B_43,A_44) = k3_xboole_0(A_44,B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_18])).

tff(c_206,plain,(
    ! [A_44,B_43] : r1_tarski(k3_xboole_0(A_44,B_43),B_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_6])).

tff(c_958,plain,(
    ! [B_83] :
      ( r1_tarski('#skF_2',B_83)
      | k3_xboole_0(B_83,'#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_816,c_206])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_966,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_958,c_28])).

tff(c_30,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_173,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_30])).

tff(c_967,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_966,c_173])).

tff(c_970,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_967])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:45:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.51/1.44  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.45  
% 2.51/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.51/1.45  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.51/1.45  
% 2.51/1.45  %Foreground sorts:
% 2.51/1.45  
% 2.51/1.45  
% 2.51/1.45  %Background operators:
% 2.51/1.45  
% 2.51/1.45  
% 2.51/1.45  %Foreground operators:
% 2.51/1.45  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.51/1.45  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.51/1.45  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.51/1.45  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.51/1.45  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.51/1.45  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.51/1.45  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.51/1.45  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.51/1.45  tff('#skF_2', type, '#skF_2': $i).
% 2.51/1.45  tff('#skF_3', type, '#skF_3': $i).
% 2.51/1.45  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.51/1.45  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.51/1.45  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.51/1.45  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.51/1.45  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.51/1.45  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.51/1.45  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.51/1.45  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.51/1.45  
% 2.88/1.47  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.88/1.47  tff(f_84, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.88/1.47  tff(f_72, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 2.88/1.47  tff(f_62, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.88/1.47  tff(f_34, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.88/1.47  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.88/1.47  tff(f_32, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.88/1.47  tff(f_30, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.88/1.47  tff(f_50, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 2.88/1.47  tff(f_36, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.88/1.47  tff(f_55, axiom, (![A, B]: (k1_setfam_1(k2_tarski(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_setfam_1)).
% 2.88/1.47  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.88/1.47  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.88/1.47  tff(c_32, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.88/1.47  tff(c_26, plain, (![A_19]: (m1_subset_1('#skF_1'(A_19), A_19) | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.47  tff(c_380, plain, (![A_54, B_55]: (k6_domain_1(A_54, B_55)=k1_tarski(B_55) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.88/1.47  tff(c_406, plain, (![A_61]: (k6_domain_1(A_61, '#skF_1'(A_61))=k1_tarski('#skF_1'(A_61)) | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61))), inference(resolution, [status(thm)], [c_26, c_380])).
% 2.88/1.47  tff(c_24, plain, (![A_19]: (k6_domain_1(A_19, '#skF_1'(A_19))=A_19 | ~v1_zfmisc_1(A_19) | v1_xboole_0(A_19))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.88/1.47  tff(c_421, plain, (![A_62]: (k1_tarski('#skF_1'(A_62))=A_62 | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62) | ~v1_zfmisc_1(A_62) | v1_xboole_0(A_62))), inference(superposition, [status(thm), theory('equality')], [c_406, c_24])).
% 2.88/1.47  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.88/1.47  tff(c_44, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.88/1.47  tff(c_48, plain, (![A_25]: (k1_tarski(A_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_44])).
% 2.88/1.47  tff(c_437, plain, (![A_63]: (k1_xboole_0!=A_63 | ~v1_zfmisc_1(A_63) | v1_xboole_0(A_63) | ~v1_zfmisc_1(A_63) | v1_xboole_0(A_63))), inference(superposition, [status(thm), theory('equality')], [c_421, c_48])).
% 2.88/1.47  tff(c_439, plain, (k1_xboole_0!='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_32, c_437])).
% 2.88/1.47  tff(c_442, plain, (k1_xboole_0!='#skF_2' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_439])).
% 2.88/1.47  tff(c_443, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_442])).
% 2.88/1.47  tff(c_412, plain, (![A_61]: (k1_tarski('#skF_1'(A_61))=A_61 | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61) | ~v1_zfmisc_1(A_61) | v1_xboole_0(A_61))), inference(superposition, [status(thm), theory('equality')], [c_406, c_24])).
% 2.88/1.47  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.88/1.47  tff(c_99, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.88/1.47  tff(c_103, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_6, c_99])).
% 2.88/1.47  tff(c_391, plain, (![C_58, B_59, A_60]: (k1_xboole_0=C_58 | k1_xboole_0=B_59 | C_58=B_59 | k2_xboole_0(B_59, C_58)!=k1_tarski(A_60))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.88/1.47  tff(c_459, plain, (![A_66, B_67, A_68]: (k1_xboole_0=A_66 | k3_xboole_0(A_66, B_67)=k1_xboole_0 | k3_xboole_0(A_66, B_67)=A_66 | k1_tarski(A_68)!=A_66)), inference(superposition, [status(thm), theory('equality')], [c_103, c_391])).
% 2.88/1.47  tff(c_743, plain, (![A_79, B_80]: (k1_xboole_0=A_79 | k3_xboole_0(A_79, B_80)=k1_xboole_0 | k3_xboole_0(A_79, B_80)=A_79 | ~v1_zfmisc_1(A_79) | v1_xboole_0(A_79))), inference(superposition, [status(thm), theory('equality')], [c_412, c_459])).
% 2.88/1.47  tff(c_745, plain, (![B_80]: (k1_xboole_0='#skF_2' | k3_xboole_0('#skF_2', B_80)=k1_xboole_0 | k3_xboole_0('#skF_2', B_80)='#skF_2' | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_32, c_743])).
% 2.88/1.47  tff(c_753, plain, (![B_81]: (k3_xboole_0('#skF_2', B_81)=k1_xboole_0 | k3_xboole_0('#skF_2', B_81)='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_34, c_443, c_745])).
% 2.88/1.47  tff(c_10, plain, (![B_7, A_6]: (k2_tarski(B_7, A_6)=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.88/1.47  tff(c_84, plain, (![A_32, B_33]: (k1_setfam_1(k2_tarski(A_32, B_33))=k3_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.47  tff(c_150, plain, (![A_41, B_42]: (k1_setfam_1(k2_tarski(A_41, B_42))=k3_xboole_0(B_42, A_41))), inference(superposition, [status(thm), theory('equality')], [c_10, c_84])).
% 2.88/1.47  tff(c_18, plain, (![A_15, B_16]: (k1_setfam_1(k2_tarski(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.88/1.47  tff(c_156, plain, (![B_42, A_41]: (k3_xboole_0(B_42, A_41)=k3_xboole_0(A_41, B_42))), inference(superposition, [status(thm), theory('equality')], [c_150, c_18])).
% 2.88/1.47  tff(c_816, plain, (![B_82]: (k3_xboole_0(B_82, '#skF_2')=k1_xboole_0 | k3_xboole_0('#skF_2', B_82)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_753, c_156])).
% 2.88/1.47  tff(c_174, plain, (![B_43, A_44]: (k3_xboole_0(B_43, A_44)=k3_xboole_0(A_44, B_43))), inference(superposition, [status(thm), theory('equality')], [c_150, c_18])).
% 2.88/1.47  tff(c_206, plain, (![A_44, B_43]: (r1_tarski(k3_xboole_0(A_44, B_43), B_43))), inference(superposition, [status(thm), theory('equality')], [c_174, c_6])).
% 2.88/1.47  tff(c_958, plain, (![B_83]: (r1_tarski('#skF_2', B_83) | k3_xboole_0(B_83, '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_816, c_206])).
% 2.88/1.47  tff(c_28, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.88/1.47  tff(c_966, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_958, c_28])).
% 2.88/1.47  tff(c_30, plain, (~v1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.88/1.47  tff(c_173, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_156, c_30])).
% 2.88/1.47  tff(c_967, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_966, c_173])).
% 2.88/1.47  tff(c_970, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2, c_967])).
% 2.88/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.88/1.47  
% 2.88/1.47  Inference rules
% 2.88/1.47  ----------------------
% 2.88/1.47  #Ref     : 1
% 2.88/1.47  #Sup     : 215
% 2.88/1.47  #Fact    : 3
% 2.88/1.47  #Define  : 0
% 2.88/1.47  #Split   : 0
% 2.88/1.47  #Chain   : 0
% 2.88/1.47  #Close   : 0
% 2.88/1.47  
% 2.88/1.47  Ordering : KBO
% 2.88/1.47  
% 2.88/1.47  Simplification rules
% 2.88/1.47  ----------------------
% 2.88/1.47  #Subsume      : 28
% 2.88/1.47  #Demod        : 66
% 2.88/1.47  #Tautology    : 130
% 2.88/1.47  #SimpNegUnit  : 21
% 2.88/1.47  #BackRed      : 2
% 2.88/1.47  
% 2.88/1.47  #Partial instantiations: 0
% 2.88/1.47  #Strategies tried      : 1
% 2.88/1.47  
% 2.88/1.47  Timing (in seconds)
% 2.88/1.47  ----------------------
% 2.88/1.47  Preprocessing        : 0.30
% 2.88/1.47  Parsing              : 0.16
% 2.88/1.47  CNF conversion       : 0.02
% 2.88/1.47  Main loop            : 0.32
% 2.88/1.47  Inferencing          : 0.12
% 2.88/1.47  Reduction            : 0.11
% 2.88/1.47  Demodulation         : 0.08
% 2.88/1.47  BG Simplification    : 0.02
% 2.88/1.47  Subsumption          : 0.05
% 2.88/1.47  Abstraction          : 0.02
% 2.88/1.47  MUC search           : 0.00
% 2.88/1.47  Cooper               : 0.00
% 2.88/1.47  Total                : 0.65
% 2.88/1.47  Index Insertion      : 0.00
% 2.88/1.47  Index Deletion       : 0.00
% 2.88/1.47  Index Matching       : 0.00
% 2.88/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------
