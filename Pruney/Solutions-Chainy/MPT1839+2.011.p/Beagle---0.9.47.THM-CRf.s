%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:22 EST 2020

% Result     : Theorem 3.47s
% Output     : CNFRefutation 3.75s
% Verified   : 
% Statistics : Number of formulae       :   62 (  84 expanded)
%              Number of leaves         :   27 (  40 expanded)
%              Depth                    :   13
%              Number of atoms          :   97 ( 156 expanded)
%              Number of equality atoms :   46 (  56 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_70,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_36,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_24,plain,(
    ! [A_17] :
      ( m1_subset_1('#skF_1'(A_17),A_17)
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_235,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_327,plain,(
    ! [A_53] :
      ( k6_domain_1(A_53,'#skF_1'(A_53)) = k1_tarski('#skF_1'(A_53))
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(resolution,[status(thm)],[c_24,c_235])).

tff(c_22,plain,(
    ! [A_17] :
      ( k6_domain_1(A_17,'#skF_1'(A_17)) = A_17
      | ~ v1_zfmisc_1(A_17)
      | v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_342,plain,(
    ! [A_54] :
      ( k1_tarski('#skF_1'(A_54)) = A_54
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54)
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_22])).

tff(c_10,plain,(
    ! [A_7] : k2_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_25,B_26] : k2_xboole_0(k1_tarski(A_25),B_26) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_48,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_44])).

tff(c_358,plain,(
    ! [A_55] :
      ( k1_xboole_0 != A_55
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55)
      | ~ v1_zfmisc_1(A_55)
      | v1_xboole_0(A_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_48])).

tff(c_360,plain,
    ( k1_xboole_0 != '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_358])).

tff(c_363,plain,
    ( k1_xboole_0 != '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_360])).

tff(c_364,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_363])).

tff(c_333,plain,(
    ! [A_53] :
      ( k1_tarski('#skF_1'(A_53)) = A_53
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53)
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_327,c_22])).

tff(c_8,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_108,plain,(
    ! [A_34,B_35] :
      ( k2_xboole_0(A_34,B_35) = B_35
      | ~ r1_tarski(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_116,plain,(
    ! [A_5,B_6] : k2_xboole_0(k3_xboole_0(A_5,B_6),A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_8,c_108])).

tff(c_305,plain,(
    ! [C_48,B_49,A_50] :
      ( k1_xboole_0 = C_48
      | k1_xboole_0 = B_49
      | C_48 = B_49
      | k2_xboole_0(B_49,C_48) != k1_tarski(A_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_380,plain,(
    ! [A_58,B_59,A_60] :
      ( k1_xboole_0 = A_58
      | k3_xboole_0(A_58,B_59) = k1_xboole_0
      | k3_xboole_0(A_58,B_59) = A_58
      | k1_tarski(A_60) != A_58 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_305])).

tff(c_978,plain,(
    ! [A_78,B_79] :
      ( k1_xboole_0 = A_78
      | k3_xboole_0(A_78,B_79) = k1_xboole_0
      | k3_xboole_0(A_78,B_79) = A_78
      | ~ v1_zfmisc_1(A_78)
      | v1_xboole_0(A_78) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_333,c_380])).

tff(c_980,plain,(
    ! [B_79] :
      ( k1_xboole_0 = '#skF_2'
      | k3_xboole_0('#skF_2',B_79) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_79) = '#skF_2'
      | v1_xboole_0('#skF_2') ) ),
    inference(resolution,[status(thm)],[c_30,c_978])).

tff(c_988,plain,(
    ! [B_80] :
      ( k3_xboole_0('#skF_2',B_80) = k1_xboole_0
      | k3_xboole_0('#skF_2',B_80) = '#skF_2' ) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_364,c_980])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1064,plain,(
    ! [B_81] :
      ( k3_xboole_0(B_81,'#skF_2') = k1_xboole_0
      | k3_xboole_0('#skF_2',B_81) = '#skF_2' ) ),
    inference(superposition,[status(thm),theory(equality)],[c_988,c_2])).

tff(c_50,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [B_28,A_29] : r1_tarski(k3_xboole_0(B_28,A_29),A_29) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_8])).

tff(c_1221,plain,(
    ! [B_82] :
      ( r1_tarski('#skF_2',B_82)
      | k3_xboole_0(B_82,'#skF_2') = k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1064,c_65])).

tff(c_26,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1229,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_1221,c_26])).

tff(c_28,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_33,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_1230,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1229,c_33])).

tff(c_1233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_1230])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:16:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.47/1.90  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.90  
% 3.75/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.91  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 3.75/1.91  
% 3.75/1.91  %Foreground sorts:
% 3.75/1.91  
% 3.75/1.91  
% 3.75/1.91  %Background operators:
% 3.75/1.91  
% 3.75/1.91  
% 3.75/1.91  %Foreground operators:
% 3.75/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.75/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.75/1.91  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.75/1.91  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.75/1.91  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 3.75/1.91  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.75/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.75/1.91  tff('#skF_2', type, '#skF_2': $i).
% 3.75/1.91  tff('#skF_3', type, '#skF_3': $i).
% 3.75/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.75/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.75/1.91  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 3.75/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.75/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.75/1.91  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.75/1.91  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.75/1.91  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 3.75/1.91  
% 3.75/1.93  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.75/1.93  tff(f_82, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_tex_2)).
% 3.75/1.93  tff(f_70, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tex_2)).
% 3.75/1.93  tff(f_60, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 3.75/1.93  tff(f_36, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 3.75/1.93  tff(f_51, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.75/1.93  tff(f_34, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.75/1.93  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.75/1.93  tff(f_48, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 3.75/1.93  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.75/1.93  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 3.75/1.93  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.75/1.93  tff(c_30, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.75/1.93  tff(c_24, plain, (![A_17]: (m1_subset_1('#skF_1'(A_17), A_17) | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.93  tff(c_235, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.75/1.93  tff(c_327, plain, (![A_53]: (k6_domain_1(A_53, '#skF_1'(A_53))=k1_tarski('#skF_1'(A_53)) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(resolution, [status(thm)], [c_24, c_235])).
% 3.75/1.93  tff(c_22, plain, (![A_17]: (k6_domain_1(A_17, '#skF_1'(A_17))=A_17 | ~v1_zfmisc_1(A_17) | v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_70])).
% 3.75/1.93  tff(c_342, plain, (![A_54]: (k1_tarski('#skF_1'(A_54))=A_54 | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(superposition, [status(thm), theory('equality')], [c_327, c_22])).
% 3.75/1.93  tff(c_10, plain, (![A_7]: (k2_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.75/1.93  tff(c_44, plain, (![A_25, B_26]: (k2_xboole_0(k1_tarski(A_25), B_26)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.75/1.93  tff(c_48, plain, (![A_25]: (k1_tarski(A_25)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_44])).
% 3.75/1.93  tff(c_358, plain, (![A_55]: (k1_xboole_0!=A_55 | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55) | ~v1_zfmisc_1(A_55) | v1_xboole_0(A_55))), inference(superposition, [status(thm), theory('equality')], [c_342, c_48])).
% 3.75/1.93  tff(c_360, plain, (k1_xboole_0!='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_358])).
% 3.75/1.93  tff(c_363, plain, (k1_xboole_0!='#skF_2' | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_360])).
% 3.75/1.93  tff(c_364, plain, (k1_xboole_0!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_363])).
% 3.75/1.93  tff(c_333, plain, (![A_53]: (k1_tarski('#skF_1'(A_53))=A_53 | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(superposition, [status(thm), theory('equality')], [c_327, c_22])).
% 3.75/1.93  tff(c_8, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 3.75/1.93  tff(c_108, plain, (![A_34, B_35]: (k2_xboole_0(A_34, B_35)=B_35 | ~r1_tarski(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.75/1.93  tff(c_116, plain, (![A_5, B_6]: (k2_xboole_0(k3_xboole_0(A_5, B_6), A_5)=A_5)), inference(resolution, [status(thm)], [c_8, c_108])).
% 3.75/1.93  tff(c_305, plain, (![C_48, B_49, A_50]: (k1_xboole_0=C_48 | k1_xboole_0=B_49 | C_48=B_49 | k2_xboole_0(B_49, C_48)!=k1_tarski(A_50))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.75/1.93  tff(c_380, plain, (![A_58, B_59, A_60]: (k1_xboole_0=A_58 | k3_xboole_0(A_58, B_59)=k1_xboole_0 | k3_xboole_0(A_58, B_59)=A_58 | k1_tarski(A_60)!=A_58)), inference(superposition, [status(thm), theory('equality')], [c_116, c_305])).
% 3.75/1.93  tff(c_978, plain, (![A_78, B_79]: (k1_xboole_0=A_78 | k3_xboole_0(A_78, B_79)=k1_xboole_0 | k3_xboole_0(A_78, B_79)=A_78 | ~v1_zfmisc_1(A_78) | v1_xboole_0(A_78))), inference(superposition, [status(thm), theory('equality')], [c_333, c_380])).
% 3.75/1.93  tff(c_980, plain, (![B_79]: (k1_xboole_0='#skF_2' | k3_xboole_0('#skF_2', B_79)=k1_xboole_0 | k3_xboole_0('#skF_2', B_79)='#skF_2' | v1_xboole_0('#skF_2'))), inference(resolution, [status(thm)], [c_30, c_978])).
% 3.75/1.93  tff(c_988, plain, (![B_80]: (k3_xboole_0('#skF_2', B_80)=k1_xboole_0 | k3_xboole_0('#skF_2', B_80)='#skF_2')), inference(negUnitSimplification, [status(thm)], [c_32, c_364, c_980])).
% 3.75/1.93  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.75/1.93  tff(c_1064, plain, (![B_81]: (k3_xboole_0(B_81, '#skF_2')=k1_xboole_0 | k3_xboole_0('#skF_2', B_81)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_988, c_2])).
% 3.75/1.93  tff(c_50, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.75/1.93  tff(c_65, plain, (![B_28, A_29]: (r1_tarski(k3_xboole_0(B_28, A_29), A_29))), inference(superposition, [status(thm), theory('equality')], [c_50, c_8])).
% 3.75/1.93  tff(c_1221, plain, (![B_82]: (r1_tarski('#skF_2', B_82) | k3_xboole_0(B_82, '#skF_2')=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1064, c_65])).
% 3.75/1.93  tff(c_26, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.75/1.93  tff(c_1229, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_1221, c_26])).
% 3.75/1.93  tff(c_28, plain, (~v1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.75/1.93  tff(c_33, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_28])).
% 3.75/1.93  tff(c_1230, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_1229, c_33])).
% 3.75/1.93  tff(c_1233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_1230])).
% 3.75/1.93  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.75/1.93  
% 3.75/1.93  Inference rules
% 3.75/1.93  ----------------------
% 3.75/1.93  #Ref     : 2
% 3.75/1.93  #Sup     : 270
% 3.75/1.93  #Fact    : 4
% 3.75/1.93  #Define  : 0
% 3.75/1.93  #Split   : 0
% 3.75/1.93  #Chain   : 0
% 3.75/1.93  #Close   : 0
% 3.75/1.93  
% 3.75/1.93  Ordering : KBO
% 3.75/1.93  
% 3.75/1.93  Simplification rules
% 3.75/1.93  ----------------------
% 3.75/1.93  #Subsume      : 54
% 3.75/1.93  #Demod        : 74
% 3.75/1.93  #Tautology    : 150
% 3.75/1.93  #SimpNegUnit  : 42
% 3.75/1.93  #BackRed      : 1
% 3.75/1.93  
% 3.75/1.93  #Partial instantiations: 0
% 3.75/1.93  #Strategies tried      : 1
% 3.75/1.93  
% 3.75/1.93  Timing (in seconds)
% 3.75/1.93  ----------------------
% 3.75/1.94  Preprocessing        : 0.49
% 3.75/1.94  Parsing              : 0.26
% 3.75/1.94  CNF conversion       : 0.03
% 3.75/1.94  Main loop            : 0.60
% 3.75/1.94  Inferencing          : 0.22
% 3.75/1.94  Reduction            : 0.21
% 3.75/1.94  Demodulation         : 0.15
% 3.75/1.94  BG Simplification    : 0.03
% 3.75/1.94  Subsumption          : 0.11
% 3.75/1.94  Abstraction          : 0.03
% 3.75/1.94  MUC search           : 0.00
% 3.75/1.94  Cooper               : 0.00
% 3.75/1.94  Total                : 1.14
% 3.75/1.94  Index Insertion      : 0.00
% 3.75/1.94  Index Deletion       : 0.00
% 3.75/1.94  Index Matching       : 0.00
% 3.75/1.94  BG Taut test         : 0.00
%------------------------------------------------------------------------------
