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
% DateTime   : Thu Dec  3 10:28:35 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 106 expanded)
%              Number of leaves         :   28 (  48 expanded)
%              Depth                    :    9
%              Number of atoms          :   78 ( 157 expanded)
%              Number of equality atoms :   32 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k6_domain_1,type,(
    k6_domain_1: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_37,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_35,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_42,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_64,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_78,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_10,plain,(
    ! [A_7] : k4_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_6] : k3_xboole_0(A_6,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_163,plain,(
    ! [A_34,B_35] : k5_xboole_0(A_34,k3_xboole_0(A_34,B_35)) = k4_xboole_0(A_34,B_35) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = k4_xboole_0(A_6,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_163])).

tff(c_195,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_189])).

tff(c_196,plain,(
    ! [A_36] : k5_xboole_0(A_36,k1_xboole_0) = A_36 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_189])).

tff(c_96,plain,(
    ! [A_30,B_31] : k5_xboole_0(A_30,k4_xboole_0(B_31,A_30)) = k2_xboole_0(A_30,B_31) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_105,plain,(
    ! [A_7] : k5_xboole_0(k1_xboole_0,A_7) = k2_xboole_0(k1_xboole_0,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_96])).

tff(c_203,plain,(
    k2_xboole_0(k1_xboole_0,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_105])).

tff(c_49,plain,(
    ! [B_28,A_29] : k3_xboole_0(B_28,A_29) = k3_xboole_0(A_29,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_65,plain,(
    ! [A_29] : k3_xboole_0(k1_xboole_0,A_29) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_8])).

tff(c_170,plain,(
    ! [B_35] : k2_xboole_0(k1_xboole_0,k3_xboole_0(k1_xboole_0,B_35)) = k4_xboole_0(k1_xboole_0,B_35) ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_105])).

tff(c_191,plain,(
    ! [B_35] : k4_xboole_0(k1_xboole_0,B_35) = k2_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_65,c_170])).

tff(c_220,plain,(
    ! [B_39] : k4_xboole_0(k1_xboole_0,B_39) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_191])).

tff(c_12,plain,(
    ! [A_8,B_9] : k5_xboole_0(A_8,k4_xboole_0(B_9,A_8)) = k2_xboole_0(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_225,plain,(
    ! [B_39] : k5_xboole_0(B_39,k1_xboole_0) = k2_xboole_0(B_39,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_12])).

tff(c_242,plain,(
    ! [B_40] : k2_xboole_0(B_40,k1_xboole_0) = B_40 ),
    inference(demodulation,[status(thm),theory(equality)],[c_195,c_225])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),B_11) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_249,plain,(
    ! [A_10] : k1_tarski(A_10) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_14])).

tff(c_30,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_28,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_24,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_258,plain,(
    ! [A_42,B_43] :
      ( k6_domain_1(A_42,B_43) = k1_tarski(B_43)
      | ~ m1_subset_1(B_43,A_42)
      | v1_xboole_0(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_261,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_28,c_258])).

tff(c_264,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_261])).

tff(c_26,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_265,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_264,c_26])).

tff(c_18,plain,(
    ! [A_15,B_16] :
      ( m1_subset_1(k6_domain_1(A_15,B_16),k1_zfmisc_1(A_15))
      | ~ m1_subset_1(B_16,A_15)
      | v1_xboole_0(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_425,plain,(
    ! [B_52,A_53] :
      ( ~ v1_subset_1(B_52,A_53)
      | v1_xboole_0(B_52)
      | ~ m1_subset_1(B_52,k1_zfmisc_1(A_53))
      | ~ v1_zfmisc_1(A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_443,plain,(
    ! [A_54,B_55] :
      ( ~ v1_subset_1(k6_domain_1(A_54,B_55),A_54)
      | v1_xboole_0(k6_domain_1(A_54,B_55))
      | ~ v1_zfmisc_1(A_54)
      | ~ m1_subset_1(B_55,A_54)
      | v1_xboole_0(A_54) ) ),
    inference(resolution,[status(thm)],[c_18,c_425])).

tff(c_449,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k6_domain_1('#skF_1','#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_264,c_443])).

tff(c_454,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_24,c_264,c_265,c_449])).

tff(c_455,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_454])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_458,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_455,c_4])).

tff(c_462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_249,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n003.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:47:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  
% 2.27/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.34  %$ v1_subset_1 > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.27/1.34  
% 2.27/1.34  %Foreground sorts:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Background operators:
% 2.27/1.34  
% 2.27/1.34  
% 2.27/1.34  %Foreground operators:
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.34  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.27/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.34  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.27/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.34  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.27/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.34  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.27/1.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.34  
% 2.27/1.35  tff(f_37, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.27/1.35  tff(f_35, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 2.27/1.35  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.27/1.35  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.27/1.35  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.27/1.35  tff(f_42, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.27/1.35  tff(f_90, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.27/1.35  tff(f_64, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.27/1.35  tff(f_57, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.27/1.35  tff(f_78, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.27/1.35  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.27/1.35  tff(c_10, plain, (![A_7]: (k4_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.27/1.35  tff(c_8, plain, (![A_6]: (k3_xboole_0(A_6, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.27/1.35  tff(c_163, plain, (![A_34, B_35]: (k5_xboole_0(A_34, k3_xboole_0(A_34, B_35))=k4_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.35  tff(c_189, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=k4_xboole_0(A_6, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_8, c_163])).
% 2.27/1.35  tff(c_195, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_189])).
% 2.27/1.35  tff(c_196, plain, (![A_36]: (k5_xboole_0(A_36, k1_xboole_0)=A_36)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_189])).
% 2.27/1.35  tff(c_96, plain, (![A_30, B_31]: (k5_xboole_0(A_30, k4_xboole_0(B_31, A_30))=k2_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.35  tff(c_105, plain, (![A_7]: (k5_xboole_0(k1_xboole_0, A_7)=k2_xboole_0(k1_xboole_0, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_96])).
% 2.27/1.35  tff(c_203, plain, (k2_xboole_0(k1_xboole_0, k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_196, c_105])).
% 2.27/1.35  tff(c_49, plain, (![B_28, A_29]: (k3_xboole_0(B_28, A_29)=k3_xboole_0(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.35  tff(c_65, plain, (![A_29]: (k3_xboole_0(k1_xboole_0, A_29)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_49, c_8])).
% 2.27/1.35  tff(c_170, plain, (![B_35]: (k2_xboole_0(k1_xboole_0, k3_xboole_0(k1_xboole_0, B_35))=k4_xboole_0(k1_xboole_0, B_35))), inference(superposition, [status(thm), theory('equality')], [c_163, c_105])).
% 2.27/1.35  tff(c_191, plain, (![B_35]: (k4_xboole_0(k1_xboole_0, B_35)=k2_xboole_0(k1_xboole_0, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_65, c_170])).
% 2.27/1.35  tff(c_220, plain, (![B_39]: (k4_xboole_0(k1_xboole_0, B_39)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_203, c_191])).
% 2.27/1.35  tff(c_12, plain, (![A_8, B_9]: (k5_xboole_0(A_8, k4_xboole_0(B_9, A_8))=k2_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.35  tff(c_225, plain, (![B_39]: (k5_xboole_0(B_39, k1_xboole_0)=k2_xboole_0(B_39, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_220, c_12])).
% 2.27/1.35  tff(c_242, plain, (![B_40]: (k2_xboole_0(B_40, k1_xboole_0)=B_40)), inference(demodulation, [status(thm), theory('equality')], [c_195, c_225])).
% 2.27/1.35  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.27/1.35  tff(c_249, plain, (![A_10]: (k1_tarski(A_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_242, c_14])).
% 2.27/1.35  tff(c_30, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.27/1.35  tff(c_28, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.27/1.35  tff(c_24, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.27/1.35  tff(c_258, plain, (![A_42, B_43]: (k6_domain_1(A_42, B_43)=k1_tarski(B_43) | ~m1_subset_1(B_43, A_42) | v1_xboole_0(A_42))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.35  tff(c_261, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_28, c_258])).
% 2.27/1.35  tff(c_264, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_30, c_261])).
% 2.27/1.35  tff(c_26, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.27/1.35  tff(c_265, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_264, c_26])).
% 2.27/1.35  tff(c_18, plain, (![A_15, B_16]: (m1_subset_1(k6_domain_1(A_15, B_16), k1_zfmisc_1(A_15)) | ~m1_subset_1(B_16, A_15) | v1_xboole_0(A_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.27/1.35  tff(c_425, plain, (![B_52, A_53]: (~v1_subset_1(B_52, A_53) | v1_xboole_0(B_52) | ~m1_subset_1(B_52, k1_zfmisc_1(A_53)) | ~v1_zfmisc_1(A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.27/1.35  tff(c_443, plain, (![A_54, B_55]: (~v1_subset_1(k6_domain_1(A_54, B_55), A_54) | v1_xboole_0(k6_domain_1(A_54, B_55)) | ~v1_zfmisc_1(A_54) | ~m1_subset_1(B_55, A_54) | v1_xboole_0(A_54))), inference(resolution, [status(thm)], [c_18, c_425])).
% 2.27/1.35  tff(c_449, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k6_domain_1('#skF_1', '#skF_2')) | ~v1_zfmisc_1('#skF_1') | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_264, c_443])).
% 2.27/1.35  tff(c_454, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_24, c_264, c_265, c_449])).
% 2.27/1.35  tff(c_455, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_30, c_454])).
% 2.27/1.35  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.35  tff(c_458, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_455, c_4])).
% 2.27/1.35  tff(c_462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_249, c_458])).
% 2.27/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  Inference rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Ref     : 0
% 2.27/1.35  #Sup     : 95
% 2.27/1.35  #Fact    : 0
% 2.27/1.35  #Define  : 0
% 2.27/1.35  #Split   : 1
% 2.27/1.35  #Chain   : 0
% 2.27/1.35  #Close   : 0
% 2.27/1.35  
% 2.27/1.35  Ordering : KBO
% 2.27/1.35  
% 2.27/1.35  Simplification rules
% 2.27/1.35  ----------------------
% 2.27/1.35  #Subsume      : 3
% 2.27/1.35  #Demod        : 55
% 2.27/1.35  #Tautology    : 67
% 2.27/1.35  #SimpNegUnit  : 11
% 2.27/1.35  #BackRed      : 3
% 2.27/1.35  
% 2.27/1.35  #Partial instantiations: 0
% 2.27/1.35  #Strategies tried      : 1
% 2.27/1.35  
% 2.27/1.35  Timing (in seconds)
% 2.27/1.35  ----------------------
% 2.27/1.36  Preprocessing        : 0.32
% 2.27/1.36  Parsing              : 0.18
% 2.27/1.36  CNF conversion       : 0.02
% 2.27/1.36  Main loop            : 0.23
% 2.27/1.36  Inferencing          : 0.09
% 2.27/1.36  Reduction            : 0.08
% 2.27/1.36  Demodulation         : 0.06
% 2.27/1.36  BG Simplification    : 0.01
% 2.27/1.36  Subsumption          : 0.04
% 2.27/1.36  Abstraction          : 0.01
% 2.27/1.36  MUC search           : 0.00
% 2.27/1.36  Cooper               : 0.00
% 2.27/1.36  Total                : 0.59
% 2.27/1.36  Index Insertion      : 0.00
% 2.27/1.36  Index Deletion       : 0.00
% 2.27/1.36  Index Matching       : 0.00
% 2.27/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------
