%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:31 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.66s
% Verified   : 
% Statistics : Number of formulae       :   66 (  85 expanded)
%              Number of leaves         :   33 (  43 expanded)
%              Depth                    :   11
%              Number of atoms          :   78 ( 126 expanded)
%              Number of equality atoms :   23 (  29 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_48,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_105,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_79,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_93,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_18,plain,(
    ! [A_14] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_62,plain,(
    ! [A_37,B_38] :
      ( r1_tarski(A_37,B_38)
      | ~ m1_subset_1(A_37,k1_zfmisc_1(B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_66,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(resolution,[status(thm)],[c_18,c_62])).

tff(c_68,plain,(
    ! [A_40,B_41] :
      ( k3_xboole_0(A_40,B_41) = A_40
      | ~ r1_tarski(A_40,B_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_72,plain,(
    ! [A_14] : k3_xboole_0(k1_xboole_0,A_14) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_66,c_68])).

tff(c_103,plain,(
    ! [A_49,B_50] : k5_xboole_0(A_49,k3_xboole_0(A_49,B_50)) = k4_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_112,plain,(
    ! [A_14] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_14) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_103])).

tff(c_116,plain,(
    ! [A_51] : k4_xboole_0(k1_xboole_0,A_51) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_112])).

tff(c_10,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k4_xboole_0(B_8,A_7)) = k2_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_121,plain,(
    ! [A_51] : k5_xboole_0(A_51,k1_xboole_0) = k2_xboole_0(A_51,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_10])).

tff(c_127,plain,(
    ! [A_52] : k2_xboole_0(A_52,k1_xboole_0) = A_52 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_121])).

tff(c_16,plain,(
    ! [A_12,B_13] : k2_xboole_0(k1_tarski(A_12),B_13) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_134,plain,(
    ! [A_12] : k1_tarski(A_12) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_16])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_277,plain,(
    ! [A_73,B_74] :
      ( k6_domain_1(A_73,B_74) = k1_tarski(B_74)
      | ~ m1_subset_1(B_74,A_73)
      | v1_xboole_0(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_286,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_277])).

tff(c_291,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_286])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_292,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_291,c_36])).

tff(c_319,plain,(
    ! [A_82,B_83] :
      ( m1_subset_1(k6_domain_1(A_82,B_83),k1_zfmisc_1(A_82))
      | ~ m1_subset_1(B_83,A_82)
      | v1_xboole_0(A_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_336,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_291,c_319])).

tff(c_344,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_336])).

tff(c_345,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_344])).

tff(c_407,plain,(
    ! [B_90,A_91] :
      ( ~ v1_subset_1(B_90,A_91)
      | v1_xboole_0(B_90)
      | ~ m1_subset_1(B_90,k1_zfmisc_1(A_91))
      | ~ v1_zfmisc_1(A_91)
      | v1_xboole_0(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_410,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_345,c_407])).

tff(c_422,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_292,c_410])).

tff(c_423,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_422])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_430,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_423,c_2])).

tff(c_434,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_134,c_430])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:39:27 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.38  
% 2.40/1.38  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.39  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.40/1.39  
% 2.40/1.39  %Foreground sorts:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Background operators:
% 2.40/1.39  
% 2.40/1.39  
% 2.40/1.39  %Foreground operators:
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.39  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.40/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.40/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.39  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.40/1.39  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.40/1.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.40/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.40/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.40/1.39  tff('#skF_2', type, '#skF_2': $i).
% 2.40/1.39  tff('#skF_1', type, '#skF_1': $i).
% 2.40/1.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.39  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.40/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.39  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.40/1.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.40/1.39  
% 2.66/1.40  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.66/1.40  tff(f_48, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 2.66/1.40  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.66/1.40  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.66/1.40  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.66/1.40  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.66/1.40  tff(f_46, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.66/1.40  tff(f_105, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.66/1.40  tff(f_79, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.66/1.40  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.66/1.40  tff(f_93, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.66/1.40  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.66/1.40  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.66/1.40  tff(c_18, plain, (![A_14]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.66/1.40  tff(c_62, plain, (![A_37, B_38]: (r1_tarski(A_37, B_38) | ~m1_subset_1(A_37, k1_zfmisc_1(B_38)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.66/1.40  tff(c_66, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(resolution, [status(thm)], [c_18, c_62])).
% 2.66/1.40  tff(c_68, plain, (![A_40, B_41]: (k3_xboole_0(A_40, B_41)=A_40 | ~r1_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.66/1.40  tff(c_72, plain, (![A_14]: (k3_xboole_0(k1_xboole_0, A_14)=k1_xboole_0)), inference(resolution, [status(thm)], [c_66, c_68])).
% 2.66/1.40  tff(c_103, plain, (![A_49, B_50]: (k5_xboole_0(A_49, k3_xboole_0(A_49, B_50))=k4_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.66/1.40  tff(c_112, plain, (![A_14]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_14))), inference(superposition, [status(thm), theory('equality')], [c_72, c_103])).
% 2.66/1.40  tff(c_116, plain, (![A_51]: (k4_xboole_0(k1_xboole_0, A_51)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_112])).
% 2.66/1.40  tff(c_10, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k4_xboole_0(B_8, A_7))=k2_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.66/1.40  tff(c_121, plain, (![A_51]: (k5_xboole_0(A_51, k1_xboole_0)=k2_xboole_0(A_51, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_116, c_10])).
% 2.66/1.40  tff(c_127, plain, (![A_52]: (k2_xboole_0(A_52, k1_xboole_0)=A_52)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_121])).
% 2.66/1.40  tff(c_16, plain, (![A_12, B_13]: (k2_xboole_0(k1_tarski(A_12), B_13)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.66/1.40  tff(c_134, plain, (![A_12]: (k1_tarski(A_12)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_127, c_16])).
% 2.66/1.40  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.66/1.40  tff(c_34, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.66/1.40  tff(c_38, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.66/1.40  tff(c_277, plain, (![A_73, B_74]: (k6_domain_1(A_73, B_74)=k1_tarski(B_74) | ~m1_subset_1(B_74, A_73) | v1_xboole_0(A_73))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.66/1.40  tff(c_286, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_277])).
% 2.66/1.40  tff(c_291, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_286])).
% 2.66/1.40  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_105])).
% 2.66/1.40  tff(c_292, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_291, c_36])).
% 2.66/1.40  tff(c_319, plain, (![A_82, B_83]: (m1_subset_1(k6_domain_1(A_82, B_83), k1_zfmisc_1(A_82)) | ~m1_subset_1(B_83, A_82) | v1_xboole_0(A_82))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.66/1.40  tff(c_336, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_291, c_319])).
% 2.66/1.40  tff(c_344, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_336])).
% 2.66/1.40  tff(c_345, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_344])).
% 2.66/1.40  tff(c_407, plain, (![B_90, A_91]: (~v1_subset_1(B_90, A_91) | v1_xboole_0(B_90) | ~m1_subset_1(B_90, k1_zfmisc_1(A_91)) | ~v1_zfmisc_1(A_91) | v1_xboole_0(A_91))), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.66/1.40  tff(c_410, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_345, c_407])).
% 2.66/1.40  tff(c_422, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_292, c_410])).
% 2.66/1.40  tff(c_423, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_422])).
% 2.66/1.40  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.66/1.40  tff(c_430, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_423, c_2])).
% 2.66/1.40  tff(c_434, plain, $false, inference(negUnitSimplification, [status(thm)], [c_134, c_430])).
% 2.66/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.66/1.40  
% 2.66/1.40  Inference rules
% 2.66/1.40  ----------------------
% 2.66/1.40  #Ref     : 0
% 2.66/1.40  #Sup     : 90
% 2.66/1.40  #Fact    : 0
% 2.66/1.40  #Define  : 0
% 2.66/1.40  #Split   : 2
% 2.66/1.40  #Chain   : 0
% 2.66/1.40  #Close   : 0
% 2.66/1.40  
% 2.66/1.40  Ordering : KBO
% 2.66/1.40  
% 2.66/1.40  Simplification rules
% 2.66/1.40  ----------------------
% 2.66/1.40  #Subsume      : 6
% 2.66/1.40  #Demod        : 17
% 2.66/1.40  #Tautology    : 35
% 2.66/1.40  #SimpNegUnit  : 10
% 2.66/1.40  #BackRed      : 2
% 2.66/1.40  
% 2.66/1.40  #Partial instantiations: 0
% 2.66/1.40  #Strategies tried      : 1
% 2.66/1.40  
% 2.66/1.40  Timing (in seconds)
% 2.66/1.40  ----------------------
% 2.66/1.41  Preprocessing        : 0.32
% 2.66/1.41  Parsing              : 0.18
% 2.66/1.41  CNF conversion       : 0.02
% 2.66/1.41  Main loop            : 0.24
% 2.66/1.41  Inferencing          : 0.10
% 2.66/1.41  Reduction            : 0.07
% 2.66/1.41  Demodulation         : 0.05
% 2.66/1.41  BG Simplification    : 0.01
% 2.66/1.41  Subsumption          : 0.04
% 2.66/1.41  Abstraction          : 0.02
% 2.66/1.41  MUC search           : 0.00
% 2.66/1.41  Cooper               : 0.00
% 2.66/1.41  Total                : 0.60
% 2.66/1.41  Index Insertion      : 0.00
% 2.66/1.41  Index Deletion       : 0.00
% 2.66/1.41  Index Matching       : 0.00
% 2.66/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
