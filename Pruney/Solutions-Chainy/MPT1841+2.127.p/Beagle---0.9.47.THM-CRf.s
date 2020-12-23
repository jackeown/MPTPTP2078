%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:45 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 118 expanded)
%              Number of leaves         :   32 (  52 expanded)
%              Depth                    :   13
%              Number of atoms          :   91 ( 214 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_49,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_54,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_51,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_103,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_78,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_71,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_40,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_16,plain,(
    ! [A_12] : k2_subset_1(A_12) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_14] : ~ v1_subset_1(k2_subset_1(A_14),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_41,plain,(
    ! [A_14] : ~ v1_subset_1(A_14,A_14) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_20])).

tff(c_18,plain,(
    ! [A_13] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_133,plain,(
    ! [A_45,B_46] :
      ( r1_tarski(A_45,B_46)
      | ~ m1_subset_1(A_45,k1_zfmisc_1(B_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_141,plain,(
    ! [A_13] : r1_tarski(k1_xboole_0,A_13) ),
    inference(resolution,[status(thm)],[c_18,c_133])).

tff(c_143,plain,(
    ! [A_48,B_49] :
      ( k2_xboole_0(A_48,B_49) = B_49
      | ~ r1_tarski(A_48,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_148,plain,(
    ! [A_50] : k2_xboole_0(k1_xboole_0,A_50) = A_50 ),
    inference(resolution,[status(thm)],[c_141,c_143])).

tff(c_73,plain,(
    ! [B_37,A_38] : k2_xboole_0(B_37,A_38) = k2_xboole_0(A_38,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),B_11) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [B_37,A_10] : k2_xboole_0(B_37,k1_tarski(A_10)) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_73,c_14])).

tff(c_155,plain,(
    ! [A_10] : k1_tarski(A_10) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_148,c_89])).

tff(c_40,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_34,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_38,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_219,plain,(
    ! [A_53,B_54] :
      ( k6_domain_1(A_53,B_54) = k1_tarski(B_54)
      | ~ m1_subset_1(B_54,A_53)
      | v1_xboole_0(A_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_228,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_38,c_219])).

tff(c_233,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_228])).

tff(c_266,plain,(
    ! [A_65,B_66] :
      ( m1_subset_1(k6_domain_1(A_65,B_66),k1_zfmisc_1(A_65))
      | ~ m1_subset_1(B_66,A_65)
      | v1_xboole_0(A_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_280,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_266])).

tff(c_287,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_280])).

tff(c_288,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_287])).

tff(c_22,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_305,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_288,c_22])).

tff(c_32,plain,(
    ! [B_26,A_24] :
      ( B_26 = A_24
      | ~ r1_tarski(A_24,B_26)
      | ~ v1_zfmisc_1(B_26)
      | v1_xboole_0(B_26)
      | v1_xboole_0(A_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_308,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_305,c_32])).

tff(c_314,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_308])).

tff(c_315,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_314])).

tff(c_335,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_315])).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_63,plain,(
    ! [B_34,A_35] :
      ( ~ v1_xboole_0(B_34)
      | B_34 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_66,plain,(
    ! [A_35] :
      ( k1_xboole_0 = A_35
      | ~ v1_xboole_0(A_35) ) ),
    inference(resolution,[status(thm)],[c_4,c_63])).

tff(c_338,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_335,c_66])).

tff(c_344,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_155,c_338])).

tff(c_345,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_315])).

tff(c_36,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_235,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_233,c_36])).

tff(c_350,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_235])).

tff(c_353,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_350])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:38:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  
% 2.06/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.29  %$ v1_subset_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.29  
% 2.06/1.29  %Foreground sorts:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Background operators:
% 2.06/1.29  
% 2.06/1.29  
% 2.06/1.29  %Foreground operators:
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.06/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.06/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.29  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.29  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.06/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.29  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.06/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.06/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.06/1.29  
% 2.06/1.31  tff(f_49, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.06/1.31  tff(f_54, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.06/1.31  tff(f_51, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 2.06/1.31  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.06/1.31  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.06/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.31  tff(f_47, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.06/1.31  tff(f_103, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.06/1.31  tff(f_78, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.06/1.31  tff(f_71, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.06/1.31  tff(f_91, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.06/1.31  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.06/1.31  tff(f_40, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.06/1.31  tff(c_16, plain, (![A_12]: (k2_subset_1(A_12)=A_12)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.06/1.31  tff(c_20, plain, (![A_14]: (~v1_subset_1(k2_subset_1(A_14), A_14))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.06/1.31  tff(c_41, plain, (![A_14]: (~v1_subset_1(A_14, A_14))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_20])).
% 2.06/1.31  tff(c_18, plain, (![A_13]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.06/1.31  tff(c_133, plain, (![A_45, B_46]: (r1_tarski(A_45, B_46) | ~m1_subset_1(A_45, k1_zfmisc_1(B_46)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.31  tff(c_141, plain, (![A_13]: (r1_tarski(k1_xboole_0, A_13))), inference(resolution, [status(thm)], [c_18, c_133])).
% 2.06/1.31  tff(c_143, plain, (![A_48, B_49]: (k2_xboole_0(A_48, B_49)=B_49 | ~r1_tarski(A_48, B_49))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.06/1.31  tff(c_148, plain, (![A_50]: (k2_xboole_0(k1_xboole_0, A_50)=A_50)), inference(resolution, [status(thm)], [c_141, c_143])).
% 2.06/1.31  tff(c_73, plain, (![B_37, A_38]: (k2_xboole_0(B_37, A_38)=k2_xboole_0(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.31  tff(c_14, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), B_11)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.31  tff(c_89, plain, (![B_37, A_10]: (k2_xboole_0(B_37, k1_tarski(A_10))!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_73, c_14])).
% 2.06/1.31  tff(c_155, plain, (![A_10]: (k1_tarski(A_10)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_148, c_89])).
% 2.06/1.31  tff(c_40, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.06/1.31  tff(c_34, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.06/1.31  tff(c_38, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.06/1.31  tff(c_219, plain, (![A_53, B_54]: (k6_domain_1(A_53, B_54)=k1_tarski(B_54) | ~m1_subset_1(B_54, A_53) | v1_xboole_0(A_53))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.06/1.31  tff(c_228, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_38, c_219])).
% 2.06/1.31  tff(c_233, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_40, c_228])).
% 2.06/1.31  tff(c_266, plain, (![A_65, B_66]: (m1_subset_1(k6_domain_1(A_65, B_66), k1_zfmisc_1(A_65)) | ~m1_subset_1(B_66, A_65) | v1_xboole_0(A_65))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.06/1.31  tff(c_280, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_233, c_266])).
% 2.06/1.31  tff(c_287, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_280])).
% 2.06/1.31  tff(c_288, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_40, c_287])).
% 2.06/1.31  tff(c_22, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.31  tff(c_305, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_288, c_22])).
% 2.06/1.31  tff(c_32, plain, (![B_26, A_24]: (B_26=A_24 | ~r1_tarski(A_24, B_26) | ~v1_zfmisc_1(B_26) | v1_xboole_0(B_26) | v1_xboole_0(A_24))), inference(cnfTransformation, [status(thm)], [f_91])).
% 2.06/1.31  tff(c_308, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_305, c_32])).
% 2.06/1.31  tff(c_314, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_308])).
% 2.06/1.31  tff(c_315, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_40, c_314])).
% 2.06/1.31  tff(c_335, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_315])).
% 2.06/1.31  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.06/1.31  tff(c_63, plain, (![B_34, A_35]: (~v1_xboole_0(B_34) | B_34=A_35 | ~v1_xboole_0(A_35))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.06/1.31  tff(c_66, plain, (![A_35]: (k1_xboole_0=A_35 | ~v1_xboole_0(A_35))), inference(resolution, [status(thm)], [c_4, c_63])).
% 2.06/1.31  tff(c_338, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_335, c_66])).
% 2.06/1.31  tff(c_344, plain, $false, inference(negUnitSimplification, [status(thm)], [c_155, c_338])).
% 2.06/1.31  tff(c_345, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_315])).
% 2.06/1.31  tff(c_36, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_103])).
% 2.06/1.31  tff(c_235, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_233, c_36])).
% 2.06/1.31  tff(c_350, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_345, c_235])).
% 2.06/1.31  tff(c_353, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_350])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 70
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 1
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 4
% 2.06/1.31  #Demod        : 18
% 2.06/1.31  #Tautology    : 36
% 2.06/1.31  #SimpNegUnit  : 5
% 2.06/1.31  #BackRed      : 6
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.31  Preprocessing        : 0.31
% 2.06/1.31  Parsing              : 0.17
% 2.06/1.31  CNF conversion       : 0.02
% 2.06/1.31  Main loop            : 0.20
% 2.06/1.31  Inferencing          : 0.07
% 2.06/1.31  Reduction            : 0.06
% 2.06/1.31  Demodulation         : 0.04
% 2.06/1.31  BG Simplification    : 0.01
% 2.06/1.31  Subsumption          : 0.03
% 2.06/1.31  Abstraction          : 0.01
% 2.06/1.31  MUC search           : 0.00
% 2.06/1.31  Cooper               : 0.00
% 2.06/1.31  Total                : 0.54
% 2.06/1.31  Index Insertion      : 0.00
% 2.06/1.31  Index Deletion       : 0.00
% 2.06/1.31  Index Matching       : 0.00
% 2.06/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
