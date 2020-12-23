%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:45 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.54s
% Verified   : 
% Statistics : Number of formulae       :   70 ( 150 expanded)
%              Number of leaves         :   33 (  64 expanded)
%              Depth                    :   17
%              Number of atoms          :   82 ( 267 expanded)
%              Number of equality atoms :   22 (  48 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k2_subset_1,type,(
    k2_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_52,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_55,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_50,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_73,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_84,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( ~ v1_xboole_0(k3_xboole_0(A,B))
         => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_22,plain,(
    ! [A_19] : k2_subset_1(A_19) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_24,plain,(
    ! [A_20] : ~ v1_subset_1(k2_subset_1(A_20),A_20) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_43,plain,(
    ! [A_20] : ~ v1_subset_1(A_20,A_20) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_24])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_73,plain,(
    ! [A_36,B_37] : k2_xboole_0(k1_tarski(A_36),B_37) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_77,plain,(
    ! [A_36] : k1_tarski(A_36) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_73])).

tff(c_42,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_36,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_40,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_205,plain,(
    ! [A_57,B_58] :
      ( k6_domain_1(A_57,B_58) = k1_tarski(B_58)
      | ~ m1_subset_1(B_58,A_57)
      | v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_211,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_40,c_205])).

tff(c_215,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_211])).

tff(c_241,plain,(
    ! [A_62,B_63] :
      ( m1_subset_1(k6_domain_1(A_62,B_63),k1_zfmisc_1(A_62))
      | ~ m1_subset_1(B_63,A_62)
      | v1_xboole_0(A_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_250,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_241])).

tff(c_254,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_250])).

tff(c_255,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_254])).

tff(c_26,plain,(
    ! [A_21,B_22] :
      ( r1_tarski(A_21,B_22)
      | ~ m1_subset_1(A_21,k1_zfmisc_1(B_22)) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_263,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_255,c_26])).

tff(c_12,plain,(
    ! [A_10,B_11] :
      ( k3_xboole_0(A_10,B_11) = A_10
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_267,plain,(
    k3_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_263,c_12])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_280,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_2])).

tff(c_34,plain,(
    ! [A_27,B_29] :
      ( r1_tarski(A_27,B_29)
      | v1_xboole_0(k3_xboole_0(A_27,B_29))
      | ~ v1_zfmisc_1(A_27)
      | v1_xboole_0(A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_297,plain,
    ( r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_280,c_34])).

tff(c_307,plain,
    ( r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_297])).

tff(c_308,plain,
    ( r1_tarski('#skF_1',k1_tarski('#skF_2'))
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_307])).

tff(c_325,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_308])).

tff(c_8,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_328,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_325,c_8])).

tff(c_332,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_77,c_328])).

tff(c_333,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(splitRight,[status(thm)],[c_308])).

tff(c_338,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(resolution,[status(thm)],[c_333,c_12])).

tff(c_339,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_280])).

tff(c_38,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_216,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_38])).

tff(c_363,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_216])).

tff(c_368,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_43,c_363])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:20:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.32  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.19/1.32  
% 2.19/1.32  %Foreground sorts:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Background operators:
% 2.19/1.32  
% 2.19/1.32  
% 2.19/1.32  %Foreground operators:
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.32  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.19/1.32  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.32  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.32  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.19/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.32  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.19/1.32  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.32  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.19/1.32  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.19/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.19/1.32  
% 2.54/1.33  tff(f_52, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_subset_1)).
% 2.54/1.33  tff(f_55, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.54/1.33  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 2.54/1.33  tff(f_50, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.54/1.33  tff(f_96, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.54/1.33  tff(f_73, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.54/1.33  tff(f_66, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.54/1.33  tff(f_59, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.54/1.33  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.54/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.54/1.33  tff(f_84, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 2.54/1.33  tff(f_35, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.54/1.33  tff(c_22, plain, (![A_19]: (k2_subset_1(A_19)=A_19)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.54/1.33  tff(c_24, plain, (![A_20]: (~v1_subset_1(k2_subset_1(A_20), A_20))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.54/1.33  tff(c_43, plain, (![A_20]: (~v1_subset_1(A_20, A_20))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_24])).
% 2.54/1.33  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.54/1.33  tff(c_73, plain, (![A_36, B_37]: (k2_xboole_0(k1_tarski(A_36), B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.54/1.33  tff(c_77, plain, (![A_36]: (k1_tarski(A_36)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_73])).
% 2.54/1.33  tff(c_42, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.54/1.33  tff(c_36, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.54/1.33  tff(c_40, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.54/1.33  tff(c_205, plain, (![A_57, B_58]: (k6_domain_1(A_57, B_58)=k1_tarski(B_58) | ~m1_subset_1(B_58, A_57) | v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.54/1.33  tff(c_211, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_40, c_205])).
% 2.54/1.33  tff(c_215, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_42, c_211])).
% 2.54/1.33  tff(c_241, plain, (![A_62, B_63]: (m1_subset_1(k6_domain_1(A_62, B_63), k1_zfmisc_1(A_62)) | ~m1_subset_1(B_63, A_62) | v1_xboole_0(A_62))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.54/1.33  tff(c_250, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_215, c_241])).
% 2.54/1.33  tff(c_254, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_250])).
% 2.54/1.33  tff(c_255, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_42, c_254])).
% 2.54/1.33  tff(c_26, plain, (![A_21, B_22]: (r1_tarski(A_21, B_22) | ~m1_subset_1(A_21, k1_zfmisc_1(B_22)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.54/1.33  tff(c_263, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_255, c_26])).
% 2.54/1.33  tff(c_12, plain, (![A_10, B_11]: (k3_xboole_0(A_10, B_11)=A_10 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.54/1.33  tff(c_267, plain, (k3_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(resolution, [status(thm)], [c_263, c_12])).
% 2.54/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.54/1.33  tff(c_280, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_267, c_2])).
% 2.54/1.33  tff(c_34, plain, (![A_27, B_29]: (r1_tarski(A_27, B_29) | v1_xboole_0(k3_xboole_0(A_27, B_29)) | ~v1_zfmisc_1(A_27) | v1_xboole_0(A_27))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.54/1.33  tff(c_297, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2')) | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_280, c_34])).
% 2.54/1.33  tff(c_307, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2')) | v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_297])).
% 2.54/1.33  tff(c_308, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2')) | v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_42, c_307])).
% 2.54/1.33  tff(c_325, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_308])).
% 2.54/1.33  tff(c_8, plain, (![A_7]: (k1_xboole_0=A_7 | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.54/1.33  tff(c_328, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_325, c_8])).
% 2.54/1.33  tff(c_332, plain, $false, inference(negUnitSimplification, [status(thm)], [c_77, c_328])).
% 2.54/1.33  tff(c_333, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(splitRight, [status(thm)], [c_308])).
% 2.54/1.33  tff(c_338, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(resolution, [status(thm)], [c_333, c_12])).
% 2.54/1.33  tff(c_339, plain, (k1_tarski('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_338, c_280])).
% 2.54/1.33  tff(c_38, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 2.54/1.33  tff(c_216, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_38])).
% 2.54/1.33  tff(c_363, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_339, c_216])).
% 2.54/1.33  tff(c_368, plain, $false, inference(negUnitSimplification, [status(thm)], [c_43, c_363])).
% 2.54/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.54/1.33  
% 2.54/1.33  Inference rules
% 2.54/1.33  ----------------------
% 2.54/1.33  #Ref     : 0
% 2.54/1.33  #Sup     : 74
% 2.54/1.33  #Fact    : 0
% 2.54/1.33  #Define  : 0
% 2.54/1.33  #Split   : 1
% 2.54/1.33  #Chain   : 0
% 2.54/1.33  #Close   : 0
% 2.54/1.33  
% 2.54/1.33  Ordering : KBO
% 2.54/1.33  
% 2.54/1.33  Simplification rules
% 2.54/1.33  ----------------------
% 2.54/1.33  #Subsume      : 1
% 2.54/1.33  #Demod        : 31
% 2.54/1.33  #Tautology    : 50
% 2.54/1.33  #SimpNegUnit  : 7
% 2.54/1.33  #BackRed      : 10
% 2.54/1.33  
% 2.54/1.33  #Partial instantiations: 0
% 2.54/1.33  #Strategies tried      : 1
% 2.54/1.33  
% 2.54/1.33  Timing (in seconds)
% 2.54/1.33  ----------------------
% 2.54/1.34  Preprocessing        : 0.33
% 2.54/1.34  Parsing              : 0.18
% 2.54/1.34  CNF conversion       : 0.02
% 2.54/1.34  Main loop            : 0.23
% 2.54/1.34  Inferencing          : 0.08
% 2.54/1.34  Reduction            : 0.08
% 2.54/1.34  Demodulation         : 0.06
% 2.54/1.34  BG Simplification    : 0.02
% 2.54/1.34  Subsumption          : 0.04
% 2.54/1.34  Abstraction          : 0.02
% 2.54/1.34  MUC search           : 0.00
% 2.54/1.34  Cooper               : 0.00
% 2.54/1.34  Total                : 0.60
% 2.54/1.34  Index Insertion      : 0.00
% 2.54/1.34  Index Deletion       : 0.00
% 2.54/1.34  Index Matching       : 0.00
% 2.54/1.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
