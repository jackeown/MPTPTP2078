%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:48 EST 2020

% Result     : Theorem 2.08s
% Output     : CNFRefutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :   63 ( 109 expanded)
%              Number of leaves         :   30 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   80 ( 201 expanded)
%              Number of equality atoms :   21 (  34 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

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

tff(f_47,axiom,(
    ! [A] : k2_subset_1(A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

tff(f_50,axiom,(
    ! [A] : ~ v1_subset_1(k2_subset_1(A),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc14_subset_1)).

tff(f_28,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_45,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_93,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_81,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

tff(c_16,plain,(
    ! [A_11] : k2_subset_1(A_11) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_18,plain,(
    ! [A_12] : ~ v1_subset_1(k2_subset_1(A_12),A_12) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,(
    ! [A_12] : ~ v1_subset_1(A_12,A_12) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_18])).

tff(c_4,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_57,plain,(
    ! [A_26,B_27] : k2_xboole_0(k1_tarski(A_26),B_27) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_61,plain,(
    ! [A_26] : k1_tarski(A_26) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_57])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_34,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_131,plain,(
    ! [A_43,B_44] :
      ( k6_domain_1(A_43,B_44) = k1_tarski(B_44)
      | ~ m1_subset_1(B_44,A_43)
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_137,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_141,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_137])).

tff(c_147,plain,(
    ! [A_45,B_46] :
      ( m1_subset_1(k6_domain_1(A_45,B_46),k1_zfmisc_1(A_45))
      | ~ m1_subset_1(B_46,A_45)
      | v1_xboole_0(A_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_156,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_141,c_147])).

tff(c_160,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_156])).

tff(c_161,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_160])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( r1_tarski(A_13,B_14)
      | ~ m1_subset_1(A_13,k1_zfmisc_1(B_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_169,plain,(
    r1_tarski(k1_tarski('#skF_2'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_161,c_20])).

tff(c_170,plain,(
    ! [B_47,A_48] :
      ( B_47 = A_48
      | ~ r1_tarski(A_48,B_47)
      | ~ v1_zfmisc_1(B_47)
      | v1_xboole_0(B_47)
      | v1_xboole_0(A_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_173,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(resolution,[status(thm)],[c_169,c_170])).

tff(c_176,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0('#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_173])).

tff(c_177,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_176])).

tff(c_178,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_177])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_72,plain,(
    ! [B_30,A_31] :
      ( ~ v1_xboole_0(B_30)
      | B_30 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,(
    ! [A_31] :
      ( k1_xboole_0 = A_31
      | ~ v1_xboole_0(A_31) ) ),
    inference(resolution,[status(thm)],[c_2,c_72])).

tff(c_181,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_178,c_75])).

tff(c_187,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_181])).

tff(c_188,plain,(
    k1_tarski('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_177])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_142,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_32])).

tff(c_192,plain,(
    v1_subset_1('#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_142])).

tff(c_195,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_192])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 15:15:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.08/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.25  
% 2.08/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.26  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k2_subset_1 > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.08/1.26  
% 2.08/1.26  %Foreground sorts:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Background operators:
% 2.08/1.26  
% 2.08/1.26  
% 2.08/1.26  %Foreground operators:
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.08/1.26  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.08/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.08/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.08/1.26  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.08/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.08/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.08/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.08/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.08/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.08/1.26  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.08/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.08/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.08/1.26  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.08/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.08/1.26  tff(k2_subset_1, type, k2_subset_1: $i > $i).
% 2.08/1.26  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.08/1.26  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.08/1.26  
% 2.08/1.27  tff(f_47, axiom, (![A]: (k2_subset_1(A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_subset_1)).
% 2.08/1.27  tff(f_50, axiom, (![A]: ~v1_subset_1(k2_subset_1(A), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc14_subset_1)).
% 2.08/1.27  tff(f_28, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.08/1.27  tff(f_45, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.08/1.27  tff(f_93, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_tex_2)).
% 2.08/1.27  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.08/1.27  tff(f_61, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.08/1.27  tff(f_54, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.08/1.27  tff(f_81, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_tex_2)).
% 2.08/1.27  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.08/1.27  tff(f_36, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_boole)).
% 2.08/1.27  tff(c_16, plain, (![A_11]: (k2_subset_1(A_11)=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.08/1.27  tff(c_18, plain, (![A_12]: (~v1_subset_1(k2_subset_1(A_12), A_12))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.08/1.27  tff(c_37, plain, (![A_12]: (~v1_subset_1(A_12, A_12))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_18])).
% 2.08/1.27  tff(c_4, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.08/1.27  tff(c_57, plain, (![A_26, B_27]: (k2_xboole_0(k1_tarski(A_26), B_27)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.08/1.27  tff(c_61, plain, (![A_26]: (k1_tarski(A_26)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_57])).
% 2.08/1.27  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.27  tff(c_30, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.27  tff(c_34, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.27  tff(c_131, plain, (![A_43, B_44]: (k6_domain_1(A_43, B_44)=k1_tarski(B_44) | ~m1_subset_1(B_44, A_43) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.08/1.27  tff(c_137, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_131])).
% 2.08/1.27  tff(c_141, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_137])).
% 2.08/1.27  tff(c_147, plain, (![A_45, B_46]: (m1_subset_1(k6_domain_1(A_45, B_46), k1_zfmisc_1(A_45)) | ~m1_subset_1(B_46, A_45) | v1_xboole_0(A_45))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.08/1.27  tff(c_156, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_141, c_147])).
% 2.08/1.27  tff(c_160, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_156])).
% 2.08/1.27  tff(c_161, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_36, c_160])).
% 2.08/1.27  tff(c_20, plain, (![A_13, B_14]: (r1_tarski(A_13, B_14) | ~m1_subset_1(A_13, k1_zfmisc_1(B_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.08/1.27  tff(c_169, plain, (r1_tarski(k1_tarski('#skF_2'), '#skF_1')), inference(resolution, [status(thm)], [c_161, c_20])).
% 2.08/1.27  tff(c_170, plain, (![B_47, A_48]: (B_47=A_48 | ~r1_tarski(A_48, B_47) | ~v1_zfmisc_1(B_47) | v1_xboole_0(B_47) | v1_xboole_0(A_48))), inference(cnfTransformation, [status(thm)], [f_81])).
% 2.08/1.27  tff(c_173, plain, (k1_tarski('#skF_2')='#skF_1' | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(resolution, [status(thm)], [c_169, c_170])).
% 2.08/1.27  tff(c_176, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0('#skF_1') | v1_xboole_0(k1_tarski('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_30, c_173])).
% 2.08/1.27  tff(c_177, plain, (k1_tarski('#skF_2')='#skF_1' | v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_176])).
% 2.08/1.27  tff(c_178, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(splitLeft, [status(thm)], [c_177])).
% 2.08/1.27  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.08/1.27  tff(c_72, plain, (![B_30, A_31]: (~v1_xboole_0(B_30) | B_30=A_31 | ~v1_xboole_0(A_31))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.08/1.27  tff(c_75, plain, (![A_31]: (k1_xboole_0=A_31 | ~v1_xboole_0(A_31))), inference(resolution, [status(thm)], [c_2, c_72])).
% 2.08/1.27  tff(c_181, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_178, c_75])).
% 2.08/1.27  tff(c_187, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_181])).
% 2.08/1.27  tff(c_188, plain, (k1_tarski('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_177])).
% 2.08/1.27  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_93])).
% 2.08/1.27  tff(c_142, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_141, c_32])).
% 2.08/1.27  tff(c_192, plain, (v1_subset_1('#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_188, c_142])).
% 2.08/1.27  tff(c_195, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_192])).
% 2.08/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.08/1.27  
% 2.08/1.27  Inference rules
% 2.08/1.27  ----------------------
% 2.08/1.27  #Ref     : 0
% 2.08/1.27  #Sup     : 32
% 2.08/1.27  #Fact    : 0
% 2.08/1.27  #Define  : 0
% 2.08/1.27  #Split   : 1
% 2.08/1.27  #Chain   : 0
% 2.08/1.27  #Close   : 0
% 2.08/1.27  
% 2.08/1.27  Ordering : KBO
% 2.08/1.27  
% 2.08/1.27  Simplification rules
% 2.08/1.27  ----------------------
% 2.08/1.27  #Subsume      : 0
% 2.08/1.27  #Demod        : 8
% 2.08/1.27  #Tautology    : 18
% 2.08/1.27  #SimpNegUnit  : 5
% 2.08/1.27  #BackRed      : 5
% 2.08/1.27  
% 2.08/1.27  #Partial instantiations: 0
% 2.08/1.27  #Strategies tried      : 1
% 2.08/1.27  
% 2.08/1.27  Timing (in seconds)
% 2.08/1.27  ----------------------
% 2.08/1.27  Preprocessing        : 0.32
% 2.08/1.27  Parsing              : 0.18
% 2.08/1.27  CNF conversion       : 0.02
% 2.08/1.27  Main loop            : 0.15
% 2.08/1.27  Inferencing          : 0.06
% 2.08/1.27  Reduction            : 0.05
% 2.08/1.27  Demodulation         : 0.03
% 2.08/1.27  BG Simplification    : 0.01
% 2.08/1.27  Subsumption          : 0.02
% 2.08/1.27  Abstraction          : 0.01
% 2.08/1.27  MUC search           : 0.00
% 2.08/1.27  Cooper               : 0.00
% 2.08/1.27  Total                : 0.50
% 2.08/1.27  Index Insertion      : 0.00
% 2.08/1.27  Index Deletion       : 0.00
% 2.08/1.27  Index Matching       : 0.00
% 2.08/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------
