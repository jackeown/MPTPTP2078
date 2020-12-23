%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:22 EST 2020

% Result     : Theorem 13.24s
% Output     : CNFRefutation 13.24s
% Verified   : 
% Statistics : Number of formulae       :   51 (  65 expanded)
%              Number of leaves         :   25 (  34 expanded)
%              Depth                    :   12
%              Number of atoms          :   83 ( 125 expanded)
%              Number of equality atoms :   23 (  31 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_28,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_71,negated_conjecture,(
    ~ ! [A] :
        ( ( ~ v1_xboole_0(A)
          & v1_zfmisc_1(A) )
       => ! [B] :
            ( ~ v1_xboole_0(k3_xboole_0(A,B))
           => r1_tarski(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tex_2)).

tff(f_59,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ( v1_zfmisc_1(A)
      <=> ? [B] :
            ( m1_subset_1(B,A)
            & A = k6_domain_1(A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tex_2)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_30,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(c_4,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_34,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_32,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_24,plain,(
    ! [A_16] :
      ( k6_domain_1(A_16,'#skF_1'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_16] :
      ( m1_subset_1('#skF_1'(A_16),A_16)
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_146,plain,(
    ! [A_40,B_41] :
      ( k6_domain_1(A_40,B_41) = k1_tarski(B_41)
      | ~ m1_subset_1(B_41,A_40)
      | v1_xboole_0(A_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    ! [A_44] :
      ( k6_domain_1(A_44,'#skF_1'(A_44)) = k1_tarski('#skF_1'(A_44))
      | ~ v1_zfmisc_1(A_44)
      | v1_xboole_0(A_44) ) ),
    inference(resolution,[status(thm)],[c_26,c_146])).

tff(c_168,plain,(
    ! [A_16] :
      ( k1_tarski('#skF_1'(A_16)) = A_16
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16)
      | ~ v1_zfmisc_1(A_16)
      | v1_xboole_0(A_16) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_156])).

tff(c_39,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_54,plain,(
    ! [B_25,A_26] : r1_tarski(k3_xboole_0(B_25,A_26),A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_39,c_6])).

tff(c_870,plain,(
    ! [A_68] :
      ( k1_tarski('#skF_1'(A_68)) = A_68
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68)
      | ~ v1_zfmisc_1(A_68)
      | v1_xboole_0(A_68) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_156])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_1150,plain,(
    ! [A_79,A_80] :
      ( k1_tarski('#skF_1'(A_79)) = A_80
      | k1_xboole_0 = A_80
      | ~ r1_tarski(A_80,A_79)
      | ~ v1_zfmisc_1(A_79)
      | v1_xboole_0(A_79)
      | ~ v1_zfmisc_1(A_79)
      | v1_xboole_0(A_79) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_12])).

tff(c_1209,plain,(
    ! [B_81,A_82] :
      ( k3_xboole_0(B_81,A_82) = k1_tarski('#skF_1'(A_82))
      | k3_xboole_0(B_81,A_82) = k1_xboole_0
      | ~ v1_zfmisc_1(A_82)
      | v1_xboole_0(A_82) ) ),
    inference(resolution,[status(thm)],[c_54,c_1150])).

tff(c_1796,plain,(
    ! [A_89,B_90] :
      ( r1_tarski(k1_tarski('#skF_1'(A_89)),B_90)
      | k3_xboole_0(B_90,A_89) = k1_xboole_0
      | ~ v1_zfmisc_1(A_89)
      | v1_xboole_0(A_89) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1209,c_6])).

tff(c_29598,plain,(
    ! [A_309,B_310] :
      ( r1_tarski(A_309,B_310)
      | k3_xboole_0(B_310,A_309) = k1_xboole_0
      | ~ v1_zfmisc_1(A_309)
      | v1_xboole_0(A_309)
      | ~ v1_zfmisc_1(A_309)
      | v1_xboole_0(A_309)
      | ~ v1_zfmisc_1(A_309)
      | v1_xboole_0(A_309) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_168,c_1796])).

tff(c_28,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_29626,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_29598,c_28])).

tff(c_29636,plain,
    ( k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_29626])).

tff(c_29637,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_29636])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_30,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_35,plain,(
    ~ v1_xboole_0(k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_30])).

tff(c_29638,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29637,c_35])).

tff(c_29641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_29638])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 10:35:41 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.24/6.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.24/6.12  
% 13.24/6.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.24/6.13  %$ r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k6_domain_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_setfam_1 > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 13.24/6.13  
% 13.24/6.13  %Foreground sorts:
% 13.24/6.13  
% 13.24/6.13  
% 13.24/6.13  %Background operators:
% 13.24/6.13  
% 13.24/6.13  
% 13.24/6.13  %Foreground operators:
% 13.24/6.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.24/6.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.24/6.13  tff('#skF_1', type, '#skF_1': $i > $i).
% 13.24/6.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.24/6.13  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 13.24/6.13  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 13.24/6.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.24/6.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.24/6.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.24/6.13  tff('#skF_2', type, '#skF_2': $i).
% 13.24/6.13  tff('#skF_3', type, '#skF_3': $i).
% 13.24/6.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.24/6.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.24/6.13  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 13.24/6.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.24/6.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 13.24/6.13  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 13.24/6.13  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 13.24/6.13  
% 13.24/6.14  tff(f_28, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 13.24/6.14  tff(f_71, negated_conjecture, ~(![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (~v1_xboole_0(k3_xboole_0(A, B)) => r1_tarski(A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_tex_2)).
% 13.24/6.14  tff(f_59, axiom, (![A]: (~v1_xboole_0(A) => (v1_zfmisc_1(A) <=> (?[B]: (m1_subset_1(B, A) & (A = k6_domain_1(A, B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tex_2)).
% 13.24/6.14  tff(f_49, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 13.24/6.14  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 13.24/6.14  tff(f_30, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 13.24/6.14  tff(f_40, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 13.24/6.14  tff(c_4, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_28])).
% 13.24/6.14  tff(c_34, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.24/6.14  tff(c_32, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.24/6.14  tff(c_24, plain, (![A_16]: (k6_domain_1(A_16, '#skF_1'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.24/6.14  tff(c_26, plain, (![A_16]: (m1_subset_1('#skF_1'(A_16), A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(cnfTransformation, [status(thm)], [f_59])).
% 13.24/6.14  tff(c_146, plain, (![A_40, B_41]: (k6_domain_1(A_40, B_41)=k1_tarski(B_41) | ~m1_subset_1(B_41, A_40) | v1_xboole_0(A_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.24/6.14  tff(c_156, plain, (![A_44]: (k6_domain_1(A_44, '#skF_1'(A_44))=k1_tarski('#skF_1'(A_44)) | ~v1_zfmisc_1(A_44) | v1_xboole_0(A_44))), inference(resolution, [status(thm)], [c_26, c_146])).
% 13.24/6.14  tff(c_168, plain, (![A_16]: (k1_tarski('#skF_1'(A_16))=A_16 | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16) | ~v1_zfmisc_1(A_16) | v1_xboole_0(A_16))), inference(superposition, [status(thm), theory('equality')], [c_24, c_156])).
% 13.24/6.14  tff(c_39, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.24/6.14  tff(c_6, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_30])).
% 13.24/6.14  tff(c_54, plain, (![B_25, A_26]: (r1_tarski(k3_xboole_0(B_25, A_26), A_26))), inference(superposition, [status(thm), theory('equality')], [c_39, c_6])).
% 13.24/6.14  tff(c_870, plain, (![A_68]: (k1_tarski('#skF_1'(A_68))=A_68 | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68) | ~v1_zfmisc_1(A_68) | v1_xboole_0(A_68))), inference(superposition, [status(thm), theory('equality')], [c_24, c_156])).
% 13.24/6.14  tff(c_12, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 13.24/6.14  tff(c_1150, plain, (![A_79, A_80]: (k1_tarski('#skF_1'(A_79))=A_80 | k1_xboole_0=A_80 | ~r1_tarski(A_80, A_79) | ~v1_zfmisc_1(A_79) | v1_xboole_0(A_79) | ~v1_zfmisc_1(A_79) | v1_xboole_0(A_79))), inference(superposition, [status(thm), theory('equality')], [c_870, c_12])).
% 13.24/6.14  tff(c_1209, plain, (![B_81, A_82]: (k3_xboole_0(B_81, A_82)=k1_tarski('#skF_1'(A_82)) | k3_xboole_0(B_81, A_82)=k1_xboole_0 | ~v1_zfmisc_1(A_82) | v1_xboole_0(A_82))), inference(resolution, [status(thm)], [c_54, c_1150])).
% 13.24/6.14  tff(c_1796, plain, (![A_89, B_90]: (r1_tarski(k1_tarski('#skF_1'(A_89)), B_90) | k3_xboole_0(B_90, A_89)=k1_xboole_0 | ~v1_zfmisc_1(A_89) | v1_xboole_0(A_89))), inference(superposition, [status(thm), theory('equality')], [c_1209, c_6])).
% 13.24/6.14  tff(c_29598, plain, (![A_309, B_310]: (r1_tarski(A_309, B_310) | k3_xboole_0(B_310, A_309)=k1_xboole_0 | ~v1_zfmisc_1(A_309) | v1_xboole_0(A_309) | ~v1_zfmisc_1(A_309) | v1_xboole_0(A_309) | ~v1_zfmisc_1(A_309) | v1_xboole_0(A_309))), inference(superposition, [status(thm), theory('equality')], [c_168, c_1796])).
% 13.24/6.14  tff(c_28, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.24/6.14  tff(c_29626, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_29598, c_28])).
% 13.24/6.14  tff(c_29636, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0 | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_29626])).
% 13.24/6.14  tff(c_29637, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_29636])).
% 13.24/6.14  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.24/6.14  tff(c_30, plain, (~v1_xboole_0(k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_71])).
% 13.24/6.14  tff(c_35, plain, (~v1_xboole_0(k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_30])).
% 13.24/6.14  tff(c_29638, plain, (~v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_29637, c_35])).
% 13.24/6.14  tff(c_29641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_29638])).
% 13.24/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.24/6.14  
% 13.24/6.14  Inference rules
% 13.24/6.14  ----------------------
% 13.24/6.14  #Ref     : 0
% 13.24/6.14  #Sup     : 7880
% 13.24/6.14  #Fact    : 12
% 13.24/6.14  #Define  : 0
% 13.24/6.14  #Split   : 3
% 13.24/6.14  #Chain   : 0
% 13.24/6.14  #Close   : 0
% 13.24/6.14  
% 13.24/6.14  Ordering : KBO
% 13.24/6.14  
% 13.24/6.14  Simplification rules
% 13.24/6.14  ----------------------
% 13.24/6.14  #Subsume      : 3996
% 13.24/6.14  #Demod        : 1541
% 13.24/6.14  #Tautology    : 2140
% 13.24/6.14  #SimpNegUnit  : 1415
% 13.24/6.14  #BackRed      : 1
% 13.24/6.14  
% 13.24/6.14  #Partial instantiations: 0
% 13.24/6.14  #Strategies tried      : 1
% 13.24/6.14  
% 13.24/6.14  Timing (in seconds)
% 13.24/6.14  ----------------------
% 13.24/6.14  Preprocessing        : 0.29
% 13.24/6.14  Parsing              : 0.15
% 13.24/6.14  CNF conversion       : 0.02
% 13.24/6.14  Main loop            : 5.08
% 13.24/6.14  Inferencing          : 0.81
% 13.24/6.14  Reduction            : 1.24
% 13.24/6.14  Demodulation         : 0.86
% 13.24/6.14  BG Simplification    : 0.12
% 13.24/6.14  Subsumption          : 2.72
% 13.24/6.14  Abstraction          : 0.18
% 13.24/6.14  MUC search           : 0.00
% 13.24/6.14  Cooper               : 0.00
% 13.24/6.14  Total                : 5.39
% 13.24/6.14  Index Insertion      : 0.00
% 13.24/6.14  Index Deletion       : 0.00
% 13.24/6.14  Index Matching       : 0.00
% 13.24/6.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------
