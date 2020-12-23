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
% DateTime   : Thu Dec  3 10:28:34 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 125 expanded)
%              Number of leaves         :   27 (  53 expanded)
%              Depth                    :   13
%              Number of atoms          :  100 ( 251 expanded)
%              Number of equality atoms :   22 (  37 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_36,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_72,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_85,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( ( ~ v1_xboole_0(B)
            & v1_zfmisc_1(B) )
         => ( r1_tarski(A,B)
           => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_54,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc3_subset_1)).

tff(f_48,axiom,(
    ! [A] :
      ( ~ v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_subset_1(B,A)
           => ~ v1_xboole_0(B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_subset_1)).

tff(c_4,plain,(
    ! [A_2] : k2_xboole_0(A_2,k1_xboole_0) = A_2 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    ! [A_24,B_25] : k2_xboole_0(k1_tarski(A_24),B_25) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_48,plain,(
    ! [A_24] : k1_tarski(A_24) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_44])).

tff(c_32,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_26,plain,(
    v1_zfmisc_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_30,plain,(
    m1_subset_1('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_71,plain,(
    ! [A_34,B_35] :
      ( k6_domain_1(A_34,B_35) = k1_tarski(B_35)
      | ~ m1_subset_1(B_35,A_34)
      | v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_80,plain,
    ( k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_71])).

tff(c_85,plain,(
    k6_domain_1('#skF_2','#skF_3') = k1_tarski('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_80])).

tff(c_20,plain,(
    ! [A_13,B_14] :
      ( m1_subset_1(k6_domain_1(A_13,B_14),k1_zfmisc_1(A_13))
      | ~ m1_subset_1(B_14,A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_99,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3','#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_20])).

tff(c_103,plain,
    ( m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2'))
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_99])).

tff(c_104,plain,(
    m1_subset_1(k1_tarski('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_103])).

tff(c_16,plain,(
    ! [A_11,B_12] :
      ( r1_tarski(A_11,B_12)
      | ~ m1_subset_1(A_11,k1_zfmisc_1(B_12)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_113,plain,(
    r1_tarski(k1_tarski('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_104,c_16])).

tff(c_121,plain,(
    ! [B_40,A_41] :
      ( B_40 = A_41
      | ~ r1_tarski(A_41,B_40)
      | ~ v1_zfmisc_1(B_40)
      | v1_xboole_0(B_40)
      | v1_xboole_0(A_41) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_127,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | ~ v1_zfmisc_1('#skF_2')
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_113,c_121])).

tff(c_134,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0('#skF_2')
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_127])).

tff(c_135,plain,
    ( k1_tarski('#skF_3') = '#skF_2'
    | v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_134])).

tff(c_137,plain,(
    v1_xboole_0(k1_tarski('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_135])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_140,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_137,c_2])).

tff(c_144,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_140])).

tff(c_145,plain,(
    k1_tarski('#skF_3') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_135])).

tff(c_28,plain,(
    v1_subset_1(k6_domain_1('#skF_2','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_95,plain,(
    v1_subset_1(k1_tarski('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_28])).

tff(c_149,plain,(
    v1_subset_1('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_95])).

tff(c_14,plain,(
    ! [A_9] : m1_subset_1('#skF_1'(A_9),k1_zfmisc_1(A_9)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_61,plain,(
    ! [A_31,B_32] :
      ( r1_tarski(A_31,B_32)
      | ~ m1_subset_1(A_31,k1_zfmisc_1(B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_69,plain,(
    ! [A_9] : r1_tarski('#skF_1'(A_9),A_9) ),
    inference(resolution,[status(thm)],[c_14,c_61])).

tff(c_447,plain,(
    ! [A_56] :
      ( '#skF_1'(A_56) = A_56
      | ~ v1_zfmisc_1(A_56)
      | v1_xboole_0(A_56)
      | v1_xboole_0('#skF_1'(A_56)) ) ),
    inference(resolution,[status(thm)],[c_69,c_121])).

tff(c_12,plain,(
    ! [A_9] : ~ v1_subset_1('#skF_1'(A_9),A_9) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_159,plain,(
    ! [B_42,A_43] :
      ( ~ v1_xboole_0(B_42)
      | v1_subset_1(B_42,A_43)
      | ~ m1_subset_1(B_42,k1_zfmisc_1(A_43))
      | v1_xboole_0(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_168,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0('#skF_1'(A_9))
      | v1_subset_1('#skF_1'(A_9),A_9)
      | v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_14,c_159])).

tff(c_173,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0('#skF_1'(A_9))
      | v1_xboole_0(A_9) ) ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_168])).

tff(c_458,plain,(
    ! [A_57] :
      ( '#skF_1'(A_57) = A_57
      | ~ v1_zfmisc_1(A_57)
      | v1_xboole_0(A_57) ) ),
    inference(resolution,[status(thm)],[c_447,c_173])).

tff(c_461,plain,
    ( '#skF_1'('#skF_2') = '#skF_2'
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_26,c_458])).

tff(c_464,plain,(
    '#skF_1'('#skF_2') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_461])).

tff(c_477,plain,(
    ~ v1_subset_1('#skF_2','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_464,c_12])).

tff(c_485,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_149,c_477])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n012.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 11:06:22 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.29  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k6_domain_1 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 2.28/1.29  
% 2.28/1.29  %Foreground sorts:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Background operators:
% 2.28/1.29  
% 2.28/1.29  
% 2.28/1.29  %Foreground operators:
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.29  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.28/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.28/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.28/1.29  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.28/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.29  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.28/1.29  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.29  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.28/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.28/1.29  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.28/1.29  
% 2.62/1.31  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.62/1.31  tff(f_36, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.62/1.31  tff(f_97, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.62/1.31  tff(f_72, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.62/1.31  tff(f_65, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.62/1.31  tff(f_58, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.62/1.31  tff(f_85, axiom, (![A]: (~v1_xboole_0(A) => (![B]: ((~v1_xboole_0(B) & v1_zfmisc_1(B)) => (r1_tarski(A, B) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_tex_2)).
% 2.62/1.31  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.62/1.31  tff(f_54, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc3_subset_1)).
% 2.62/1.31  tff(f_48, axiom, (![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_subset_1(B, A) => ~v1_xboole_0(B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_subset_1)).
% 2.62/1.31  tff(c_4, plain, (![A_2]: (k2_xboole_0(A_2, k1_xboole_0)=A_2)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.31  tff(c_44, plain, (![A_24, B_25]: (k2_xboole_0(k1_tarski(A_24), B_25)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.62/1.31  tff(c_48, plain, (![A_24]: (k1_tarski(A_24)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_44])).
% 2.62/1.31  tff(c_32, plain, (~v1_xboole_0('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.31  tff(c_26, plain, (v1_zfmisc_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.31  tff(c_30, plain, (m1_subset_1('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.31  tff(c_71, plain, (![A_34, B_35]: (k6_domain_1(A_34, B_35)=k1_tarski(B_35) | ~m1_subset_1(B_35, A_34) | v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.62/1.31  tff(c_80, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_71])).
% 2.62/1.31  tff(c_85, plain, (k6_domain_1('#skF_2', '#skF_3')=k1_tarski('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_32, c_80])).
% 2.62/1.31  tff(c_20, plain, (![A_13, B_14]: (m1_subset_1(k6_domain_1(A_13, B_14), k1_zfmisc_1(A_13)) | ~m1_subset_1(B_14, A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.62/1.31  tff(c_99, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', '#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_85, c_20])).
% 2.62/1.31  tff(c_103, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2')) | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_99])).
% 2.62/1.31  tff(c_104, plain, (m1_subset_1(k1_tarski('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_32, c_103])).
% 2.62/1.31  tff(c_16, plain, (![A_11, B_12]: (r1_tarski(A_11, B_12) | ~m1_subset_1(A_11, k1_zfmisc_1(B_12)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.62/1.31  tff(c_113, plain, (r1_tarski(k1_tarski('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_104, c_16])).
% 2.62/1.31  tff(c_121, plain, (![B_40, A_41]: (B_40=A_41 | ~r1_tarski(A_41, B_40) | ~v1_zfmisc_1(B_40) | v1_xboole_0(B_40) | v1_xboole_0(A_41))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.62/1.31  tff(c_127, plain, (k1_tarski('#skF_3')='#skF_2' | ~v1_zfmisc_1('#skF_2') | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_113, c_121])).
% 2.62/1.31  tff(c_134, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0('#skF_2') | v1_xboole_0(k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_127])).
% 2.62/1.31  tff(c_135, plain, (k1_tarski('#skF_3')='#skF_2' | v1_xboole_0(k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_32, c_134])).
% 2.62/1.31  tff(c_137, plain, (v1_xboole_0(k1_tarski('#skF_3'))), inference(splitLeft, [status(thm)], [c_135])).
% 2.62/1.31  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.62/1.31  tff(c_140, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_137, c_2])).
% 2.62/1.31  tff(c_144, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_140])).
% 2.62/1.31  tff(c_145, plain, (k1_tarski('#skF_3')='#skF_2'), inference(splitRight, [status(thm)], [c_135])).
% 2.62/1.31  tff(c_28, plain, (v1_subset_1(k6_domain_1('#skF_2', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 2.62/1.31  tff(c_95, plain, (v1_subset_1(k1_tarski('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_85, c_28])).
% 2.62/1.31  tff(c_149, plain, (v1_subset_1('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_145, c_95])).
% 2.62/1.31  tff(c_14, plain, (![A_9]: (m1_subset_1('#skF_1'(A_9), k1_zfmisc_1(A_9)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.31  tff(c_61, plain, (![A_31, B_32]: (r1_tarski(A_31, B_32) | ~m1_subset_1(A_31, k1_zfmisc_1(B_32)))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.62/1.31  tff(c_69, plain, (![A_9]: (r1_tarski('#skF_1'(A_9), A_9))), inference(resolution, [status(thm)], [c_14, c_61])).
% 2.62/1.31  tff(c_447, plain, (![A_56]: ('#skF_1'(A_56)=A_56 | ~v1_zfmisc_1(A_56) | v1_xboole_0(A_56) | v1_xboole_0('#skF_1'(A_56)))), inference(resolution, [status(thm)], [c_69, c_121])).
% 2.62/1.31  tff(c_12, plain, (![A_9]: (~v1_subset_1('#skF_1'(A_9), A_9))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.62/1.31  tff(c_159, plain, (![B_42, A_43]: (~v1_xboole_0(B_42) | v1_subset_1(B_42, A_43) | ~m1_subset_1(B_42, k1_zfmisc_1(A_43)) | v1_xboole_0(A_43))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.62/1.31  tff(c_168, plain, (![A_9]: (~v1_xboole_0('#skF_1'(A_9)) | v1_subset_1('#skF_1'(A_9), A_9) | v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_14, c_159])).
% 2.62/1.31  tff(c_173, plain, (![A_9]: (~v1_xboole_0('#skF_1'(A_9)) | v1_xboole_0(A_9))), inference(negUnitSimplification, [status(thm)], [c_12, c_168])).
% 2.62/1.31  tff(c_458, plain, (![A_57]: ('#skF_1'(A_57)=A_57 | ~v1_zfmisc_1(A_57) | v1_xboole_0(A_57))), inference(resolution, [status(thm)], [c_447, c_173])).
% 2.62/1.31  tff(c_461, plain, ('#skF_1'('#skF_2')='#skF_2' | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_26, c_458])).
% 2.62/1.31  tff(c_464, plain, ('#skF_1'('#skF_2')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_32, c_461])).
% 2.62/1.31  tff(c_477, plain, (~v1_subset_1('#skF_2', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_464, c_12])).
% 2.62/1.31  tff(c_485, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_149, c_477])).
% 2.62/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.31  
% 2.62/1.31  Inference rules
% 2.62/1.31  ----------------------
% 2.62/1.31  #Ref     : 0
% 2.62/1.31  #Sup     : 93
% 2.62/1.31  #Fact    : 0
% 2.62/1.31  #Define  : 0
% 2.62/1.31  #Split   : 4
% 2.62/1.31  #Chain   : 0
% 2.62/1.31  #Close   : 0
% 2.62/1.31  
% 2.62/1.31  Ordering : KBO
% 2.62/1.31  
% 2.62/1.31  Simplification rules
% 2.62/1.31  ----------------------
% 2.62/1.31  #Subsume      : 9
% 2.62/1.31  #Demod        : 53
% 2.62/1.31  #Tautology    : 42
% 2.62/1.31  #SimpNegUnit  : 24
% 2.62/1.31  #BackRed      : 9
% 2.62/1.31  
% 2.62/1.31  #Partial instantiations: 0
% 2.62/1.31  #Strategies tried      : 1
% 2.62/1.31  
% 2.62/1.31  Timing (in seconds)
% 2.62/1.31  ----------------------
% 2.62/1.31  Preprocessing        : 0.31
% 2.62/1.31  Parsing              : 0.17
% 2.62/1.31  CNF conversion       : 0.02
% 2.62/1.31  Main loop            : 0.24
% 2.62/1.31  Inferencing          : 0.09
% 2.62/1.31  Reduction            : 0.07
% 2.62/1.31  Demodulation         : 0.05
% 2.62/1.31  BG Simplification    : 0.01
% 2.62/1.31  Subsumption          : 0.03
% 2.62/1.31  Abstraction          : 0.01
% 2.62/1.31  MUC search           : 0.00
% 2.62/1.31  Cooper               : 0.00
% 2.62/1.31  Total                : 0.58
% 2.62/1.31  Index Insertion      : 0.00
% 2.62/1.31  Index Deletion       : 0.00
% 2.62/1.31  Index Matching       : 0.00
% 2.62/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------
