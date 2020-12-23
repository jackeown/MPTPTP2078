%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:28:41 EST 2020

% Result     : Theorem 2.18s
% Output     : CNFRefutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :   65 (  84 expanded)
%              Number of leaves         :   32 (  42 expanded)
%              Depth                    :   11
%              Number of atoms          :   79 ( 127 expanded)
%              Number of equality atoms :   24 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_36,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_28,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_46,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_101,negated_conjecture,(
    ~ ! [A] :
        ( ~ v1_xboole_0(A)
       => ! [B] :
            ( m1_subset_1(B,A)
           => ~ ( v1_subset_1(k6_domain_1(A,B),A)
                & v1_zfmisc_1(A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_tex_2)).

tff(f_75,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => k6_domain_1(A,B) = k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ( ~ v1_xboole_0(A)
        & m1_subset_1(B,A) )
     => m1_subset_1(k6_domain_1(A,B),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_domain_1)).

tff(f_89,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_zfmisc_1(A) )
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => ( ~ v1_xboole_0(B)
           => ~ v1_subset_1(B,A) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_tex_2)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] :
      ~ ( v1_xboole_0(A)
        & A != B
        & v1_xboole_0(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_boole)).

tff(c_10,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_8,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_37,B_38] :
      ( k3_xboole_0(A_37,B_38) = A_37
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_80,plain,(
    ! [A_5] : k3_xboole_0(k1_xboole_0,A_5) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_8,c_76])).

tff(c_97,plain,(
    ! [A_42,B_43] : k5_xboole_0(A_42,k3_xboole_0(A_42,B_43)) = k4_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_106,plain,(
    ! [A_5] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_97])).

tff(c_110,plain,(
    ! [A_44] : k4_xboole_0(k1_xboole_0,A_44) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_106])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_115,plain,(
    ! [A_44] : k5_xboole_0(A_44,k1_xboole_0) = k2_xboole_0(A_44,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_14])).

tff(c_121,plain,(
    ! [A_45] : k2_xboole_0(A_45,k1_xboole_0) = A_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_115])).

tff(c_20,plain,(
    ! [A_14,B_15] : k2_xboole_0(k1_tarski(A_14),B_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    ! [A_14] : k1_tarski(A_14) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_121,c_20])).

tff(c_36,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_30,plain,(
    v1_zfmisc_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_34,plain,(
    m1_subset_1('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_136,plain,(
    ! [A_49,B_50] :
      ( k6_domain_1(A_49,B_50) = k1_tarski(B_50)
      | ~ m1_subset_1(B_50,A_49)
      | v1_xboole_0(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_139,plain,
    ( k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_136])).

tff(c_142,plain,(
    k6_domain_1('#skF_1','#skF_2') = k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_139])).

tff(c_32,plain,(
    v1_subset_1(k6_domain_1('#skF_1','#skF_2'),'#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_143,plain,(
    v1_subset_1(k1_tarski('#skF_2'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_142,c_32])).

tff(c_148,plain,(
    ! [A_51,B_52] :
      ( m1_subset_1(k6_domain_1(A_51,B_52),k1_zfmisc_1(A_51))
      | ~ m1_subset_1(B_52,A_51)
      | v1_xboole_0(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_157,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | ~ m1_subset_1('#skF_2','#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_142,c_148])).

tff(c_161,plain,
    ( m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_157])).

tff(c_162,plain,(
    m1_subset_1(k1_tarski('#skF_2'),k1_zfmisc_1('#skF_1')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_161])).

tff(c_173,plain,(
    ! [B_53,A_54] :
      ( ~ v1_subset_1(B_53,A_54)
      | v1_xboole_0(B_53)
      | ~ m1_subset_1(B_53,k1_zfmisc_1(A_54))
      | ~ v1_zfmisc_1(A_54)
      | v1_xboole_0(A_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_176,plain,
    ( ~ v1_subset_1(k1_tarski('#skF_2'),'#skF_1')
    | v1_xboole_0(k1_tarski('#skF_2'))
    | ~ v1_zfmisc_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_162,c_173])).

tff(c_182,plain,
    ( v1_xboole_0(k1_tarski('#skF_2'))
    | v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_143,c_176])).

tff(c_183,plain,(
    v1_xboole_0(k1_tarski('#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_182])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_57,plain,(
    ! [B_32,A_33] :
      ( ~ v1_xboole_0(B_32)
      | B_32 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    ! [A_33] :
      ( k1_xboole_0 = A_33
      | ~ v1_xboole_0(A_33) ) ),
    inference(resolution,[status(thm)],[c_2,c_57])).

tff(c_187,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_183,c_60])).

tff(c_193,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_187])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.18/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.21  
% 2.18/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.21  %$ v1_subset_1 > r1_tarski > m1_subset_1 > v1_zfmisc_1 > v1_xboole_0 > k1_enumset1 > k6_domain_1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_zfmisc_1 > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.18/1.21  
% 2.18/1.21  %Foreground sorts:
% 2.18/1.21  
% 2.18/1.21  
% 2.18/1.21  %Background operators:
% 2.18/1.21  
% 2.18/1.21  
% 2.18/1.21  %Foreground operators:
% 2.18/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.18/1.21  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 2.18/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.18/1.21  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.18/1.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.18/1.21  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.18/1.21  tff(k6_domain_1, type, k6_domain_1: ($i * $i) > $i).
% 2.18/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.18/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.18/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.18/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.18/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.18/1.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.18/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.18/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.18/1.21  tff(v1_zfmisc_1, type, v1_zfmisc_1: $i > $o).
% 2.18/1.21  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.18/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.18/1.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.18/1.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.18/1.21  
% 2.18/1.23  tff(f_36, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 2.18/1.23  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.18/1.23  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.18/1.23  tff(f_28, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.18/1.23  tff(f_46, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.18/1.23  tff(f_53, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.18/1.23  tff(f_101, negated_conjecture, ~(![A]: (~v1_xboole_0(A) => (![B]: (m1_subset_1(B, A) => ~(v1_subset_1(k6_domain_1(A, B), A) & v1_zfmisc_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_tex_2)).
% 2.18/1.23  tff(f_75, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => (k6_domain_1(A, B) = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_domain_1)).
% 2.18/1.23  tff(f_68, axiom, (![A, B]: ((~v1_xboole_0(A) & m1_subset_1(B, A)) => m1_subset_1(k6_domain_1(A, B), k1_zfmisc_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_domain_1)).
% 2.18/1.23  tff(f_89, axiom, (![A]: ((~v1_xboole_0(A) & v1_zfmisc_1(A)) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => (~v1_xboole_0(B) => ~v1_subset_1(B, A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_tex_2)).
% 2.18/1.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.18/1.23  tff(f_44, axiom, (![A, B]: ~((v1_xboole_0(A) & ~(A = B)) & v1_xboole_0(B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_boole)).
% 2.18/1.23  tff(c_10, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.18/1.23  tff(c_8, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.18/1.23  tff(c_76, plain, (![A_37, B_38]: (k3_xboole_0(A_37, B_38)=A_37 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.18/1.23  tff(c_80, plain, (![A_5]: (k3_xboole_0(k1_xboole_0, A_5)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_76])).
% 2.18/1.23  tff(c_97, plain, (![A_42, B_43]: (k5_xboole_0(A_42, k3_xboole_0(A_42, B_43))=k4_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_28])).
% 2.18/1.23  tff(c_106, plain, (![A_5]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, A_5))), inference(superposition, [status(thm), theory('equality')], [c_80, c_97])).
% 2.18/1.23  tff(c_110, plain, (![A_44]: (k4_xboole_0(k1_xboole_0, A_44)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_106])).
% 2.18/1.23  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.18/1.23  tff(c_115, plain, (![A_44]: (k5_xboole_0(A_44, k1_xboole_0)=k2_xboole_0(A_44, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_110, c_14])).
% 2.18/1.23  tff(c_121, plain, (![A_45]: (k2_xboole_0(A_45, k1_xboole_0)=A_45)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_115])).
% 2.18/1.23  tff(c_20, plain, (![A_14, B_15]: (k2_xboole_0(k1_tarski(A_14), B_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.18/1.23  tff(c_128, plain, (![A_14]: (k1_tarski(A_14)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_121, c_20])).
% 2.18/1.23  tff(c_36, plain, (~v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.18/1.23  tff(c_30, plain, (v1_zfmisc_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.18/1.23  tff(c_34, plain, (m1_subset_1('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.18/1.23  tff(c_136, plain, (![A_49, B_50]: (k6_domain_1(A_49, B_50)=k1_tarski(B_50) | ~m1_subset_1(B_50, A_49) | v1_xboole_0(A_49))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.18/1.23  tff(c_139, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_34, c_136])).
% 2.18/1.23  tff(c_142, plain, (k6_domain_1('#skF_1', '#skF_2')=k1_tarski('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_36, c_139])).
% 2.18/1.23  tff(c_32, plain, (v1_subset_1(k6_domain_1('#skF_1', '#skF_2'), '#skF_1')), inference(cnfTransformation, [status(thm)], [f_101])).
% 2.18/1.23  tff(c_143, plain, (v1_subset_1(k1_tarski('#skF_2'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_142, c_32])).
% 2.18/1.23  tff(c_148, plain, (![A_51, B_52]: (m1_subset_1(k6_domain_1(A_51, B_52), k1_zfmisc_1(A_51)) | ~m1_subset_1(B_52, A_51) | v1_xboole_0(A_51))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.18/1.23  tff(c_157, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | ~m1_subset_1('#skF_2', '#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_142, c_148])).
% 2.18/1.23  tff(c_161, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_157])).
% 2.18/1.23  tff(c_162, plain, (m1_subset_1(k1_tarski('#skF_2'), k1_zfmisc_1('#skF_1'))), inference(negUnitSimplification, [status(thm)], [c_36, c_161])).
% 2.18/1.23  tff(c_173, plain, (![B_53, A_54]: (~v1_subset_1(B_53, A_54) | v1_xboole_0(B_53) | ~m1_subset_1(B_53, k1_zfmisc_1(A_54)) | ~v1_zfmisc_1(A_54) | v1_xboole_0(A_54))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.18/1.23  tff(c_176, plain, (~v1_subset_1(k1_tarski('#skF_2'), '#skF_1') | v1_xboole_0(k1_tarski('#skF_2')) | ~v1_zfmisc_1('#skF_1') | v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_162, c_173])).
% 2.18/1.23  tff(c_182, plain, (v1_xboole_0(k1_tarski('#skF_2')) | v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_143, c_176])).
% 2.18/1.23  tff(c_183, plain, (v1_xboole_0(k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_36, c_182])).
% 2.18/1.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.18/1.23  tff(c_57, plain, (![B_32, A_33]: (~v1_xboole_0(B_32) | B_32=A_33 | ~v1_xboole_0(A_33))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.18/1.23  tff(c_60, plain, (![A_33]: (k1_xboole_0=A_33 | ~v1_xboole_0(A_33))), inference(resolution, [status(thm)], [c_2, c_57])).
% 2.18/1.23  tff(c_187, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_183, c_60])).
% 2.18/1.23  tff(c_193, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_187])).
% 2.18/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.18/1.23  
% 2.18/1.23  Inference rules
% 2.18/1.23  ----------------------
% 2.18/1.23  #Ref     : 0
% 2.18/1.23  #Sup     : 34
% 2.18/1.23  #Fact    : 0
% 2.18/1.23  #Define  : 0
% 2.18/1.23  #Split   : 0
% 2.18/1.23  #Chain   : 0
% 2.18/1.23  #Close   : 0
% 2.18/1.23  
% 2.18/1.23  Ordering : KBO
% 2.18/1.23  
% 2.18/1.23  Simplification rules
% 2.18/1.23  ----------------------
% 2.18/1.23  #Subsume      : 1
% 2.18/1.23  #Demod        : 7
% 2.18/1.23  #Tautology    : 20
% 2.18/1.23  #SimpNegUnit  : 4
% 2.18/1.23  #BackRed      : 1
% 2.18/1.23  
% 2.18/1.23  #Partial instantiations: 0
% 2.18/1.23  #Strategies tried      : 1
% 2.18/1.23  
% 2.18/1.23  Timing (in seconds)
% 2.18/1.23  ----------------------
% 2.18/1.23  Preprocessing        : 0.31
% 2.18/1.23  Parsing              : 0.17
% 2.18/1.23  CNF conversion       : 0.02
% 2.18/1.23  Main loop            : 0.15
% 2.18/1.23  Inferencing          : 0.06
% 2.18/1.23  Reduction            : 0.05
% 2.18/1.23  Demodulation         : 0.03
% 2.18/1.23  BG Simplification    : 0.01
% 2.18/1.23  Subsumption          : 0.02
% 2.18/1.23  Abstraction          : 0.01
% 2.18/1.23  MUC search           : 0.00
% 2.18/1.23  Cooper               : 0.00
% 2.18/1.23  Total                : 0.50
% 2.18/1.23  Index Insertion      : 0.00
% 2.18/1.23  Index Deletion       : 0.00
% 2.18/1.23  Index Matching       : 0.00
% 2.18/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------
