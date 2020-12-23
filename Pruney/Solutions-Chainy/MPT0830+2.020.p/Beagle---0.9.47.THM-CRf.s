%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:28 EST 2020

% Result     : Theorem 2.62s
% Output     : CNFRefutation 2.62s
% Verified   : 
% Statistics : Number of formulae       :   61 (  80 expanded)
%              Number of leaves         :   31 (  40 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 112 expanded)
%              Number of equality atoms :    6 (   6 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k5_relset_1,type,(
    k5_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_88,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v4_relat_1(C,B) )
     => ( v1_relat_1(k7_relat_1(C,A))
        & v4_relat_1(k7_relat_1(C,A),A)
        & v4_relat_1(k7_relat_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc23_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_34,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_45,plain,(
    ! [C_36,A_37,B_38] :
      ( v1_relat_1(C_36)
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_45])).

tff(c_14,plain,(
    ! [B_10,A_9] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_10,A_9)),A_9)
      | ~ v1_relat_1(B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    ! [C_44,A_45,B_46] :
      ( v4_relat_1(C_44,A_45)
      | ~ m1_subset_1(C_44,k1_zfmisc_1(k2_zfmisc_1(A_45,B_46))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_76,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_34,c_67])).

tff(c_149,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(k7_relat_1(C_66,A_67))
      | ~ v4_relat_1(C_66,B_68)
      | ~ v1_relat_1(C_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_153,plain,(
    ! [A_67] :
      ( v1_relat_1(k7_relat_1('#skF_4',A_67))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_76,c_149])).

tff(c_157,plain,(
    ! [A_67] : v1_relat_1(k7_relat_1('#skF_4',A_67)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_153])).

tff(c_16,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_12,A_11)),k2_relat_1(B_12))
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_226,plain,(
    ! [A_94,B_95,C_96] :
      ( k2_relset_1(A_94,B_95,C_96) = k2_relat_1(C_96)
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_94,B_95))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_235,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_34,c_226])).

tff(c_294,plain,(
    ! [A_120,B_121,C_122] :
      ( m1_subset_1(k2_relset_1(A_120,B_121,C_122),k1_zfmisc_1(B_121))
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_120,B_121))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_316,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_235,c_294])).

tff(c_323,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_316])).

tff(c_4,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | ~ m1_subset_1(A_4,k1_zfmisc_1(B_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_327,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_323,c_4])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_334,plain,(
    ! [A_123] :
      ( r1_tarski(A_123,'#skF_3')
      | ~ r1_tarski(A_123,k2_relat_1('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_327,c_2])).

tff(c_338,plain,(
    ! [A_11] :
      ( r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_11)),'#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_334])).

tff(c_345,plain,(
    ! [A_11] : r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_11)),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_338])).

tff(c_461,plain,(
    ! [C_148,A_149,B_150] :
      ( m1_subset_1(C_148,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ r1_tarski(k2_relat_1(C_148),B_150)
      | ~ r1_tarski(k1_relat_1(C_148),A_149)
      | ~ v1_relat_1(C_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_382,plain,(
    ! [A_130,B_131,C_132,D_133] :
      ( k5_relset_1(A_130,B_131,C_132,D_133) = k7_relat_1(C_132,D_133)
      | ~ m1_subset_1(C_132,k1_zfmisc_1(k2_zfmisc_1(A_130,B_131))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_393,plain,(
    ! [D_133] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_133) = k7_relat_1('#skF_4',D_133) ),
    inference(resolution,[status(thm)],[c_34,c_382])).

tff(c_32,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_395,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_393,c_32])).

tff(c_464,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_461,c_395])).

tff(c_484,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_345,c_464])).

tff(c_493,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_484])).

tff(c_497,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_493])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:56 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.62/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.50  
% 2.62/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.50  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k2_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.62/1.50  
% 2.62/1.50  %Foreground sorts:
% 2.62/1.50  
% 2.62/1.50  
% 2.62/1.50  %Background operators:
% 2.62/1.50  
% 2.62/1.50  
% 2.62/1.50  %Foreground operators:
% 2.62/1.50  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.62/1.50  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.62/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.62/1.50  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.62/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.62/1.50  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.62/1.50  tff('#skF_2', type, '#skF_2': $i).
% 2.62/1.50  tff('#skF_3', type, '#skF_3': $i).
% 2.62/1.50  tff('#skF_1', type, '#skF_1': $i).
% 2.62/1.50  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.62/1.50  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.62/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.62/1.50  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.62/1.50  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.62/1.50  tff('#skF_4', type, '#skF_4': $i).
% 2.62/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.62/1.50  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.62/1.50  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.62/1.50  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.62/1.50  
% 2.62/1.52  tff(f_88, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_relset_1)).
% 2.62/1.52  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.62/1.52  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_relat_1)).
% 2.62/1.52  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.62/1.52  tff(f_45, axiom, (![A, B, C]: ((v1_relat_1(C) & v4_relat_1(C, B)) => ((v1_relat_1(k7_relat_1(C, A)) & v4_relat_1(k7_relat_1(C, A), A)) & v4_relat_1(k7_relat_1(C, A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc23_relat_1)).
% 2.62/1.52  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t99_relat_1)).
% 2.62/1.52  tff(f_71, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.62/1.52  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.62/1.52  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.62/1.52  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.62/1.52  tff(f_83, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 2.62/1.52  tff(f_75, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.62/1.52  tff(c_34, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.62/1.52  tff(c_45, plain, (![C_36, A_37, B_38]: (v1_relat_1(C_36) | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.62/1.52  tff(c_54, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_45])).
% 2.62/1.52  tff(c_14, plain, (![B_10, A_9]: (r1_tarski(k1_relat_1(k7_relat_1(B_10, A_9)), A_9) | ~v1_relat_1(B_10))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.62/1.52  tff(c_67, plain, (![C_44, A_45, B_46]: (v4_relat_1(C_44, A_45) | ~m1_subset_1(C_44, k1_zfmisc_1(k2_zfmisc_1(A_45, B_46))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.62/1.52  tff(c_76, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_34, c_67])).
% 2.62/1.52  tff(c_149, plain, (![C_66, A_67, B_68]: (v1_relat_1(k7_relat_1(C_66, A_67)) | ~v4_relat_1(C_66, B_68) | ~v1_relat_1(C_66))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.62/1.52  tff(c_153, plain, (![A_67]: (v1_relat_1(k7_relat_1('#skF_4', A_67)) | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_76, c_149])).
% 2.62/1.52  tff(c_157, plain, (![A_67]: (v1_relat_1(k7_relat_1('#skF_4', A_67)))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_153])).
% 2.62/1.52  tff(c_16, plain, (![B_12, A_11]: (r1_tarski(k2_relat_1(k7_relat_1(B_12, A_11)), k2_relat_1(B_12)) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.62/1.52  tff(c_226, plain, (![A_94, B_95, C_96]: (k2_relset_1(A_94, B_95, C_96)=k2_relat_1(C_96) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_94, B_95))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.62/1.52  tff(c_235, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_34, c_226])).
% 2.62/1.52  tff(c_294, plain, (![A_120, B_121, C_122]: (m1_subset_1(k2_relset_1(A_120, B_121, C_122), k1_zfmisc_1(B_121)) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_120, B_121))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.62/1.52  tff(c_316, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_235, c_294])).
% 2.62/1.52  tff(c_323, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_34, c_316])).
% 2.62/1.52  tff(c_4, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | ~m1_subset_1(A_4, k1_zfmisc_1(B_5)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.62/1.52  tff(c_327, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_323, c_4])).
% 2.62/1.52  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.62/1.52  tff(c_334, plain, (![A_123]: (r1_tarski(A_123, '#skF_3') | ~r1_tarski(A_123, k2_relat_1('#skF_4')))), inference(resolution, [status(thm)], [c_327, c_2])).
% 2.62/1.52  tff(c_338, plain, (![A_11]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_11)), '#skF_3') | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_16, c_334])).
% 2.62/1.52  tff(c_345, plain, (![A_11]: (r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_11)), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_338])).
% 2.62/1.52  tff(c_461, plain, (![C_148, A_149, B_150]: (m1_subset_1(C_148, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~r1_tarski(k2_relat_1(C_148), B_150) | ~r1_tarski(k1_relat_1(C_148), A_149) | ~v1_relat_1(C_148))), inference(cnfTransformation, [status(thm)], [f_83])).
% 2.62/1.52  tff(c_382, plain, (![A_130, B_131, C_132, D_133]: (k5_relset_1(A_130, B_131, C_132, D_133)=k7_relat_1(C_132, D_133) | ~m1_subset_1(C_132, k1_zfmisc_1(k2_zfmisc_1(A_130, B_131))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.62/1.52  tff(c_393, plain, (![D_133]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_133)=k7_relat_1('#skF_4', D_133))), inference(resolution, [status(thm)], [c_34, c_382])).
% 2.62/1.52  tff(c_32, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.62/1.52  tff(c_395, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_393, c_32])).
% 2.62/1.52  tff(c_464, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_461, c_395])).
% 2.62/1.52  tff(c_484, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_345, c_464])).
% 2.62/1.52  tff(c_493, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_484])).
% 2.62/1.52  tff(c_497, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_54, c_493])).
% 2.62/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.62/1.52  
% 2.62/1.52  Inference rules
% 2.62/1.52  ----------------------
% 2.62/1.52  #Ref     : 0
% 2.62/1.52  #Sup     : 99
% 2.62/1.52  #Fact    : 0
% 2.62/1.52  #Define  : 0
% 2.62/1.52  #Split   : 1
% 2.62/1.52  #Chain   : 0
% 2.62/1.52  #Close   : 0
% 2.62/1.52  
% 2.62/1.52  Ordering : KBO
% 2.62/1.52  
% 2.62/1.52  Simplification rules
% 2.62/1.52  ----------------------
% 2.62/1.52  #Subsume      : 7
% 2.62/1.52  #Demod        : 24
% 2.62/1.52  #Tautology    : 11
% 2.62/1.52  #SimpNegUnit  : 0
% 2.62/1.52  #BackRed      : 2
% 2.62/1.52  
% 2.62/1.52  #Partial instantiations: 0
% 2.62/1.52  #Strategies tried      : 1
% 2.62/1.52  
% 2.62/1.52  Timing (in seconds)
% 2.62/1.52  ----------------------
% 2.62/1.52  Preprocessing        : 0.30
% 2.62/1.52  Parsing              : 0.17
% 2.62/1.52  CNF conversion       : 0.02
% 2.62/1.52  Main loop            : 0.32
% 2.62/1.52  Inferencing          : 0.13
% 2.62/1.52  Reduction            : 0.09
% 2.62/1.52  Demodulation         : 0.06
% 2.62/1.52  BG Simplification    : 0.02
% 2.62/1.52  Subsumption          : 0.06
% 2.62/1.52  Abstraction          : 0.02
% 2.62/1.52  MUC search           : 0.00
% 2.62/1.52  Cooper               : 0.00
% 2.62/1.52  Total                : 0.65
% 2.62/1.52  Index Insertion      : 0.00
% 2.62/1.52  Index Deletion       : 0.00
% 2.62/1.52  Index Matching       : 0.00
% 2.62/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------
