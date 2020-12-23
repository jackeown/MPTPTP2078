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
% DateTime   : Thu Dec  3 10:07:28 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   56 (  94 expanded)
%              Number of leaves         :   28 (  43 expanded)
%              Depth                    :    8
%              Number of atoms          :   75 ( 147 expanded)
%              Number of equality atoms :    3 (   9 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
       => m1_subset_1(k5_relset_1(A,C,D,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k1_relat_1(k7_relat_1(B,A)),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k2_relat_1(k7_relat_1(B,A)),k2_relat_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t99_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_71,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k5_relset_1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k5_relset_1)).

tff(c_26,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_29,plain,(
    ! [C_29,A_30,B_31] :
      ( v1_relat_1(C_29)
      | ~ m1_subset_1(C_29,k1_zfmisc_1(k2_zfmisc_1(A_30,B_31))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_33,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_26,c_29])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( r1_tarski(k1_relat_1(k7_relat_1(B_9,A_8)),A_8)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,(
    ! [C_42,B_43,A_44] :
      ( v5_relat_1(C_42,B_43)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_44,B_43))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    v5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_52])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_11,A_10)),k2_relat_1(B_11))
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_38,plain,(
    ! [B_35,A_36] :
      ( r1_tarski(k2_relat_1(B_35),A_36)
      | ~ v5_relat_1(B_35,A_36)
      | ~ v1_relat_1(B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_90,plain,(
    ! [A_55,A_56,B_57] :
      ( r1_tarski(A_55,A_56)
      | ~ r1_tarski(A_55,k2_relat_1(B_57))
      | ~ v5_relat_1(B_57,A_56)
      | ~ v1_relat_1(B_57) ) ),
    inference(resolution,[status(thm)],[c_38,c_2])).

tff(c_99,plain,(
    ! [B_11,A_10,A_56] :
      ( r1_tarski(k2_relat_1(k7_relat_1(B_11,A_10)),A_56)
      | ~ v5_relat_1(B_11,A_56)
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( v1_relat_1(k7_relat_1(A_6,B_7))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_102,plain,(
    ! [C_58,A_59,B_60] :
      ( m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_59,B_60)))
      | ~ r1_tarski(k2_relat_1(C_58),B_60)
      | ~ r1_tarski(k1_relat_1(C_58),A_59)
      | ~ v1_relat_1(C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_76,plain,(
    ! [A_50,B_51,C_52,D_53] :
      ( k5_relset_1(A_50,B_51,C_52,D_53) = k7_relat_1(C_52,D_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_79,plain,(
    ! [D_53] : k5_relset_1('#skF_1','#skF_3','#skF_4',D_53) = k7_relat_1('#skF_4',D_53) ),
    inference(resolution,[status(thm)],[c_26,c_76])).

tff(c_24,plain,(
    ~ m1_subset_1(k5_relset_1('#skF_1','#skF_3','#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_80,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_24])).

tff(c_117,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(resolution,[status(thm)],[c_102,c_80])).

tff(c_222,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_4','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_117])).

tff(c_225,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8,c_222])).

tff(c_229,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_225])).

tff(c_230,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_117])).

tff(c_232,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_230])).

tff(c_235,plain,
    ( ~ v5_relat_1('#skF_4','#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_99,c_232])).

tff(c_242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_56,c_235])).

tff(c_243,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_230])).

tff(c_247,plain,(
    ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_10,c_243])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_33,c_247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 14:01:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  
% 2.17/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k5_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.17/1.27  
% 2.17/1.27  %Foreground sorts:
% 2.17/1.27  
% 2.17/1.27  
% 2.17/1.27  %Background operators:
% 2.17/1.27  
% 2.17/1.27  
% 2.17/1.27  %Foreground operators:
% 2.17/1.27  tff(k5_relset_1, type, k5_relset_1: ($i * $i * $i * $i) > $i).
% 2.17/1.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.27  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 2.17/1.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.27  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.27  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.27  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.27  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.27  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.27  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.27  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.27  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.27  tff('#skF_4', type, '#skF_4': $i).
% 2.17/1.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.27  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.27  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.27  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.27  
% 2.17/1.28  tff(f_76, negated_conjecture, ~(![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => m1_subset_1(k5_relset_1(A, C, D, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t33_relset_1)).
% 2.17/1.28  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.17/1.28  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k1_relat_1(k7_relat_1(B, A)), A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_relat_1)).
% 2.17/1.28  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.17/1.28  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k7_relat_1(B, A)), k2_relat_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t99_relat_1)).
% 2.17/1.28  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 2.17/1.28  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.17/1.28  tff(f_41, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 2.17/1.28  tff(f_71, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 2.17/1.28  tff(f_63, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k5_relset_1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k5_relset_1)).
% 2.17/1.28  tff(c_26, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.28  tff(c_29, plain, (![C_29, A_30, B_31]: (v1_relat_1(C_29) | ~m1_subset_1(C_29, k1_zfmisc_1(k2_zfmisc_1(A_30, B_31))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.17/1.28  tff(c_33, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_26, c_29])).
% 2.17/1.28  tff(c_10, plain, (![B_9, A_8]: (r1_tarski(k1_relat_1(k7_relat_1(B_9, A_8)), A_8) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.17/1.28  tff(c_52, plain, (![C_42, B_43, A_44]: (v5_relat_1(C_42, B_43) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_44, B_43))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.17/1.28  tff(c_56, plain, (v5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_26, c_52])).
% 2.17/1.28  tff(c_12, plain, (![B_11, A_10]: (r1_tarski(k2_relat_1(k7_relat_1(B_11, A_10)), k2_relat_1(B_11)) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.17/1.28  tff(c_38, plain, (![B_35, A_36]: (r1_tarski(k2_relat_1(B_35), A_36) | ~v5_relat_1(B_35, A_36) | ~v1_relat_1(B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.28  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.28  tff(c_90, plain, (![A_55, A_56, B_57]: (r1_tarski(A_55, A_56) | ~r1_tarski(A_55, k2_relat_1(B_57)) | ~v5_relat_1(B_57, A_56) | ~v1_relat_1(B_57))), inference(resolution, [status(thm)], [c_38, c_2])).
% 2.17/1.28  tff(c_99, plain, (![B_11, A_10, A_56]: (r1_tarski(k2_relat_1(k7_relat_1(B_11, A_10)), A_56) | ~v5_relat_1(B_11, A_56) | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_12, c_90])).
% 2.17/1.28  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k7_relat_1(A_6, B_7)) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.17/1.28  tff(c_102, plain, (![C_58, A_59, B_60]: (m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_59, B_60))) | ~r1_tarski(k2_relat_1(C_58), B_60) | ~r1_tarski(k1_relat_1(C_58), A_59) | ~v1_relat_1(C_58))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.17/1.28  tff(c_76, plain, (![A_50, B_51, C_52, D_53]: (k5_relset_1(A_50, B_51, C_52, D_53)=k7_relat_1(C_52, D_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.17/1.28  tff(c_79, plain, (![D_53]: (k5_relset_1('#skF_1', '#skF_3', '#skF_4', D_53)=k7_relat_1('#skF_4', D_53))), inference(resolution, [status(thm)], [c_26, c_76])).
% 2.17/1.28  tff(c_24, plain, (~m1_subset_1(k5_relset_1('#skF_1', '#skF_3', '#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.17/1.28  tff(c_80, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_24])).
% 2.17/1.28  tff(c_117, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(resolution, [status(thm)], [c_102, c_80])).
% 2.17/1.28  tff(c_222, plain, (~v1_relat_1(k7_relat_1('#skF_4', '#skF_2'))), inference(splitLeft, [status(thm)], [c_117])).
% 2.17/1.28  tff(c_225, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8, c_222])).
% 2.17/1.28  tff(c_229, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_225])).
% 2.17/1.28  tff(c_230, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_117])).
% 2.17/1.28  tff(c_232, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_230])).
% 2.17/1.28  tff(c_235, plain, (~v5_relat_1('#skF_4', '#skF_3') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_99, c_232])).
% 2.17/1.28  tff(c_242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_56, c_235])).
% 2.17/1.28  tff(c_243, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_230])).
% 2.17/1.28  tff(c_247, plain, (~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_10, c_243])).
% 2.17/1.28  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_33, c_247])).
% 2.17/1.28  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.28  
% 2.17/1.28  Inference rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Ref     : 0
% 2.17/1.28  #Sup     : 49
% 2.17/1.28  #Fact    : 0
% 2.17/1.28  #Define  : 0
% 2.17/1.28  #Split   : 2
% 2.17/1.28  #Chain   : 0
% 2.17/1.28  #Close   : 0
% 2.17/1.28  
% 2.17/1.28  Ordering : KBO
% 2.17/1.28  
% 2.17/1.28  Simplification rules
% 2.17/1.28  ----------------------
% 2.17/1.28  #Subsume      : 1
% 2.17/1.28  #Demod        : 5
% 2.17/1.28  #Tautology    : 4
% 2.17/1.28  #SimpNegUnit  : 0
% 2.17/1.28  #BackRed      : 1
% 2.17/1.28  
% 2.17/1.28  #Partial instantiations: 0
% 2.17/1.28  #Strategies tried      : 1
% 2.17/1.28  
% 2.17/1.28  Timing (in seconds)
% 2.17/1.28  ----------------------
% 2.17/1.28  Preprocessing        : 0.30
% 2.17/1.28  Parsing              : 0.16
% 2.17/1.28  CNF conversion       : 0.02
% 2.17/1.28  Main loop            : 0.22
% 2.17/1.28  Inferencing          : 0.08
% 2.17/1.28  Reduction            : 0.05
% 2.17/1.28  Demodulation         : 0.04
% 2.17/1.28  BG Simplification    : 0.01
% 2.17/1.28  Subsumption          : 0.05
% 2.17/1.28  Abstraction          : 0.01
% 2.17/1.28  MUC search           : 0.00
% 2.17/1.28  Cooper               : 0.00
% 2.17/1.28  Total                : 0.54
% 2.17/1.29  Index Insertion      : 0.00
% 2.17/1.29  Index Deletion       : 0.00
% 2.17/1.29  Index Matching       : 0.00
% 2.17/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------
