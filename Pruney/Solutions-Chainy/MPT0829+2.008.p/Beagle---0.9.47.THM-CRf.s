%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:07:22 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.43s
% Verified   : 
% Statistics : Number of formulae       :   68 ( 127 expanded)
%              Number of leaves         :   29 (  55 expanded)
%              Depth                    :    9
%              Number of atoms          :   92 ( 223 expanded)
%              Number of equality atoms :   24 (  67 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_80,negated_conjecture,(
    ~ ! [A,B,C] :
        ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
       => ( r1_tarski(k6_relat_1(B),C)
         => ( r1_tarski(B,k1_relset_1(A,B,C))
            & B = k2_relset_1(A,B,C) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t32_relset_1)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_71,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( r1_tarski(k6_relat_1(C),D)
       => ( r1_tarski(C,k1_relset_1(A,B,D))
          & r1_tarski(C,k2_relset_1(A,B,D)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_relset_1)).

tff(f_37,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_33,axiom,(
    ! [A] : v1_relat_1(k6_relat_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k1_relat_1(B),A)
       => k5_relat_1(k6_relat_1(A),B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t77_relat_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k5_relat_1(B,k6_relat_1(A)) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_relat_1)).

tff(c_32,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_297,plain,(
    ! [A_85,B_86,C_87] :
      ( k2_relset_1(A_85,B_86,C_87) = k2_relat_1(C_87)
      | ~ m1_subset_1(C_87,k1_zfmisc_1(k2_zfmisc_1(A_85,B_86))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_301,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_297])).

tff(c_28,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_64,plain,(
    ~ r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_30,plain,(
    r1_tarski(k6_relat_1('#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_185,plain,(
    ! [C_59,A_60,B_61,D_62] :
      ( r1_tarski(C_59,k1_relset_1(A_60,B_61,D_62))
      | ~ r1_tarski(k6_relat_1(C_59),D_62)
      | ~ m1_subset_1(D_62,k1_zfmisc_1(k2_zfmisc_1(A_60,B_61))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_189,plain,(
    ! [A_63,B_64] :
      ( r1_tarski('#skF_2',k1_relset_1(A_63,B_64,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(resolution,[status(thm)],[c_30,c_185])).

tff(c_192,plain,(
    r1_tarski('#skF_2',k1_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_189])).

tff(c_196,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_192])).

tff(c_197,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_302,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_197])).

tff(c_10,plain,(
    ! [A_4] : k2_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_52,plain,(
    ! [C_25,A_26,B_27] :
      ( v1_relat_1(C_25)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_56,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_32,c_52])).

tff(c_219,plain,(
    ! [C_72,B_73,A_74] :
      ( v5_relat_1(C_72,B_73)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_74,B_73))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_223,plain,(
    v5_relat_1('#skF_3','#skF_2') ),
    inference(resolution,[status(thm)],[c_32,c_219])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( r1_tarski(k2_relat_1(B_2),A_1)
      | ~ v5_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_324,plain,(
    ! [C_92,A_93,B_94,D_95] :
      ( r1_tarski(C_92,k2_relset_1(A_93,B_94,D_95))
      | ~ r1_tarski(k6_relat_1(C_92),D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_328,plain,(
    ! [A_96,B_97] :
      ( r1_tarski('#skF_2',k2_relset_1(A_96,B_97,'#skF_3'))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_96,B_97))) ) ),
    inference(resolution,[status(thm)],[c_30,c_324])).

tff(c_331,plain,(
    r1_tarski('#skF_2',k2_relset_1('#skF_1','#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_32,c_328])).

tff(c_333,plain,(
    r1_tarski('#skF_2',k2_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_331])).

tff(c_6,plain,(
    ! [A_3] : v1_relat_1(k6_relat_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_8,plain,(
    ! [A_4] : k1_relat_1(k6_relat_1(A_4)) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_265,plain,(
    ! [A_81,B_82] :
      ( k5_relat_1(k6_relat_1(A_81),B_82) = B_82
      | ~ r1_tarski(k1_relat_1(B_82),A_81)
      | ~ v1_relat_1(B_82) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_268,plain,(
    ! [A_81,A_4] :
      ( k5_relat_1(k6_relat_1(A_81),k6_relat_1(A_4)) = k6_relat_1(A_4)
      | ~ r1_tarski(A_4,A_81)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_265])).

tff(c_271,plain,(
    ! [A_83,A_84] :
      ( k5_relat_1(k6_relat_1(A_83),k6_relat_1(A_84)) = k6_relat_1(A_84)
      | ~ r1_tarski(A_84,A_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_268])).

tff(c_224,plain,(
    ! [B_75,A_76] :
      ( k5_relat_1(B_75,k6_relat_1(A_76)) = B_75
      | ~ r1_tarski(k2_relat_1(B_75),A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_230,plain,(
    ! [A_4,A_76] :
      ( k5_relat_1(k6_relat_1(A_4),k6_relat_1(A_76)) = k6_relat_1(A_4)
      | ~ r1_tarski(A_4,A_76)
      | ~ v1_relat_1(k6_relat_1(A_4)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_224])).

tff(c_233,plain,(
    ! [A_4,A_76] :
      ( k5_relat_1(k6_relat_1(A_4),k6_relat_1(A_76)) = k6_relat_1(A_4)
      | ~ r1_tarski(A_4,A_76) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_230])).

tff(c_277,plain,(
    ! [A_84,A_83] :
      ( k6_relat_1(A_84) = k6_relat_1(A_83)
      | ~ r1_tarski(A_83,A_84)
      | ~ r1_tarski(A_84,A_83) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_233])).

tff(c_336,plain,
    ( k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2')
    | ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_333,c_277])).

tff(c_337,plain,(
    ~ r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_336])).

tff(c_340,plain,
    ( ~ v5_relat_1('#skF_3','#skF_2')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_4,c_337])).

tff(c_344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_223,c_340])).

tff(c_345,plain,(
    k6_relat_1(k2_relat_1('#skF_3')) = k6_relat_1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_336])).

tff(c_393,plain,(
    k2_relat_1(k6_relat_1('#skF_2')) = k2_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_345,c_10])).

tff(c_404,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_393])).

tff(c_406,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_302,c_404])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:54 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.32  
% 2.17/1.32  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.32  %$ v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.32  
% 2.17/1.32  %Foreground sorts:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Background operators:
% 2.17/1.32  
% 2.17/1.32  
% 2.17/1.32  %Foreground operators:
% 2.17/1.32  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.32  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.17/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.32  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.17/1.32  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.32  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.32  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.17/1.32  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.17/1.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.17/1.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.17/1.32  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.17/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.32  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.17/1.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.17/1.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.17/1.32  
% 2.43/1.34  tff(f_80, negated_conjecture, ~(![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(B), C) => (r1_tarski(B, k1_relset_1(A, B, C)) & (B = k2_relset_1(A, B, C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t32_relset_1)).
% 2.43/1.34  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.43/1.34  tff(f_71, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (r1_tarski(k6_relat_1(C), D) => (r1_tarski(C, k1_relset_1(A, B, D)) & r1_tarski(C, k2_relset_1(A, B, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t30_relset_1)).
% 2.43/1.34  tff(f_37, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_relat_1)).
% 2.43/1.34  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.43/1.34  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.43/1.34  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 2.43/1.34  tff(f_33, axiom, (![A]: v1_relat_1(k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_relat_1)).
% 2.43/1.34  tff(f_43, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k1_relat_1(B), A) => (k5_relat_1(k6_relat_1(A), B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t77_relat_1)).
% 2.43/1.34  tff(f_49, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k5_relat_1(B, k6_relat_1(A)) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_relat_1)).
% 2.43/1.34  tff(c_32, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.34  tff(c_297, plain, (![A_85, B_86, C_87]: (k2_relset_1(A_85, B_86, C_87)=k2_relat_1(C_87) | ~m1_subset_1(C_87, k1_zfmisc_1(k2_zfmisc_1(A_85, B_86))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.43/1.34  tff(c_301, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_297])).
% 2.43/1.34  tff(c_28, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.34  tff(c_64, plain, (~r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(splitLeft, [status(thm)], [c_28])).
% 2.43/1.34  tff(c_30, plain, (r1_tarski(k6_relat_1('#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.43/1.34  tff(c_185, plain, (![C_59, A_60, B_61, D_62]: (r1_tarski(C_59, k1_relset_1(A_60, B_61, D_62)) | ~r1_tarski(k6_relat_1(C_59), D_62) | ~m1_subset_1(D_62, k1_zfmisc_1(k2_zfmisc_1(A_60, B_61))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.43/1.34  tff(c_189, plain, (![A_63, B_64]: (r1_tarski('#skF_2', k1_relset_1(A_63, B_64, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(resolution, [status(thm)], [c_30, c_185])).
% 2.43/1.34  tff(c_192, plain, (r1_tarski('#skF_2', k1_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_189])).
% 2.43/1.34  tff(c_196, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_192])).
% 2.43/1.34  tff(c_197, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(splitRight, [status(thm)], [c_28])).
% 2.43/1.34  tff(c_302, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_301, c_197])).
% 2.43/1.34  tff(c_10, plain, (![A_4]: (k2_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.34  tff(c_52, plain, (![C_25, A_26, B_27]: (v1_relat_1(C_25) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.43/1.34  tff(c_56, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_32, c_52])).
% 2.43/1.34  tff(c_219, plain, (![C_72, B_73, A_74]: (v5_relat_1(C_72, B_73) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_74, B_73))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.43/1.34  tff(c_223, plain, (v5_relat_1('#skF_3', '#skF_2')), inference(resolution, [status(thm)], [c_32, c_219])).
% 2.43/1.34  tff(c_4, plain, (![B_2, A_1]: (r1_tarski(k2_relat_1(B_2), A_1) | ~v5_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.43/1.34  tff(c_324, plain, (![C_92, A_93, B_94, D_95]: (r1_tarski(C_92, k2_relset_1(A_93, B_94, D_95)) | ~r1_tarski(k6_relat_1(C_92), D_95) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.43/1.34  tff(c_328, plain, (![A_96, B_97]: (r1_tarski('#skF_2', k2_relset_1(A_96, B_97, '#skF_3')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_96, B_97))))), inference(resolution, [status(thm)], [c_30, c_324])).
% 2.43/1.34  tff(c_331, plain, (r1_tarski('#skF_2', k2_relset_1('#skF_1', '#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_32, c_328])).
% 2.43/1.34  tff(c_333, plain, (r1_tarski('#skF_2', k2_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_301, c_331])).
% 2.43/1.34  tff(c_6, plain, (![A_3]: (v1_relat_1(k6_relat_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.43/1.34  tff(c_8, plain, (![A_4]: (k1_relat_1(k6_relat_1(A_4))=A_4)), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.43/1.34  tff(c_265, plain, (![A_81, B_82]: (k5_relat_1(k6_relat_1(A_81), B_82)=B_82 | ~r1_tarski(k1_relat_1(B_82), A_81) | ~v1_relat_1(B_82))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.43/1.34  tff(c_268, plain, (![A_81, A_4]: (k5_relat_1(k6_relat_1(A_81), k6_relat_1(A_4))=k6_relat_1(A_4) | ~r1_tarski(A_4, A_81) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_8, c_265])).
% 2.43/1.34  tff(c_271, plain, (![A_83, A_84]: (k5_relat_1(k6_relat_1(A_83), k6_relat_1(A_84))=k6_relat_1(A_84) | ~r1_tarski(A_84, A_83))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_268])).
% 2.43/1.34  tff(c_224, plain, (![B_75, A_76]: (k5_relat_1(B_75, k6_relat_1(A_76))=B_75 | ~r1_tarski(k2_relat_1(B_75), A_76) | ~v1_relat_1(B_75))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.43/1.34  tff(c_230, plain, (![A_4, A_76]: (k5_relat_1(k6_relat_1(A_4), k6_relat_1(A_76))=k6_relat_1(A_4) | ~r1_tarski(A_4, A_76) | ~v1_relat_1(k6_relat_1(A_4)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_224])).
% 2.43/1.34  tff(c_233, plain, (![A_4, A_76]: (k5_relat_1(k6_relat_1(A_4), k6_relat_1(A_76))=k6_relat_1(A_4) | ~r1_tarski(A_4, A_76))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_230])).
% 2.43/1.34  tff(c_277, plain, (![A_84, A_83]: (k6_relat_1(A_84)=k6_relat_1(A_83) | ~r1_tarski(A_83, A_84) | ~r1_tarski(A_84, A_83))), inference(superposition, [status(thm), theory('equality')], [c_271, c_233])).
% 2.43/1.34  tff(c_336, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2') | ~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_333, c_277])).
% 2.43/1.34  tff(c_337, plain, (~r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(splitLeft, [status(thm)], [c_336])).
% 2.43/1.34  tff(c_340, plain, (~v5_relat_1('#skF_3', '#skF_2') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_4, c_337])).
% 2.43/1.34  tff(c_344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_56, c_223, c_340])).
% 2.43/1.34  tff(c_345, plain, (k6_relat_1(k2_relat_1('#skF_3'))=k6_relat_1('#skF_2')), inference(splitRight, [status(thm)], [c_336])).
% 2.43/1.34  tff(c_393, plain, (k2_relat_1(k6_relat_1('#skF_2'))=k2_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_345, c_10])).
% 2.43/1.34  tff(c_404, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_393])).
% 2.43/1.34  tff(c_406, plain, $false, inference(negUnitSimplification, [status(thm)], [c_302, c_404])).
% 2.43/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.43/1.34  
% 2.43/1.34  Inference rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Ref     : 0
% 2.43/1.34  #Sup     : 82
% 2.43/1.34  #Fact    : 0
% 2.43/1.34  #Define  : 0
% 2.43/1.34  #Split   : 5
% 2.43/1.34  #Chain   : 0
% 2.43/1.34  #Close   : 0
% 2.43/1.34  
% 2.43/1.34  Ordering : KBO
% 2.43/1.34  
% 2.43/1.34  Simplification rules
% 2.43/1.34  ----------------------
% 2.43/1.34  #Subsume      : 6
% 2.43/1.34  #Demod        : 27
% 2.43/1.34  #Tautology    : 30
% 2.43/1.34  #SimpNegUnit  : 2
% 2.43/1.34  #BackRed      : 1
% 2.43/1.34  
% 2.43/1.34  #Partial instantiations: 0
% 2.43/1.34  #Strategies tried      : 1
% 2.43/1.34  
% 2.43/1.34  Timing (in seconds)
% 2.43/1.34  ----------------------
% 2.43/1.34  Preprocessing        : 0.32
% 2.43/1.35  Parsing              : 0.17
% 2.43/1.35  CNF conversion       : 0.02
% 2.43/1.35  Main loop            : 0.27
% 2.43/1.35  Inferencing          : 0.11
% 2.43/1.35  Reduction            : 0.08
% 2.43/1.35  Demodulation         : 0.05
% 2.43/1.35  BG Simplification    : 0.02
% 2.43/1.35  Subsumption          : 0.04
% 2.43/1.35  Abstraction          : 0.02
% 2.43/1.35  MUC search           : 0.00
% 2.43/1.35  Cooper               : 0.00
% 2.43/1.35  Total                : 0.62
% 2.43/1.35  Index Insertion      : 0.00
% 2.43/1.35  Index Deletion       : 0.00
% 2.43/1.35  Index Matching       : 0.00
% 2.43/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
