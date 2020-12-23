%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:17 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   62 (  72 expanded)
%              Number of leaves         :   35 (  42 expanded)
%              Depth                    :    6
%              Number of atoms          :   78 ( 116 expanded)
%              Number of equality atoms :   29 (  36 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => r2_hidden(k1_funct_1(C,A),B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_2)).

tff(f_64,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_70,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_60,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v5_relat_1(B,A)
        & v1_funct_1(B) )
     => ! [C] :
          ( r2_hidden(C,k1_relat_1(B))
         => r2_hidden(k1_funct_1(B,C),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t172_funct_1)).

tff(f_74,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( ( B = k1_xboole_0
           => A = k1_xboole_0 )
         => ( v1_funct_2(C,A,B)
          <=> A = k1_relset_1(A,B,C) ) )
        & ( B = k1_xboole_0
         => ( A = k1_xboole_0
            | ( v1_funct_2(C,A,B)
            <=> C = k1_xboole_0 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_29,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_31,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D,E] :
      ( E = k2_enumset1(A,B,C,D)
    <=> ! [F] :
          ( r2_hidden(F,E)
        <=> ~ ( F != A
              & F != B
              & F != C
              & F != D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_enumset1)).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_91,plain,(
    ! [C_50,A_51,B_52] :
      ( v1_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_95,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_91])).

tff(c_96,plain,(
    ! [C_53,B_54,A_55] :
      ( v5_relat_1(C_53,B_54)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_55,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_100,plain,(
    v5_relat_1('#skF_5','#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_96])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_227,plain,(
    ! [B_100,C_101,A_102] :
      ( r2_hidden(k1_funct_1(B_100,C_101),A_102)
      | ~ r2_hidden(C_101,k1_relat_1(B_100))
      | ~ v1_funct_1(B_100)
      | ~ v5_relat_1(B_100,A_102)
      | ~ v1_relat_1(B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_60,plain,(
    ~ r2_hidden(k1_funct_1('#skF_5','#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_246,plain,
    ( ~ r2_hidden('#skF_3',k1_relat_1('#skF_5'))
    | ~ v1_funct_1('#skF_5')
    | ~ v5_relat_1('#skF_5','#skF_4')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_227,c_60])).

tff(c_253,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_100,c_68,c_246])).

tff(c_62,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_66,plain,(
    v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_151,plain,(
    ! [A_76,B_77,C_78] :
      ( k1_relset_1(A_76,B_77,C_78) = k1_relat_1(C_78)
      | ~ m1_subset_1(C_78,k1_zfmisc_1(k2_zfmisc_1(A_76,B_77))) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_155,plain,(
    k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_151])).

tff(c_259,plain,(
    ! [B_106,A_107,C_108] :
      ( k1_xboole_0 = B_106
      | k1_relset_1(A_107,B_106,C_108) = A_107
      | ~ v1_funct_2(C_108,A_107,B_106)
      | ~ m1_subset_1(C_108,k1_zfmisc_1(k2_zfmisc_1(A_107,B_106))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_262,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1(k1_tarski('#skF_3'),'#skF_4','#skF_5') = k1_tarski('#skF_3')
    | ~ v1_funct_2('#skF_5',k1_tarski('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_259])).

tff(c_265,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_155,c_262])).

tff(c_266,plain,(
    k1_tarski('#skF_3') = k1_relat_1('#skF_5') ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_265])).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_2,B_3] : k1_enumset1(A_2,A_2,B_3) = k2_tarski(A_2,B_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_56,B_57,C_58] : k2_enumset1(A_56,A_56,B_57,C_58) = k1_enumset1(A_56,B_57,C_58) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [F_14,B_8,C_9,D_10] : r2_hidden(F_14,k2_enumset1(F_14,B_8,C_9,D_10)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_122,plain,(
    ! [A_59,B_60,C_61] : r2_hidden(A_59,k1_enumset1(A_59,B_60,C_61)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_16])).

tff(c_126,plain,(
    ! [A_62,B_63] : r2_hidden(A_62,k2_tarski(A_62,B_63)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_122])).

tff(c_129,plain,(
    ! [A_1] : r2_hidden(A_1,k1_tarski(A_1)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_126])).

tff(c_277,plain,(
    r2_hidden('#skF_3',k1_relat_1('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_266,c_129])).

tff(c_281,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_253,c_277])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:12:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.28  
% 2.27/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.28  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_enumset1 > k1_relset_1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_1 > #skF_4
% 2.27/1.28  
% 2.27/1.28  %Foreground sorts:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Background operators:
% 2.27/1.28  
% 2.27/1.28  
% 2.27/1.28  %Foreground operators:
% 2.27/1.28  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.27/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.27/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i * $i) > $i).
% 2.27/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.27/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.27/1.28  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.27/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.27/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.28  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.27/1.28  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 2.27/1.28  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.27/1.28  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i * $i) > $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.28  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.27/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.27/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.27/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.28  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 2.27/1.28  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.27/1.28  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.27/1.28  
% 2.27/1.29  tff(f_104, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => r2_hidden(k1_funct_1(C, A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_2)).
% 2.27/1.29  tff(f_64, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.27/1.29  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 2.27/1.29  tff(f_60, axiom, (![A, B]: (((v1_relat_1(B) & v5_relat_1(B, A)) & v1_funct_1(B)) => (![C]: (r2_hidden(C, k1_relat_1(B)) => r2_hidden(k1_funct_1(B, C), A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t172_funct_1)).
% 2.27/1.29  tff(f_74, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.27/1.29  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.27/1.29  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.27/1.29  tff(f_29, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.27/1.29  tff(f_31, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.27/1.29  tff(f_49, axiom, (![A, B, C, D, E]: ((E = k2_enumset1(A, B, C, D)) <=> (![F]: (r2_hidden(F, E) <=> ~(((~(F = A) & ~(F = B)) & ~(F = C)) & ~(F = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_enumset1)).
% 2.27/1.29  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.27/1.29  tff(c_91, plain, (![C_50, A_51, B_52]: (v1_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.27/1.29  tff(c_95, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_91])).
% 2.27/1.29  tff(c_96, plain, (![C_53, B_54, A_55]: (v5_relat_1(C_53, B_54) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_55, B_54))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.27/1.29  tff(c_100, plain, (v5_relat_1('#skF_5', '#skF_4')), inference(resolution, [status(thm)], [c_64, c_96])).
% 2.27/1.29  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.27/1.29  tff(c_227, plain, (![B_100, C_101, A_102]: (r2_hidden(k1_funct_1(B_100, C_101), A_102) | ~r2_hidden(C_101, k1_relat_1(B_100)) | ~v1_funct_1(B_100) | ~v5_relat_1(B_100, A_102) | ~v1_relat_1(B_100))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.29  tff(c_60, plain, (~r2_hidden(k1_funct_1('#skF_5', '#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.27/1.29  tff(c_246, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5')) | ~v1_funct_1('#skF_5') | ~v5_relat_1('#skF_5', '#skF_4') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_227, c_60])).
% 2.27/1.29  tff(c_253, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_95, c_100, c_68, c_246])).
% 2.27/1.29  tff(c_62, plain, (k1_xboole_0!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.27/1.29  tff(c_66, plain, (v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.27/1.29  tff(c_151, plain, (![A_76, B_77, C_78]: (k1_relset_1(A_76, B_77, C_78)=k1_relat_1(C_78) | ~m1_subset_1(C_78, k1_zfmisc_1(k2_zfmisc_1(A_76, B_77))))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.27/1.29  tff(c_155, plain, (k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_151])).
% 2.27/1.29  tff(c_259, plain, (![B_106, A_107, C_108]: (k1_xboole_0=B_106 | k1_relset_1(A_107, B_106, C_108)=A_107 | ~v1_funct_2(C_108, A_107, B_106) | ~m1_subset_1(C_108, k1_zfmisc_1(k2_zfmisc_1(A_107, B_106))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.27/1.29  tff(c_262, plain, (k1_xboole_0='#skF_4' | k1_relset_1(k1_tarski('#skF_3'), '#skF_4', '#skF_5')=k1_tarski('#skF_3') | ~v1_funct_2('#skF_5', k1_tarski('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_64, c_259])).
% 2.27/1.29  tff(c_265, plain, (k1_xboole_0='#skF_4' | k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_66, c_155, c_262])).
% 2.27/1.29  tff(c_266, plain, (k1_tarski('#skF_3')=k1_relat_1('#skF_5')), inference(negUnitSimplification, [status(thm)], [c_62, c_265])).
% 2.27/1.29  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.29  tff(c_4, plain, (![A_2, B_3]: (k1_enumset1(A_2, A_2, B_3)=k2_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.27/1.29  tff(c_101, plain, (![A_56, B_57, C_58]: (k2_enumset1(A_56, A_56, B_57, C_58)=k1_enumset1(A_56, B_57, C_58))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.27/1.29  tff(c_16, plain, (![F_14, B_8, C_9, D_10]: (r2_hidden(F_14, k2_enumset1(F_14, B_8, C_9, D_10)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.29  tff(c_122, plain, (![A_59, B_60, C_61]: (r2_hidden(A_59, k1_enumset1(A_59, B_60, C_61)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_16])).
% 2.27/1.29  tff(c_126, plain, (![A_62, B_63]: (r2_hidden(A_62, k2_tarski(A_62, B_63)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_122])).
% 2.27/1.29  tff(c_129, plain, (![A_1]: (r2_hidden(A_1, k1_tarski(A_1)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_126])).
% 2.27/1.29  tff(c_277, plain, (r2_hidden('#skF_3', k1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_266, c_129])).
% 2.27/1.29  tff(c_281, plain, $false, inference(negUnitSimplification, [status(thm)], [c_253, c_277])).
% 2.27/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.29  
% 2.27/1.29  Inference rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Ref     : 0
% 2.27/1.29  #Sup     : 45
% 2.27/1.29  #Fact    : 0
% 2.27/1.29  #Define  : 0
% 2.27/1.29  #Split   : 0
% 2.27/1.29  #Chain   : 0
% 2.27/1.29  #Close   : 0
% 2.27/1.29  
% 2.27/1.29  Ordering : KBO
% 2.27/1.29  
% 2.27/1.29  Simplification rules
% 2.27/1.29  ----------------------
% 2.27/1.29  #Subsume      : 0
% 2.27/1.29  #Demod        : 12
% 2.27/1.29  #Tautology    : 22
% 2.27/1.29  #SimpNegUnit  : 2
% 2.27/1.29  #BackRed      : 4
% 2.27/1.29  
% 2.27/1.29  #Partial instantiations: 0
% 2.27/1.29  #Strategies tried      : 1
% 2.27/1.29  
% 2.27/1.30  Timing (in seconds)
% 2.27/1.30  ----------------------
% 2.27/1.30  Preprocessing        : 0.33
% 2.27/1.30  Parsing              : 0.17
% 2.27/1.30  CNF conversion       : 0.02
% 2.27/1.30  Main loop            : 0.22
% 2.27/1.30  Inferencing          : 0.07
% 2.27/1.30  Reduction            : 0.07
% 2.27/1.30  Demodulation         : 0.05
% 2.27/1.30  BG Simplification    : 0.02
% 2.27/1.30  Subsumption          : 0.05
% 2.27/1.30  Abstraction          : 0.01
% 2.27/1.30  MUC search           : 0.00
% 2.27/1.30  Cooper               : 0.00
% 2.27/1.30  Total                : 0.58
% 2.27/1.30  Index Insertion      : 0.00
% 2.27/1.30  Index Deletion       : 0.00
% 2.27/1.30  Index Matching       : 0.00
% 2.27/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------
