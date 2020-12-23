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
% DateTime   : Thu Dec  3 10:11:02 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   61 (  79 expanded)
%              Number of leaves         :   31 (  42 expanded)
%              Depth                    :   12
%              Number of atoms          :   85 ( 155 expanded)
%              Number of equality atoms :   25 (  35 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(k8_relat_1,type,(
    k8_relat_1: ( $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k1_funct_1,type,(
    k1_funct_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r2_hidden(C,A)
         => ( B = k1_xboole_0
            | r2_hidden(k1_funct_1(D,C),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_funct_2)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_79,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_35,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(k2_relat_1(B),A)
       => k8_relat_1(A,B) = B ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t125_relat_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( v1_relat_1(C)
        & v1_funct_1(C) )
     => ( r2_hidden(A,k1_relat_1(k8_relat_1(B,C)))
      <=> ( r2_hidden(A,k1_relat_1(C))
          & r2_hidden(k1_funct_1(C,A),B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_funct_1)).

tff(c_38,plain,(
    r2_hidden('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_36,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_42,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_40,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_98,plain,(
    ! [A_43,B_44,C_45] :
      ( k1_relset_1(A_43,B_44,C_45) = k1_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_107,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_98])).

tff(c_305,plain,(
    ! [B_91,A_92,C_93] :
      ( k1_xboole_0 = B_91
      | k1_relset_1(A_92,B_91,C_93) = A_92
      | ~ v1_funct_2(C_93,A_92,B_91)
      | ~ m1_subset_1(C_93,k1_zfmisc_1(k2_zfmisc_1(A_92,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_316,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_305])).

tff(c_321,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_107,c_316])).

tff(c_322,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_321])).

tff(c_55,plain,(
    ! [C_27,A_28,B_29] :
      ( v1_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_64,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_55])).

tff(c_44,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_78,plain,(
    ! [A_37,B_38,C_39] :
      ( k2_relset_1(A_37,B_38,C_39) = k2_relat_1(C_39)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_37,B_38))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_87,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_40,c_78])).

tff(c_118,plain,(
    ! [A_49,B_50,C_51] :
      ( m1_subset_1(k2_relset_1(A_49,B_50,C_51),k1_zfmisc_1(B_50))
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_87,c_118])).

tff(c_142,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_136])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_146,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_142,c_2])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k8_relat_1(A_3,B_4) = B_4
      | ~ r1_tarski(k2_relat_1(B_4),A_3)
      | ~ v1_relat_1(B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_149,plain,
    ( k8_relat_1('#skF_2','#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_146,c_6])).

tff(c_152,plain,(
    k8_relat_1('#skF_2','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_149])).

tff(c_220,plain,(
    ! [C_69,A_70,B_71] :
      ( r2_hidden(k1_funct_1(C_69,A_70),B_71)
      | ~ r2_hidden(A_70,k1_relat_1(k8_relat_1(B_71,C_69)))
      | ~ v1_funct_1(C_69)
      | ~ v1_relat_1(C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_223,plain,(
    ! [A_70] :
      ( r2_hidden(k1_funct_1('#skF_4',A_70),'#skF_2')
      | ~ r2_hidden(A_70,k1_relat_1('#skF_4'))
      | ~ v1_funct_1('#skF_4')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_220])).

tff(c_226,plain,(
    ! [A_72] :
      ( r2_hidden(k1_funct_1('#skF_4',A_72),'#skF_2')
      | ~ r2_hidden(A_72,k1_relat_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_44,c_223])).

tff(c_34,plain,(
    ~ r2_hidden(k1_funct_1('#skF_4','#skF_3'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_230,plain,(
    ~ r2_hidden('#skF_3',k1_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_226,c_34])).

tff(c_323,plain,(
    ~ r2_hidden('#skF_3','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_230])).

tff(c_328,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_323])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n013.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:43:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.30  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.31  
% 2.07/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.31  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k8_relat_1 > k2_zfmisc_1 > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.07/1.31  
% 2.07/1.31  %Foreground sorts:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Background operators:
% 2.07/1.31  
% 2.07/1.31  
% 2.07/1.31  %Foreground operators:
% 2.07/1.31  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.07/1.31  tff(k8_relat_1, type, k8_relat_1: ($i * $i) > $i).
% 2.07/1.31  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.31  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.07/1.31  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.31  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.07/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.31  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.07/1.31  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.31  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.31  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.31  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.31  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.31  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.31  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.31  
% 2.47/1.32  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_hidden(C, A) => ((B = k1_xboole_0) | r2_hidden(k1_funct_1(D, C), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_funct_2)).
% 2.47/1.32  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.47/1.32  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.47/1.32  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.47/1.32  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.47/1.32  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 2.47/1.32  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 2.47/1.32  tff(f_35, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(k2_relat_1(B), A) => (k8_relat_1(A, B) = B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t125_relat_1)).
% 2.47/1.32  tff(f_45, axiom, (![A, B, C]: ((v1_relat_1(C) & v1_funct_1(C)) => (r2_hidden(A, k1_relat_1(k8_relat_1(B, C))) <=> (r2_hidden(A, k1_relat_1(C)) & r2_hidden(k1_funct_1(C, A), B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_funct_1)).
% 2.47/1.32  tff(c_38, plain, (r2_hidden('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.32  tff(c_36, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.32  tff(c_42, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.32  tff(c_40, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.32  tff(c_98, plain, (![A_43, B_44, C_45]: (k1_relset_1(A_43, B_44, C_45)=k1_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.47/1.32  tff(c_107, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_98])).
% 2.47/1.32  tff(c_305, plain, (![B_91, A_92, C_93]: (k1_xboole_0=B_91 | k1_relset_1(A_92, B_91, C_93)=A_92 | ~v1_funct_2(C_93, A_92, B_91) | ~m1_subset_1(C_93, k1_zfmisc_1(k2_zfmisc_1(A_92, B_91))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 2.47/1.32  tff(c_316, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_40, c_305])).
% 2.47/1.32  tff(c_321, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_42, c_107, c_316])).
% 2.47/1.32  tff(c_322, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_36, c_321])).
% 2.47/1.32  tff(c_55, plain, (![C_27, A_28, B_29]: (v1_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.47/1.32  tff(c_64, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_55])).
% 2.47/1.32  tff(c_44, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.32  tff(c_78, plain, (![A_37, B_38, C_39]: (k2_relset_1(A_37, B_38, C_39)=k2_relat_1(C_39) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_37, B_38))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.47/1.32  tff(c_87, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_40, c_78])).
% 2.47/1.32  tff(c_118, plain, (![A_49, B_50, C_51]: (m1_subset_1(k2_relset_1(A_49, B_50, C_51), k1_zfmisc_1(B_50)) | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.47/1.32  tff(c_136, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_87, c_118])).
% 2.47/1.32  tff(c_142, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_136])).
% 2.47/1.32  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.47/1.32  tff(c_146, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_142, c_2])).
% 2.47/1.32  tff(c_6, plain, (![A_3, B_4]: (k8_relat_1(A_3, B_4)=B_4 | ~r1_tarski(k2_relat_1(B_4), A_3) | ~v1_relat_1(B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.32  tff(c_149, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_146, c_6])).
% 2.47/1.32  tff(c_152, plain, (k8_relat_1('#skF_2', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_64, c_149])).
% 2.47/1.32  tff(c_220, plain, (![C_69, A_70, B_71]: (r2_hidden(k1_funct_1(C_69, A_70), B_71) | ~r2_hidden(A_70, k1_relat_1(k8_relat_1(B_71, C_69))) | ~v1_funct_1(C_69) | ~v1_relat_1(C_69))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.47/1.32  tff(c_223, plain, (![A_70]: (r2_hidden(k1_funct_1('#skF_4', A_70), '#skF_2') | ~r2_hidden(A_70, k1_relat_1('#skF_4')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_152, c_220])).
% 2.47/1.32  tff(c_226, plain, (![A_72]: (r2_hidden(k1_funct_1('#skF_4', A_72), '#skF_2') | ~r2_hidden(A_72, k1_relat_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_44, c_223])).
% 2.47/1.32  tff(c_34, plain, (~r2_hidden(k1_funct_1('#skF_4', '#skF_3'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_92])).
% 2.47/1.32  tff(c_230, plain, (~r2_hidden('#skF_3', k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_226, c_34])).
% 2.47/1.32  tff(c_323, plain, (~r2_hidden('#skF_3', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_322, c_230])).
% 2.47/1.32  tff(c_328, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_38, c_323])).
% 2.47/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.32  
% 2.47/1.32  Inference rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Ref     : 0
% 2.47/1.32  #Sup     : 55
% 2.47/1.32  #Fact    : 0
% 2.47/1.32  #Define  : 0
% 2.47/1.32  #Split   : 0
% 2.47/1.32  #Chain   : 0
% 2.47/1.32  #Close   : 0
% 2.47/1.32  
% 2.47/1.32  Ordering : KBO
% 2.47/1.32  
% 2.47/1.32  Simplification rules
% 2.47/1.32  ----------------------
% 2.47/1.32  #Subsume      : 1
% 2.47/1.32  #Demod        : 23
% 2.47/1.32  #Tautology    : 15
% 2.47/1.32  #SimpNegUnit  : 3
% 2.47/1.32  #BackRed      : 3
% 2.47/1.32  
% 2.47/1.32  #Partial instantiations: 0
% 2.47/1.32  #Strategies tried      : 1
% 2.47/1.32  
% 2.47/1.32  Timing (in seconds)
% 2.47/1.32  ----------------------
% 2.47/1.33  Preprocessing        : 0.31
% 2.47/1.33  Parsing              : 0.16
% 2.47/1.33  CNF conversion       : 0.02
% 2.47/1.33  Main loop            : 0.22
% 2.47/1.33  Inferencing          : 0.08
% 2.47/1.33  Reduction            : 0.06
% 2.47/1.33  Demodulation         : 0.04
% 2.47/1.33  BG Simplification    : 0.02
% 2.47/1.33  Subsumption          : 0.04
% 2.47/1.33  Abstraction          : 0.01
% 2.47/1.33  MUC search           : 0.00
% 2.47/1.33  Cooper               : 0.00
% 2.47/1.33  Total                : 0.56
% 2.47/1.33  Index Insertion      : 0.00
% 2.47/1.33  Index Deletion       : 0.00
% 2.47/1.33  Index Matching       : 0.00
% 2.47/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------
