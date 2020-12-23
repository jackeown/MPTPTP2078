%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:55 EST 2020

% Result     : Theorem 2.31s
% Output     : CNFRefutation 2.37s
% Verified   : 
% Statistics : Number of formulae       :   62 (  91 expanded)
%              Number of leaves         :   30 (  47 expanded)
%              Depth                    :    5
%              Number of atoms          :   93 ( 223 expanded)
%              Number of equality atoms :   41 (  99 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

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

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_34,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( k2_relset_1(A,B,C) = B
            & v2_funct_1(C) )
         => ( B = k1_xboole_0
            | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
              & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_32,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_72,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_44,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_70,axiom,(
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

tff(c_4,plain,(
    ! [A_4,B_5] : v1_relat_1(k2_zfmisc_1(A_4,B_5)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_57,plain,(
    ! [B_20,A_21] :
      ( v1_relat_1(B_20)
      | ~ m1_subset_1(B_20,k1_zfmisc_1(A_21))
      | ~ v1_relat_1(A_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_60,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_57])).

tff(c_63,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_60])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_32,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_34,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_136,plain,(
    ! [A_43,B_44,C_45] :
      ( k2_relset_1(A_43,B_44,C_45) = k2_relat_1(C_45)
      | ~ m1_subset_1(C_45,k1_zfmisc_1(k2_zfmisc_1(A_43,B_44))) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_139,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_136])).

tff(c_141,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_139])).

tff(c_26,plain,(
    ! [A_16] : k6_relat_1(A_16) = k6_partfun1(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_6,plain,(
    ! [A_6] :
      ( k5_relat_1(k2_funct_1(A_6),A_6) = k6_relat_1(k2_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_175,plain,(
    ! [A_51] :
      ( k5_relat_1(k2_funct_1(A_51),A_51) = k6_partfun1(k2_relat_1(A_51))
      | ~ v2_funct_1(A_51)
      | ~ v1_funct_1(A_51)
      | ~ v1_relat_1(A_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_76,plain,(
    ! [A_26,B_27,C_28] :
      ( k1_relset_1(A_26,B_27,C_28) = k1_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_80,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_36,c_76])).

tff(c_118,plain,(
    ! [B_40,A_41,C_42] :
      ( k1_xboole_0 = B_40
      | k1_relset_1(A_41,B_40,C_42) = A_41
      | ~ v1_funct_2(C_42,A_41,B_40)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_41,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_121,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_118])).

tff(c_124,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_80,c_121])).

tff(c_125,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_124])).

tff(c_8,plain,(
    ! [A_6] :
      ( k5_relat_1(A_6,k2_funct_1(A_6)) = k6_relat_1(k1_relat_1(A_6))
      | ~ v2_funct_1(A_6)
      | ~ v1_funct_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_85,plain,(
    ! [A_29] :
      ( k5_relat_1(A_29,k2_funct_1(A_29)) = k6_partfun1(k1_relat_1(A_29))
      | ~ v2_funct_1(A_29)
      | ~ v1_funct_1(A_29)
      | ~ v1_relat_1(A_29) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_8])).

tff(c_28,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2')
    | k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_64,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_91,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_64])).

tff(c_97,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_40,c_32,c_91])).

tff(c_129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_125,c_97])).

tff(c_130,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_181,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_130])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_63,c_40,c_32,c_141,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:07:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.31/1.47  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.48  
% 2.31/1.48  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.31/1.48  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.31/1.48  
% 2.31/1.48  %Foreground sorts:
% 2.31/1.48  
% 2.31/1.48  
% 2.31/1.48  %Background operators:
% 2.31/1.48  
% 2.31/1.48  
% 2.31/1.48  %Foreground operators:
% 2.31/1.48  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.31/1.48  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.31/1.48  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.31/1.48  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.31/1.48  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.31/1.48  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.31/1.48  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.31/1.48  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.31/1.48  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.31/1.48  tff('#skF_2', type, '#skF_2': $i).
% 2.31/1.48  tff('#skF_3', type, '#skF_3': $i).
% 2.31/1.48  tff('#skF_1', type, '#skF_1': $i).
% 2.31/1.48  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.31/1.48  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.31/1.48  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.31/1.48  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.31/1.48  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.31/1.48  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.31/1.48  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.31/1.48  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.31/1.48  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.31/1.48  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.31/1.48  
% 2.37/1.50  tff(f_34, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.37/1.50  tff(f_89, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_funct_2)).
% 2.37/1.50  tff(f_32, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.37/1.50  tff(f_52, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.37/1.50  tff(f_72, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.37/1.50  tff(f_44, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 2.37/1.50  tff(f_48, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.37/1.50  tff(f_70, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 2.37/1.50  tff(c_4, plain, (![A_4, B_5]: (v1_relat_1(k2_zfmisc_1(A_4, B_5)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.37/1.50  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.50  tff(c_57, plain, (![B_20, A_21]: (v1_relat_1(B_20) | ~m1_subset_1(B_20, k1_zfmisc_1(A_21)) | ~v1_relat_1(A_21))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.37/1.50  tff(c_60, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_57])).
% 2.37/1.50  tff(c_63, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_60])).
% 2.37/1.50  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.50  tff(c_32, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.50  tff(c_34, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.50  tff(c_136, plain, (![A_43, B_44, C_45]: (k2_relset_1(A_43, B_44, C_45)=k2_relat_1(C_45) | ~m1_subset_1(C_45, k1_zfmisc_1(k2_zfmisc_1(A_43, B_44))))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.37/1.50  tff(c_139, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_136])).
% 2.37/1.50  tff(c_141, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_139])).
% 2.37/1.50  tff(c_26, plain, (![A_16]: (k6_relat_1(A_16)=k6_partfun1(A_16))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.37/1.50  tff(c_6, plain, (![A_6]: (k5_relat_1(k2_funct_1(A_6), A_6)=k6_relat_1(k2_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.37/1.50  tff(c_175, plain, (![A_51]: (k5_relat_1(k2_funct_1(A_51), A_51)=k6_partfun1(k2_relat_1(A_51)) | ~v2_funct_1(A_51) | ~v1_funct_1(A_51) | ~v1_relat_1(A_51))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6])).
% 2.37/1.50  tff(c_30, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.50  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.50  tff(c_76, plain, (![A_26, B_27, C_28]: (k1_relset_1(A_26, B_27, C_28)=k1_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.37/1.50  tff(c_80, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_36, c_76])).
% 2.37/1.50  tff(c_118, plain, (![B_40, A_41, C_42]: (k1_xboole_0=B_40 | k1_relset_1(A_41, B_40, C_42)=A_41 | ~v1_funct_2(C_42, A_41, B_40) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_41, B_40))))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.37/1.50  tff(c_121, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_36, c_118])).
% 2.37/1.50  tff(c_124, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_38, c_80, c_121])).
% 2.37/1.50  tff(c_125, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_30, c_124])).
% 2.37/1.50  tff(c_8, plain, (![A_6]: (k5_relat_1(A_6, k2_funct_1(A_6))=k6_relat_1(k1_relat_1(A_6)) | ~v2_funct_1(A_6) | ~v1_funct_1(A_6) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.37/1.50  tff(c_85, plain, (![A_29]: (k5_relat_1(A_29, k2_funct_1(A_29))=k6_partfun1(k1_relat_1(A_29)) | ~v2_funct_1(A_29) | ~v1_funct_1(A_29) | ~v1_relat_1(A_29))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_8])).
% 2.37/1.50  tff(c_28, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2') | k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.37/1.50  tff(c_64, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_28])).
% 2.37/1.50  tff(c_91, plain, (k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85, c_64])).
% 2.37/1.50  tff(c_97, plain, (k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_63, c_40, c_32, c_91])).
% 2.37/1.50  tff(c_129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_125, c_97])).
% 2.37/1.50  tff(c_130, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_28])).
% 2.37/1.50  tff(c_181, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_130])).
% 2.37/1.50  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_63, c_40, c_32, c_141, c_181])).
% 2.37/1.50  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.37/1.50  
% 2.37/1.50  Inference rules
% 2.37/1.50  ----------------------
% 2.37/1.50  #Ref     : 0
% 2.37/1.50  #Sup     : 33
% 2.37/1.50  #Fact    : 0
% 2.37/1.50  #Define  : 0
% 2.37/1.50  #Split   : 1
% 2.37/1.50  #Chain   : 0
% 2.37/1.50  #Close   : 0
% 2.37/1.50  
% 2.37/1.50  Ordering : KBO
% 2.37/1.50  
% 2.37/1.50  Simplification rules
% 2.37/1.50  ----------------------
% 2.37/1.50  #Subsume      : 0
% 2.37/1.50  #Demod        : 24
% 2.37/1.50  #Tautology    : 22
% 2.37/1.50  #SimpNegUnit  : 2
% 2.37/1.50  #BackRed      : 2
% 2.37/1.50  
% 2.37/1.50  #Partial instantiations: 0
% 2.37/1.50  #Strategies tried      : 1
% 2.37/1.50  
% 2.37/1.50  Timing (in seconds)
% 2.37/1.50  ----------------------
% 2.37/1.50  Preprocessing        : 0.41
% 2.37/1.50  Parsing              : 0.22
% 2.37/1.50  CNF conversion       : 0.02
% 2.37/1.50  Main loop            : 0.19
% 2.37/1.50  Inferencing          : 0.07
% 2.37/1.50  Reduction            : 0.06
% 2.37/1.50  Demodulation         : 0.05
% 2.37/1.50  BG Simplification    : 0.02
% 2.37/1.50  Subsumption          : 0.03
% 2.37/1.50  Abstraction          : 0.01
% 2.37/1.50  MUC search           : 0.00
% 2.37/1.50  Cooper               : 0.00
% 2.37/1.50  Total                : 0.64
% 2.37/1.50  Index Insertion      : 0.00
% 2.37/1.50  Index Deletion       : 0.00
% 2.37/1.50  Index Matching       : 0.00
% 2.37/1.50  BG Taut test         : 0.00
%------------------------------------------------------------------------------
