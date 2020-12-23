%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:55 EST 2020

% Result     : Theorem 2.03s
% Output     : CNFRefutation 2.03s
% Verified   : 
% Statistics : Number of formulae       :   59 (  85 expanded)
%              Number of leaves         :   29 (  45 expanded)
%              Depth                    :    5
%              Number of atoms          :   87 ( 211 expanded)
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

tff(f_84,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( k2_relset_1(A,B,C) = B
            & v2_funct_1(C) )
         => ( B = k1_xboole_0
            | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
              & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_67,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_35,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_65,axiom,(
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

tff(c_34,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    ! [C_16,A_17,B_18] :
      ( v1_relat_1(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_58,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_54])).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_30,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_32,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_131,plain,(
    ! [A_40,B_41,C_42] :
      ( k2_relset_1(A_40,B_41,C_42) = k2_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_134,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_131])).

tff(c_136,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_134])).

tff(c_24,plain,(
    ! [A_14] : k6_relat_1(A_14) = k6_partfun1(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2,plain,(
    ! [A_1] :
      ( k5_relat_1(k2_funct_1(A_1),A_1) = k6_relat_1(k2_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_175,plain,(
    ! [A_48] :
      ( k5_relat_1(k2_funct_1(A_48),A_48) = k6_partfun1(k2_relat_1(A_48))
      | ~ v2_funct_1(A_48)
      | ~ v1_funct_1(A_48)
      | ~ v1_relat_1(A_48) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_2])).

tff(c_28,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_70,plain,(
    ! [A_22,B_23,C_24] :
      ( k1_relset_1(A_22,B_23,C_24) = k1_relat_1(C_24)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_34,c_70])).

tff(c_113,plain,(
    ! [B_37,A_38,C_39] :
      ( k1_xboole_0 = B_37
      | k1_relset_1(A_38,B_37,C_39) = A_38
      | ~ v1_funct_2(C_39,A_38,B_37)
      | ~ m1_subset_1(C_39,k1_zfmisc_1(k2_zfmisc_1(A_38,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_113])).

tff(c_119,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_74,c_116])).

tff(c_120,plain,(
    k1_relat_1('#skF_3') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_119])).

tff(c_4,plain,(
    ! [A_1] :
      ( k5_relat_1(A_1,k2_funct_1(A_1)) = k6_relat_1(k1_relat_1(A_1))
      | ~ v2_funct_1(A_1)
      | ~ v1_funct_1(A_1)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_89,plain,(
    ! [A_27] :
      ( k5_relat_1(A_27,k2_funct_1(A_27)) = k6_partfun1(k1_relat_1(A_27))
      | ~ v2_funct_1(A_27)
      | ~ v1_funct_1(A_27)
      | ~ v1_relat_1(A_27) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_4])).

tff(c_26,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2')
    | k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_59,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) != k6_partfun1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_95,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_59])).

tff(c_101,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) != k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_38,c_30,c_95])).

tff(c_124,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_120,c_101])).

tff(c_125,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),'#skF_3') != k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_181,plain,
    ( k6_partfun1(k2_relat_1('#skF_3')) != k6_partfun1('#skF_2')
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_125])).

tff(c_188,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_38,c_30,c_136,c_181])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n013.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 17:31:54 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.03/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.20  
% 2.03/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.20  %$ v1_funct_2 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.03/1.20  
% 2.03/1.20  %Foreground sorts:
% 2.03/1.20  
% 2.03/1.20  
% 2.03/1.20  %Background operators:
% 2.03/1.20  
% 2.03/1.20  
% 2.03/1.20  %Foreground operators:
% 2.03/1.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.03/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.03/1.20  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 2.03/1.20  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 2.03/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.03/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.03/1.20  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 2.03/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.03/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.03/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.03/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.03/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.03/1.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.03/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.03/1.20  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 2.03/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.03/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.03/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.03/1.20  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 2.03/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.03/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.03/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.03/1.20  
% 2.03/1.22  tff(f_84, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 2.03/1.22  tff(f_39, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 2.03/1.22  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 2.03/1.22  tff(f_67, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 2.03/1.22  tff(f_35, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 2.03/1.22  tff(f_43, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.03/1.22  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.03/1.22  tff(c_34, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.03/1.22  tff(c_54, plain, (![C_16, A_17, B_18]: (v1_relat_1(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.03/1.22  tff(c_58, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_54])).
% 2.03/1.22  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.03/1.22  tff(c_30, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.03/1.22  tff(c_32, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.03/1.22  tff(c_131, plain, (![A_40, B_41, C_42]: (k2_relset_1(A_40, B_41, C_42)=k2_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.03/1.22  tff(c_134, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_131])).
% 2.03/1.22  tff(c_136, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_134])).
% 2.03/1.22  tff(c_24, plain, (![A_14]: (k6_relat_1(A_14)=k6_partfun1(A_14))), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.03/1.22  tff(c_2, plain, (![A_1]: (k5_relat_1(k2_funct_1(A_1), A_1)=k6_relat_1(k2_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.22  tff(c_175, plain, (![A_48]: (k5_relat_1(k2_funct_1(A_48), A_48)=k6_partfun1(k2_relat_1(A_48)) | ~v2_funct_1(A_48) | ~v1_funct_1(A_48) | ~v1_relat_1(A_48))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_2])).
% 2.03/1.22  tff(c_28, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.03/1.22  tff(c_36, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.03/1.22  tff(c_70, plain, (![A_22, B_23, C_24]: (k1_relset_1(A_22, B_23, C_24)=k1_relat_1(C_24) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.03/1.22  tff(c_74, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_34, c_70])).
% 2.03/1.22  tff(c_113, plain, (![B_37, A_38, C_39]: (k1_xboole_0=B_37 | k1_relset_1(A_38, B_37, C_39)=A_38 | ~v1_funct_2(C_39, A_38, B_37) | ~m1_subset_1(C_39, k1_zfmisc_1(k2_zfmisc_1(A_38, B_37))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.03/1.22  tff(c_116, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_34, c_113])).
% 2.03/1.22  tff(c_119, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_36, c_74, c_116])).
% 2.03/1.22  tff(c_120, plain, (k1_relat_1('#skF_3')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_28, c_119])).
% 2.03/1.22  tff(c_4, plain, (![A_1]: (k5_relat_1(A_1, k2_funct_1(A_1))=k6_relat_1(k1_relat_1(A_1)) | ~v2_funct_1(A_1) | ~v1_funct_1(A_1) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.03/1.22  tff(c_89, plain, (![A_27]: (k5_relat_1(A_27, k2_funct_1(A_27))=k6_partfun1(k1_relat_1(A_27)) | ~v2_funct_1(A_27) | ~v1_funct_1(A_27) | ~v1_relat_1(A_27))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_4])).
% 2.03/1.22  tff(c_26, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2') | k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.03/1.22  tff(c_59, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))!=k6_partfun1('#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.03/1.22  tff(c_95, plain, (k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_89, c_59])).
% 2.03/1.22  tff(c_101, plain, (k6_partfun1(k1_relat_1('#skF_3'))!=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_58, c_38, c_30, c_95])).
% 2.03/1.22  tff(c_124, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_120, c_101])).
% 2.03/1.22  tff(c_125, plain, (k5_relat_1(k2_funct_1('#skF_3'), '#skF_3')!=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_26])).
% 2.03/1.22  tff(c_181, plain, (k6_partfun1(k2_relat_1('#skF_3'))!=k6_partfun1('#skF_2') | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_125])).
% 2.03/1.22  tff(c_188, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_38, c_30, c_136, c_181])).
% 2.03/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.03/1.22  
% 2.03/1.22  Inference rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Ref     : 0
% 2.03/1.22  #Sup     : 35
% 2.03/1.22  #Fact    : 0
% 2.03/1.22  #Define  : 0
% 2.03/1.22  #Split   : 1
% 2.03/1.22  #Chain   : 0
% 2.03/1.22  #Close   : 0
% 2.03/1.22  
% 2.03/1.22  Ordering : KBO
% 2.03/1.22  
% 2.03/1.22  Simplification rules
% 2.03/1.22  ----------------------
% 2.03/1.22  #Subsume      : 0
% 2.03/1.22  #Demod        : 24
% 2.03/1.22  #Tautology    : 25
% 2.03/1.22  #SimpNegUnit  : 2
% 2.03/1.22  #BackRed      : 2
% 2.03/1.22  
% 2.03/1.22  #Partial instantiations: 0
% 2.03/1.22  #Strategies tried      : 1
% 2.03/1.22  
% 2.03/1.22  Timing (in seconds)
% 2.03/1.22  ----------------------
% 2.03/1.22  Preprocessing        : 0.31
% 2.03/1.22  Parsing              : 0.17
% 2.03/1.22  CNF conversion       : 0.02
% 2.03/1.22  Main loop            : 0.16
% 2.03/1.22  Inferencing          : 0.06
% 2.03/1.22  Reduction            : 0.05
% 2.03/1.22  Demodulation         : 0.04
% 2.03/1.22  BG Simplification    : 0.01
% 2.03/1.22  Subsumption          : 0.02
% 2.03/1.22  Abstraction          : 0.01
% 2.03/1.22  MUC search           : 0.00
% 2.03/1.22  Cooper               : 0.00
% 2.03/1.22  Total                : 0.50
% 2.03/1.22  Index Insertion      : 0.00
% 2.03/1.22  Index Deletion       : 0.00
% 2.03/1.22  Index Matching       : 0.00
% 2.03/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
