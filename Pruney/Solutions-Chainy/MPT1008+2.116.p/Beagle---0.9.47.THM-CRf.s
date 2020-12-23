%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:14:42 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   65 ( 155 expanded)
%              Number of leaves         :   33 (  71 expanded)
%              Depth                    :   13
%              Number of atoms          :   92 ( 363 expanded)
%              Number of equality atoms :   45 ( 170 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_40,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_102,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,k1_tarski(A),B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A),B))) )
       => ( B != k1_xboole_0
         => k2_relset_1(k1_tarski(A),B,C) = k1_tarski(k1_funct_1(C,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_2)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_78,axiom,(
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

tff(f_52,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( k1_relat_1(B) = k1_tarski(A)
       => k2_relat_1(B) = k1_tarski(k1_funct_1(B,A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_funct_1)).

tff(f_44,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k9_relat_1(A,k1_relat_1(A)) = k2_relat_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

tff(f_60,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_90,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( B = k1_xboole_0
         => A = k1_xboole_0 )
       => k7_relset_1(A,B,C,A) = k2_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_funct_2)).

tff(c_10,plain,(
    ! [A_10,B_11] : v1_relat_1(k2_zfmisc_1(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_40,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_64,plain,(
    ! [B_33,A_34] :
      ( v1_relat_1(B_33)
      | ~ m1_subset_1(B_33,k1_zfmisc_1(A_34))
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_67,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_70,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_67])).

tff(c_44,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_42,plain,(
    v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_90,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_94,plain,(
    k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_40,c_90])).

tff(c_124,plain,(
    ! [B_56,A_57,C_58] :
      ( k1_xboole_0 = B_56
      | k1_relset_1(A_57,B_56,C_58) = A_57
      | ~ v1_funct_2(C_58,A_57,B_56)
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_127,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') = k1_tarski('#skF_1')
    | ~ v1_funct_2('#skF_3',k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_40,c_124])).

tff(c_130,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_94,c_127])).

tff(c_131,plain,(
    k1_tarski('#skF_1') = k1_relat_1('#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_130])).

tff(c_14,plain,(
    ! [B_14,A_13] :
      ( k1_tarski(k1_funct_1(B_14,A_13)) = k2_relat_1(B_14)
      | k1_tarski(A_13) != k1_relat_1(B_14)
      | ~ v1_funct_1(B_14)
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [A_12] :
      ( k9_relat_1(A_12,k1_relat_1(A_12)) = k2_relat_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_136,plain,(
    v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_42])).

tff(c_109,plain,(
    ! [A_47,B_48,C_49,D_50] :
      ( k7_relset_1(A_47,B_48,C_49,D_50) = k9_relat_1(C_49,D_50)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_47,B_48))) ) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_112,plain,(
    ! [D_50] : k7_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3',D_50) = k9_relat_1('#skF_3',D_50) ),
    inference(resolution,[status(thm)],[c_40,c_109])).

tff(c_132,plain,(
    ! [D_50] : k7_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3',D_50) = k9_relat_1('#skF_3',D_50) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_112])).

tff(c_135,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'),'#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_40])).

tff(c_185,plain,(
    ! [B_65,A_66,C_67] :
      ( k1_xboole_0 = B_65
      | k7_relset_1(A_66,B_65,C_67,A_66) = k2_relset_1(A_66,B_65,C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_66,B_65)))
      | ~ v1_funct_2(C_67,A_66,B_65)
      | ~ v1_funct_1(C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_187,plain,
    ( k1_xboole_0 = '#skF_2'
    | k7_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3',k1_relat_1('#skF_3')) = k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3')
    | ~ v1_funct_2('#skF_3',k1_relat_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_135,c_185])).

tff(c_190,plain,
    ( k1_xboole_0 = '#skF_2'
    | k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_136,c_132,c_187])).

tff(c_191,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') = k9_relat_1('#skF_3',k1_relat_1('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_190])).

tff(c_36,plain,(
    k2_relset_1(k1_tarski('#skF_1'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_134,plain,(
    k2_relset_1(k1_relat_1('#skF_3'),'#skF_2','#skF_3') != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_36])).

tff(c_192,plain,(
    k9_relat_1('#skF_3',k1_relat_1('#skF_3')) != k1_tarski(k1_funct_1('#skF_3','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_191,c_134])).

tff(c_199,plain,
    ( k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_192])).

tff(c_201,plain,(
    k1_tarski(k1_funct_1('#skF_3','#skF_1')) != k2_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_199])).

tff(c_204,plain,
    ( k1_tarski('#skF_1') != k1_relat_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_201])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_44,c_131,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:17:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.20  
% 2.07/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.20  %$ v1_funct_2 > m1_subset_1 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_enumset1 > k2_relset_1 > k1_relset_1 > k1_enumset1 > k9_relat_1 > k2_zfmisc_1 > k2_tarski > k1_funct_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_tarski > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.07/1.20  
% 2.07/1.20  %Foreground sorts:
% 2.07/1.20  
% 2.07/1.20  
% 2.07/1.20  %Background operators:
% 2.07/1.20  
% 2.07/1.20  
% 2.07/1.20  %Foreground operators:
% 2.07/1.20  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 2.07/1.20  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.07/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.20  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.07/1.20  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 2.07/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.20  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.07/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.20  tff('#skF_2', type, '#skF_2': $i).
% 2.07/1.20  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 2.07/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.20  tff('#skF_1', type, '#skF_1': $i).
% 2.07/1.20  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.07/1.20  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.07/1.20  tff(k1_funct_1, type, k1_funct_1: ($i * $i) > $i).
% 2.07/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.20  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.07/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.20  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.07/1.20  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.07/1.20  
% 2.17/1.22  tff(f_40, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 2.17/1.22  tff(f_102, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, k1_tarski(A), B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(k1_tarski(A), B)))) => (~(B = k1_xboole_0) => (k2_relset_1(k1_tarski(A), B, C) = k1_tarski(k1_funct_1(C, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t62_funct_2)).
% 2.17/1.22  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 2.17/1.22  tff(f_56, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 2.17/1.22  tff(f_78, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.17/1.22  tff(f_52, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((k1_relat_1(B) = k1_tarski(A)) => (k2_relat_1(B) = k1_tarski(k1_funct_1(B, A)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_funct_1)).
% 2.17/1.22  tff(f_44, axiom, (![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_relat_1(A)) = k2_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t146_relat_1)).
% 2.17/1.22  tff(f_60, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 2.17/1.22  tff(f_90, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((B = k1_xboole_0) => (A = k1_xboole_0)) => (k7_relset_1(A, B, C, A) = k2_relset_1(A, B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_funct_2)).
% 2.17/1.22  tff(c_10, plain, (![A_10, B_11]: (v1_relat_1(k2_zfmisc_1(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.17/1.22  tff(c_40, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.17/1.22  tff(c_64, plain, (![B_33, A_34]: (v1_relat_1(B_33) | ~m1_subset_1(B_33, k1_zfmisc_1(A_34)) | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.17/1.22  tff(c_67, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_40, c_64])).
% 2.17/1.22  tff(c_70, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_67])).
% 2.17/1.22  tff(c_44, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.17/1.22  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.17/1.22  tff(c_42, plain, (v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.17/1.22  tff(c_90, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.17/1.22  tff(c_94, plain, (k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_40, c_90])).
% 2.17/1.22  tff(c_124, plain, (![B_56, A_57, C_58]: (k1_xboole_0=B_56 | k1_relset_1(A_57, B_56, C_58)=A_57 | ~v1_funct_2(C_58, A_57, B_56) | ~m1_subset_1(C_58, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.17/1.22  tff(c_127, plain, (k1_xboole_0='#skF_2' | k1_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')=k1_tarski('#skF_1') | ~v1_funct_2('#skF_3', k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_40, c_124])).
% 2.17/1.22  tff(c_130, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_94, c_127])).
% 2.17/1.22  tff(c_131, plain, (k1_tarski('#skF_1')=k1_relat_1('#skF_3')), inference(negUnitSimplification, [status(thm)], [c_38, c_130])).
% 2.17/1.22  tff(c_14, plain, (![B_14, A_13]: (k1_tarski(k1_funct_1(B_14, A_13))=k2_relat_1(B_14) | k1_tarski(A_13)!=k1_relat_1(B_14) | ~v1_funct_1(B_14) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.17/1.22  tff(c_12, plain, (![A_12]: (k9_relat_1(A_12, k1_relat_1(A_12))=k2_relat_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.17/1.22  tff(c_136, plain, (v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_42])).
% 2.17/1.22  tff(c_109, plain, (![A_47, B_48, C_49, D_50]: (k7_relset_1(A_47, B_48, C_49, D_50)=k9_relat_1(C_49, D_50) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_47, B_48))))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.17/1.22  tff(c_112, plain, (![D_50]: (k7_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3', D_50)=k9_relat_1('#skF_3', D_50))), inference(resolution, [status(thm)], [c_40, c_109])).
% 2.17/1.22  tff(c_132, plain, (![D_50]: (k7_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', D_50)=k9_relat_1('#skF_3', D_50))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_112])).
% 2.17/1.22  tff(c_135, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_3'), '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_40])).
% 2.17/1.22  tff(c_185, plain, (![B_65, A_66, C_67]: (k1_xboole_0=B_65 | k7_relset_1(A_66, B_65, C_67, A_66)=k2_relset_1(A_66, B_65, C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_66, B_65))) | ~v1_funct_2(C_67, A_66, B_65) | ~v1_funct_1(C_67))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.17/1.22  tff(c_187, plain, (k1_xboole_0='#skF_2' | k7_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3', k1_relat_1('#skF_3'))=k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3') | ~v1_funct_2('#skF_3', k1_relat_1('#skF_3'), '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_135, c_185])).
% 2.17/1.22  tff(c_190, plain, (k1_xboole_0='#skF_2' | k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_136, c_132, c_187])).
% 2.17/1.22  tff(c_191, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')=k9_relat_1('#skF_3', k1_relat_1('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_38, c_190])).
% 2.17/1.22  tff(c_36, plain, (k2_relset_1(k1_tarski('#skF_1'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(cnfTransformation, [status(thm)], [f_102])).
% 2.17/1.22  tff(c_134, plain, (k2_relset_1(k1_relat_1('#skF_3'), '#skF_2', '#skF_3')!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_131, c_36])).
% 2.17/1.22  tff(c_192, plain, (k9_relat_1('#skF_3', k1_relat_1('#skF_3'))!=k1_tarski(k1_funct_1('#skF_3', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_191, c_134])).
% 2.17/1.22  tff(c_199, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12, c_192])).
% 2.17/1.22  tff(c_201, plain, (k1_tarski(k1_funct_1('#skF_3', '#skF_1'))!=k2_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_199])).
% 2.17/1.22  tff(c_204, plain, (k1_tarski('#skF_1')!=k1_relat_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_14, c_201])).
% 2.17/1.22  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_44, c_131, c_204])).
% 2.17/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.22  
% 2.17/1.22  Inference rules
% 2.17/1.22  ----------------------
% 2.17/1.22  #Ref     : 0
% 2.17/1.22  #Sup     : 34
% 2.17/1.22  #Fact    : 0
% 2.17/1.22  #Define  : 0
% 2.17/1.22  #Split   : 0
% 2.17/1.22  #Chain   : 0
% 2.17/1.22  #Close   : 0
% 2.17/1.22  
% 2.17/1.22  Ordering : KBO
% 2.17/1.22  
% 2.17/1.22  Simplification rules
% 2.17/1.22  ----------------------
% 2.17/1.22  #Subsume      : 0
% 2.17/1.22  #Demod        : 24
% 2.17/1.22  #Tautology    : 27
% 2.17/1.22  #SimpNegUnit  : 4
% 2.17/1.22  #BackRed      : 6
% 2.17/1.22  
% 2.17/1.22  #Partial instantiations: 0
% 2.17/1.22  #Strategies tried      : 1
% 2.17/1.22  
% 2.17/1.22  Timing (in seconds)
% 2.17/1.22  ----------------------
% 2.17/1.22  Preprocessing        : 0.34
% 2.17/1.22  Parsing              : 0.18
% 2.17/1.22  CNF conversion       : 0.02
% 2.17/1.22  Main loop            : 0.17
% 2.17/1.22  Inferencing          : 0.06
% 2.17/1.22  Reduction            : 0.05
% 2.17/1.22  Demodulation         : 0.04
% 2.17/1.22  BG Simplification    : 0.01
% 2.17/1.22  Subsumption          : 0.02
% 2.17/1.22  Abstraction          : 0.01
% 2.17/1.22  MUC search           : 0.00
% 2.17/1.22  Cooper               : 0.00
% 2.17/1.22  Total                : 0.53
% 2.17/1.22  Index Insertion      : 0.00
% 2.17/1.22  Index Deletion       : 0.00
% 2.17/1.22  Index Matching       : 0.00
% 2.17/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------
