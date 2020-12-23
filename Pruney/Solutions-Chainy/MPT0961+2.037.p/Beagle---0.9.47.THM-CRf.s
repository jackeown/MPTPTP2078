%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:46 EST 2020

% Result     : Theorem 6.47s
% Output     : CNFRefutation 6.47s
% Verified   : 
% Statistics : Number of formulae       :   94 (1022 expanded)
%              Number of leaves         :   24 ( 348 expanded)
%              Depth                    :   14
%              Number of atoms          :  167 (2737 expanded)
%              Number of equality atoms :   48 (1074 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

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

tff(f_90,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_41,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k1_relset_1(A,B,C),k1_zfmisc_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_relset_1)).

tff(f_35,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_42,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5662,plain,(
    ! [C_309,A_310,B_311] :
      ( m1_subset_1(C_309,k1_zfmisc_1(k2_zfmisc_1(A_310,B_311)))
      | ~ r1_tarski(k2_relat_1(C_309),B_311)
      | ~ r1_tarski(k1_relat_1(C_309),A_310)
      | ~ v1_relat_1(C_309) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_26,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_17,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_47,plain,(
    ! [A_17] :
      ( v1_funct_2(k1_xboole_0,A_17,k1_xboole_0)
      | k1_xboole_0 = A_17
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_105,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_47])).

tff(c_108,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_105])).

tff(c_112,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_108])).

tff(c_114,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_47])).

tff(c_121,plain,(
    ! [A_33,B_34,C_35] :
      ( k1_relset_1(A_33,B_34,C_35) = k1_relat_1(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1(k2_zfmisc_1(A_33,B_34))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_133,plain,(
    ! [A_36,C_37] :
      ( k1_relset_1(A_36,k1_xboole_0,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_121])).

tff(c_139,plain,(
    ! [A_36] : k1_relset_1(A_36,k1_xboole_0,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_114,c_133])).

tff(c_148,plain,(
    ! [A_39,B_40,C_41] :
      ( m1_subset_1(k1_relset_1(A_39,B_40,C_41),k1_zfmisc_1(A_39))
      | ~ m1_subset_1(C_41,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40))) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_161,plain,(
    ! [A_36] :
      ( m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_36))
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_148])).

tff(c_168,plain,(
    ! [A_42] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_42)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_12,c_161])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_182,plain,(
    ! [A_43] : r1_tarski(k1_relat_1(k1_xboole_0),A_43) ),
    inference(resolution,[status(thm)],[c_168,c_16])).

tff(c_8,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_182,c_8])).

tff(c_181,plain,(
    ! [A_42] : r1_tarski(k1_relat_1(k1_xboole_0),A_42) ),
    inference(resolution,[status(thm)],[c_168,c_16])).

tff(c_191,plain,(
    ! [A_42] : r1_tarski(k1_xboole_0,A_42) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_181])).

tff(c_259,plain,(
    ! [C_51,A_52,B_53] :
      ( m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_53)))
      | ~ r1_tarski(k2_relat_1(C_51),B_53)
      | ~ r1_tarski(k1_relat_1(C_51),A_52)
      | ~ v1_relat_1(C_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_820,plain,(
    ! [C_113,A_114,B_115] :
      ( r1_tarski(C_113,k2_zfmisc_1(A_114,B_115))
      | ~ r1_tarski(k2_relat_1(C_113),B_115)
      | ~ r1_tarski(k1_relat_1(C_113),A_114)
      | ~ v1_relat_1(C_113) ) ),
    inference(resolution,[status(thm)],[c_259,c_16])).

tff(c_825,plain,(
    ! [C_116,A_117] :
      ( r1_tarski(C_116,k2_zfmisc_1(A_117,k2_relat_1(C_116)))
      | ~ r1_tarski(k1_relat_1(C_116),A_117)
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_6,c_820])).

tff(c_132,plain,(
    ! [A_33,B_34,A_6] :
      ( k1_relset_1(A_33,B_34,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_33,B_34)) ) ),
    inference(resolution,[status(thm)],[c_18,c_121])).

tff(c_984,plain,(
    ! [A_126,C_127] :
      ( k1_relset_1(A_126,k2_relat_1(C_127),C_127) = k1_relat_1(C_127)
      | ~ r1_tarski(k1_relat_1(C_127),A_126)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_825,c_132])).

tff(c_999,plain,(
    ! [C_127] :
      ( k1_relset_1(k1_relat_1(C_127),k2_relat_1(C_127),C_127) = k1_relat_1(C_127)
      | ~ v1_relat_1(C_127) ) ),
    inference(resolution,[status(thm)],[c_6,c_984])).

tff(c_24,plain,(
    ! [C_16,A_14,B_15] :
      ( m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_14,B_15)))
      | ~ r1_tarski(k2_relat_1(C_16),B_15)
      | ~ r1_tarski(k1_relat_1(C_16),A_14)
      | ~ v1_relat_1(C_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_356,plain,(
    ! [B_66,C_67,A_68] :
      ( k1_xboole_0 = B_66
      | v1_funct_2(C_67,A_68,B_66)
      | k1_relset_1(A_68,B_66,C_67) != A_68
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_2023,plain,(
    ! [B_186,C_187,A_188] :
      ( k1_xboole_0 = B_186
      | v1_funct_2(C_187,A_188,B_186)
      | k1_relset_1(A_188,B_186,C_187) != A_188
      | ~ r1_tarski(k2_relat_1(C_187),B_186)
      | ~ r1_tarski(k1_relat_1(C_187),A_188)
      | ~ v1_relat_1(C_187) ) ),
    inference(resolution,[status(thm)],[c_24,c_356])).

tff(c_4964,plain,(
    ! [C_274,A_275] :
      ( k2_relat_1(C_274) = k1_xboole_0
      | v1_funct_2(C_274,A_275,k2_relat_1(C_274))
      | k1_relset_1(A_275,k2_relat_1(C_274),C_274) != A_275
      | ~ r1_tarski(k1_relat_1(C_274),A_275)
      | ~ v1_relat_1(C_274) ) ),
    inference(resolution,[status(thm)],[c_6,c_2023])).

tff(c_40,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38])).

tff(c_97,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_4973,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_4964,c_97])).

tff(c_4982,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_4973])).

tff(c_4983,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_4982])).

tff(c_4986,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_999,c_4983])).

tff(c_4990,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4986])).

tff(c_4991,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_4982])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_840,plain,(
    ! [A_117,C_116] :
      ( k2_zfmisc_1(A_117,k2_relat_1(C_116)) = C_116
      | ~ r1_tarski(k2_zfmisc_1(A_117,k2_relat_1(C_116)),C_116)
      | ~ r1_tarski(k1_relat_1(C_116),A_117)
      | ~ v1_relat_1(C_116) ) ),
    inference(resolution,[status(thm)],[c_825,c_2])).

tff(c_5000,plain,(
    ! [A_117] :
      ( k2_zfmisc_1(A_117,k2_relat_1('#skF_1')) = '#skF_1'
      | ~ r1_tarski(k2_zfmisc_1(A_117,k1_xboole_0),'#skF_1')
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_117)
      | ~ v1_relat_1('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4991,c_840])).

tff(c_5023,plain,(
    ! [A_117] :
      ( k1_xboole_0 = '#skF_1'
      | ~ r1_tarski(k1_relat_1('#skF_1'),A_117) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_191,c_12,c_12,c_4991,c_5000])).

tff(c_5040,plain,(
    ! [A_276] : ~ r1_tarski(k1_relat_1('#skF_1'),A_276) ),
    inference(splitLeft,[status(thm)],[c_5023])).

tff(c_5050,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_5040])).

tff(c_5051,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5023])).

tff(c_167,plain,(
    ! [A_36] : m1_subset_1(k1_relat_1(k1_xboole_0),k1_zfmisc_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_12,c_161])).

tff(c_209,plain,(
    ! [A_45] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_45)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_167])).

tff(c_22,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_relset_1(A_11,B_12,C_13) = k1_relat_1(C_13)
      | ~ m1_subset_1(C_13,k1_zfmisc_1(k2_zfmisc_1(A_11,B_12))) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_216,plain,(
    ! [A_11,B_12] : k1_relset_1(A_11,B_12,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_209,c_22])).

tff(c_223,plain,(
    ! [A_11,B_12] : k1_relset_1(A_11,B_12,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_216])).

tff(c_192,plain,(
    ! [A_36] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_36)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_167])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_30,plain,(
    ! [C_19,B_18] :
      ( v1_funct_2(C_19,k1_xboole_0,B_18)
      | k1_relset_1(k1_xboole_0,B_18,C_19) != k1_xboole_0
      | ~ m1_subset_1(C_19,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_303,plain,(
    ! [C_58,B_59] :
      ( v1_funct_2(C_58,k1_xboole_0,B_59)
      | k1_relset_1(k1_xboole_0,B_59,C_58) != k1_xboole_0
      | ~ m1_subset_1(C_58,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_306,plain,(
    ! [B_59] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_59)
      | k1_relset_1(k1_xboole_0,B_59,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_192,c_303])).

tff(c_315,plain,(
    ! [B_59] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_306])).

tff(c_5112,plain,(
    ! [B_59] : v1_funct_2('#skF_1','#skF_1',B_59) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_5051,c_315])).

tff(c_5120,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_5051,c_190])).

tff(c_4993,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4991,c_97])).

tff(c_5052,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5051,c_4993])).

tff(c_5443,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5120,c_5052])).

tff(c_5494,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5112,c_5443])).

tff(c_5495,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_5668,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ r1_tarski(k1_relat_1('#skF_1'),k1_relat_1('#skF_1'))
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_5662,c_5495])).

tff(c_5682,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_6,c_6,c_5668])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:39:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.47/2.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.34  
% 6.47/2.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.34  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 6.47/2.34  
% 6.47/2.34  %Foreground sorts:
% 6.47/2.34  
% 6.47/2.34  
% 6.47/2.34  %Background operators:
% 6.47/2.34  
% 6.47/2.34  
% 6.47/2.34  %Foreground operators:
% 6.47/2.34  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.47/2.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.47/2.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.47/2.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.47/2.34  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.47/2.34  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.47/2.34  tff('#skF_1', type, '#skF_1': $i).
% 6.47/2.34  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.47/2.34  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.47/2.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.47/2.34  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.47/2.34  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.47/2.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.47/2.34  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.47/2.34  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.47/2.34  
% 6.47/2.36  tff(f_90, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 6.47/2.36  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.47/2.36  tff(f_61, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_relset_1)).
% 6.47/2.36  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.47/2.36  tff(f_41, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.47/2.36  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.47/2.36  tff(f_53, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.47/2.36  tff(f_49, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k1_relset_1(A, B, C), k1_zfmisc_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_relset_1)).
% 6.47/2.36  tff(f_35, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.47/2.36  tff(c_42, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.47/2.36  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.47/2.36  tff(c_5662, plain, (![C_309, A_310, B_311]: (m1_subset_1(C_309, k1_zfmisc_1(k2_zfmisc_1(A_310, B_311))) | ~r1_tarski(k2_relat_1(C_309), B_311) | ~r1_tarski(k1_relat_1(C_309), A_310) | ~v1_relat_1(C_309))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.47/2.36  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.47/2.36  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.36  tff(c_26, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_17, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.47/2.36  tff(c_47, plain, (![A_17]: (v1_funct_2(k1_xboole_0, A_17, k1_xboole_0) | k1_xboole_0=A_17 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 6.47/2.36  tff(c_105, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_47])).
% 6.47/2.36  tff(c_108, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_105])).
% 6.47/2.36  tff(c_112, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_108])).
% 6.47/2.36  tff(c_114, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_47])).
% 6.47/2.36  tff(c_121, plain, (![A_33, B_34, C_35]: (k1_relset_1(A_33, B_34, C_35)=k1_relat_1(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1(k2_zfmisc_1(A_33, B_34))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.47/2.36  tff(c_133, plain, (![A_36, C_37]: (k1_relset_1(A_36, k1_xboole_0, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_121])).
% 6.47/2.36  tff(c_139, plain, (![A_36]: (k1_relset_1(A_36, k1_xboole_0, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_114, c_133])).
% 6.47/2.36  tff(c_148, plain, (![A_39, B_40, C_41]: (m1_subset_1(k1_relset_1(A_39, B_40, C_41), k1_zfmisc_1(A_39)) | ~m1_subset_1(C_41, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.47/2.36  tff(c_161, plain, (![A_36]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_36)) | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(superposition, [status(thm), theory('equality')], [c_139, c_148])).
% 6.47/2.36  tff(c_168, plain, (![A_42]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_42)))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_12, c_161])).
% 6.47/2.36  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.47/2.36  tff(c_182, plain, (![A_43]: (r1_tarski(k1_relat_1(k1_xboole_0), A_43))), inference(resolution, [status(thm)], [c_168, c_16])).
% 6.47/2.36  tff(c_8, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.47/2.36  tff(c_190, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_182, c_8])).
% 6.47/2.36  tff(c_181, plain, (![A_42]: (r1_tarski(k1_relat_1(k1_xboole_0), A_42))), inference(resolution, [status(thm)], [c_168, c_16])).
% 6.47/2.36  tff(c_191, plain, (![A_42]: (r1_tarski(k1_xboole_0, A_42))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_181])).
% 6.47/2.36  tff(c_259, plain, (![C_51, A_52, B_53]: (m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_53))) | ~r1_tarski(k2_relat_1(C_51), B_53) | ~r1_tarski(k1_relat_1(C_51), A_52) | ~v1_relat_1(C_51))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.47/2.36  tff(c_820, plain, (![C_113, A_114, B_115]: (r1_tarski(C_113, k2_zfmisc_1(A_114, B_115)) | ~r1_tarski(k2_relat_1(C_113), B_115) | ~r1_tarski(k1_relat_1(C_113), A_114) | ~v1_relat_1(C_113))), inference(resolution, [status(thm)], [c_259, c_16])).
% 6.47/2.36  tff(c_825, plain, (![C_116, A_117]: (r1_tarski(C_116, k2_zfmisc_1(A_117, k2_relat_1(C_116))) | ~r1_tarski(k1_relat_1(C_116), A_117) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_6, c_820])).
% 6.47/2.36  tff(c_132, plain, (![A_33, B_34, A_6]: (k1_relset_1(A_33, B_34, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_33, B_34)))), inference(resolution, [status(thm)], [c_18, c_121])).
% 6.47/2.36  tff(c_984, plain, (![A_126, C_127]: (k1_relset_1(A_126, k2_relat_1(C_127), C_127)=k1_relat_1(C_127) | ~r1_tarski(k1_relat_1(C_127), A_126) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_825, c_132])).
% 6.47/2.36  tff(c_999, plain, (![C_127]: (k1_relset_1(k1_relat_1(C_127), k2_relat_1(C_127), C_127)=k1_relat_1(C_127) | ~v1_relat_1(C_127))), inference(resolution, [status(thm)], [c_6, c_984])).
% 6.47/2.36  tff(c_24, plain, (![C_16, A_14, B_15]: (m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_14, B_15))) | ~r1_tarski(k2_relat_1(C_16), B_15) | ~r1_tarski(k1_relat_1(C_16), A_14) | ~v1_relat_1(C_16))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.47/2.36  tff(c_356, plain, (![B_66, C_67, A_68]: (k1_xboole_0=B_66 | v1_funct_2(C_67, A_68, B_66) | k1_relset_1(A_68, B_66, C_67)!=A_68 | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_66))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.47/2.36  tff(c_2023, plain, (![B_186, C_187, A_188]: (k1_xboole_0=B_186 | v1_funct_2(C_187, A_188, B_186) | k1_relset_1(A_188, B_186, C_187)!=A_188 | ~r1_tarski(k2_relat_1(C_187), B_186) | ~r1_tarski(k1_relat_1(C_187), A_188) | ~v1_relat_1(C_187))), inference(resolution, [status(thm)], [c_24, c_356])).
% 6.47/2.36  tff(c_4964, plain, (![C_274, A_275]: (k2_relat_1(C_274)=k1_xboole_0 | v1_funct_2(C_274, A_275, k2_relat_1(C_274)) | k1_relset_1(A_275, k2_relat_1(C_274), C_274)!=A_275 | ~r1_tarski(k1_relat_1(C_274), A_275) | ~v1_relat_1(C_274))), inference(resolution, [status(thm)], [c_6, c_2023])).
% 6.47/2.36  tff(c_40, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.47/2.36  tff(c_38, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_90])).
% 6.47/2.36  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38])).
% 6.47/2.36  tff(c_97, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_44])).
% 6.47/2.36  tff(c_4973, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_4964, c_97])).
% 6.47/2.36  tff(c_4982, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_4973])).
% 6.47/2.36  tff(c_4983, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(splitLeft, [status(thm)], [c_4982])).
% 6.47/2.36  tff(c_4986, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_999, c_4983])).
% 6.47/2.36  tff(c_4990, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_4986])).
% 6.47/2.36  tff(c_4991, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_4982])).
% 6.47/2.36  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.47/2.36  tff(c_840, plain, (![A_117, C_116]: (k2_zfmisc_1(A_117, k2_relat_1(C_116))=C_116 | ~r1_tarski(k2_zfmisc_1(A_117, k2_relat_1(C_116)), C_116) | ~r1_tarski(k1_relat_1(C_116), A_117) | ~v1_relat_1(C_116))), inference(resolution, [status(thm)], [c_825, c_2])).
% 6.47/2.36  tff(c_5000, plain, (![A_117]: (k2_zfmisc_1(A_117, k2_relat_1('#skF_1'))='#skF_1' | ~r1_tarski(k2_zfmisc_1(A_117, k1_xboole_0), '#skF_1') | ~r1_tarski(k1_relat_1('#skF_1'), A_117) | ~v1_relat_1('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4991, c_840])).
% 6.47/2.36  tff(c_5023, plain, (![A_117]: (k1_xboole_0='#skF_1' | ~r1_tarski(k1_relat_1('#skF_1'), A_117))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_191, c_12, c_12, c_4991, c_5000])).
% 6.47/2.36  tff(c_5040, plain, (![A_276]: (~r1_tarski(k1_relat_1('#skF_1'), A_276))), inference(splitLeft, [status(thm)], [c_5023])).
% 6.47/2.36  tff(c_5050, plain, $false, inference(resolution, [status(thm)], [c_6, c_5040])).
% 6.47/2.36  tff(c_5051, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_5023])).
% 6.47/2.36  tff(c_167, plain, (![A_36]: (m1_subset_1(k1_relat_1(k1_xboole_0), k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_12, c_161])).
% 6.47/2.36  tff(c_209, plain, (![A_45]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_45)))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_167])).
% 6.47/2.36  tff(c_22, plain, (![A_11, B_12, C_13]: (k1_relset_1(A_11, B_12, C_13)=k1_relat_1(C_13) | ~m1_subset_1(C_13, k1_zfmisc_1(k2_zfmisc_1(A_11, B_12))))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.47/2.36  tff(c_216, plain, (![A_11, B_12]: (k1_relset_1(A_11, B_12, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_209, c_22])).
% 6.47/2.36  tff(c_223, plain, (![A_11, B_12]: (k1_relset_1(A_11, B_12, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_190, c_216])).
% 6.47/2.36  tff(c_192, plain, (![A_36]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_36)))), inference(demodulation, [status(thm), theory('equality')], [c_190, c_167])).
% 6.47/2.36  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.47/2.36  tff(c_30, plain, (![C_19, B_18]: (v1_funct_2(C_19, k1_xboole_0, B_18) | k1_relset_1(k1_xboole_0, B_18, C_19)!=k1_xboole_0 | ~m1_subset_1(C_19, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_18))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.47/2.36  tff(c_303, plain, (![C_58, B_59]: (v1_funct_2(C_58, k1_xboole_0, B_59) | k1_relset_1(k1_xboole_0, B_59, C_58)!=k1_xboole_0 | ~m1_subset_1(C_58, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 6.47/2.36  tff(c_306, plain, (![B_59]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_59) | k1_relset_1(k1_xboole_0, B_59, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_192, c_303])).
% 6.47/2.36  tff(c_315, plain, (![B_59]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_59))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_306])).
% 6.47/2.36  tff(c_5112, plain, (![B_59]: (v1_funct_2('#skF_1', '#skF_1', B_59))), inference(demodulation, [status(thm), theory('equality')], [c_5051, c_5051, c_315])).
% 6.47/2.36  tff(c_5120, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5051, c_5051, c_190])).
% 6.47/2.36  tff(c_4993, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4991, c_97])).
% 6.47/2.36  tff(c_5052, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5051, c_4993])).
% 6.47/2.36  tff(c_5443, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5120, c_5052])).
% 6.47/2.36  tff(c_5494, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5112, c_5443])).
% 6.47/2.36  tff(c_5495, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_44])).
% 6.47/2.36  tff(c_5668, plain, (~r1_tarski(k2_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~r1_tarski(k1_relat_1('#skF_1'), k1_relat_1('#skF_1')) | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_5662, c_5495])).
% 6.47/2.36  tff(c_5682, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_42, c_6, c_6, c_5668])).
% 6.47/2.36  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.47/2.36  
% 6.47/2.36  Inference rules
% 6.47/2.36  ----------------------
% 6.47/2.36  #Ref     : 0
% 6.47/2.36  #Sup     : 1209
% 6.47/2.36  #Fact    : 0
% 6.47/2.36  #Define  : 0
% 6.47/2.36  #Split   : 5
% 6.47/2.36  #Chain   : 0
% 6.47/2.36  #Close   : 0
% 6.47/2.36  
% 6.47/2.36  Ordering : KBO
% 6.47/2.36  
% 6.47/2.36  Simplification rules
% 6.47/2.36  ----------------------
% 6.47/2.36  #Subsume      : 169
% 6.47/2.36  #Demod        : 2560
% 6.47/2.36  #Tautology    : 560
% 6.47/2.36  #SimpNegUnit  : 0
% 6.47/2.36  #BackRed      : 84
% 6.47/2.36  
% 6.47/2.36  #Partial instantiations: 0
% 6.47/2.36  #Strategies tried      : 1
% 6.47/2.36  
% 6.47/2.36  Timing (in seconds)
% 6.47/2.36  ----------------------
% 6.82/2.36  Preprocessing        : 0.33
% 6.82/2.36  Parsing              : 0.17
% 6.82/2.36  CNF conversion       : 0.02
% 6.82/2.36  Main loop            : 1.25
% 6.82/2.37  Inferencing          : 0.40
% 6.82/2.37  Reduction            : 0.46
% 6.82/2.37  Demodulation         : 0.36
% 6.82/2.37  BG Simplification    : 0.05
% 6.82/2.37  Subsumption          : 0.25
% 6.82/2.37  Abstraction          : 0.08
% 6.82/2.37  MUC search           : 0.00
% 6.82/2.37  Cooper               : 0.00
% 6.82/2.37  Total                : 1.62
% 6.82/2.37  Index Insertion      : 0.00
% 6.82/2.37  Index Deletion       : 0.00
% 6.82/2.37  Index Matching       : 0.00
% 6.82/2.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------
