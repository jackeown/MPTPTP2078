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
% DateTime   : Thu Dec  3 10:10:50 EST 2020

% Result     : Theorem 3.23s
% Output     : CNFRefutation 3.43s
% Verified   : 
% Statistics : Number of formulae       :   86 ( 220 expanded)
%              Number of leaves         :   27 (  81 expanded)
%              Depth                    :    8
%              Number of atoms          :  131 ( 495 expanded)
%              Number of equality atoms :   64 ( 214 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_96,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_85,axiom,(
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

tff(f_59,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_33,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_1055,plain,(
    ! [A_147] :
      ( r1_tarski(A_147,k2_zfmisc_1(k1_relat_1(A_147),k2_relat_1(A_147)))
      | ~ v1_relat_1(A_147) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_947,plain,(
    ! [A_135,B_136] :
      ( m1_subset_1(A_135,k1_zfmisc_1(B_136))
      | ~ r1_tarski(A_135,B_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_9] :
      ( r1_tarski(A_9,k2_zfmisc_1(k1_relat_1(A_9),k2_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_12,plain,(
    ! [A_4,B_5] :
      ( m1_subset_1(A_4,k1_zfmisc_1(B_5))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_246,plain,(
    ! [A_51,B_52,C_53] :
      ( k1_relset_1(A_51,B_52,C_53) = k1_relat_1(C_53)
      | ~ m1_subset_1(C_53,k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_345,plain,(
    ! [A_71,B_72,A_73] :
      ( k1_relset_1(A_71,B_72,A_73) = k1_relat_1(A_73)
      | ~ r1_tarski(A_73,k2_zfmisc_1(A_71,B_72)) ) ),
    inference(resolution,[status(thm)],[c_12,c_246])).

tff(c_364,plain,(
    ! [A_9] :
      ( k1_relset_1(k1_relat_1(A_9),k2_relat_1(A_9),A_9) = k1_relat_1(A_9)
      | ~ v1_relat_1(A_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_345])).

tff(c_164,plain,(
    ! [A_34] :
      ( k2_relat_1(A_34) != k1_xboole_0
      | k1_xboole_0 = A_34
      | ~ v1_relat_1(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_178,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_164])).

tff(c_179,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_178])).

tff(c_264,plain,(
    ! [B_54,C_55,A_56] :
      ( k1_xboole_0 = B_54
      | v1_funct_2(C_55,A_56,B_54)
      | k1_relset_1(A_56,B_54,C_55) != A_56
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_56,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_535,plain,(
    ! [B_91,A_92,A_93] :
      ( k1_xboole_0 = B_91
      | v1_funct_2(A_92,A_93,B_91)
      | k1_relset_1(A_93,B_91,A_92) != A_93
      | ~ r1_tarski(A_92,k2_zfmisc_1(A_93,B_91)) ) ),
    inference(resolution,[status(thm)],[c_12,c_264])).

tff(c_559,plain,(
    ! [A_94] :
      ( k2_relat_1(A_94) = k1_xboole_0
      | v1_funct_2(A_94,k1_relat_1(A_94),k2_relat_1(A_94))
      | k1_relset_1(k1_relat_1(A_94),k2_relat_1(A_94),A_94) != k1_relat_1(A_94)
      | ~ v1_relat_1(A_94) ) ),
    inference(resolution,[status(thm)],[c_16,c_535])).

tff(c_46,plain,(
    v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))
    | ~ v1_funct_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))))
    | ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_99,plain,(
    ~ v1_funct_2('#skF_1',k1_relat_1('#skF_1'),k2_relat_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_566,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1')
    | ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_559,c_99])).

tff(c_578,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_566])).

tff(c_579,plain,(
    k1_relset_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'),'#skF_1') != k1_relat_1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_179,c_578])).

tff(c_612,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_579])).

tff(c_616,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_612])).

tff(c_617,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_178])).

tff(c_22,plain,(
    ! [A_11] : k1_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_26,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_112,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_115,plain,(
    ! [A_12] :
      ( k1_relat_1(k6_relat_1(A_12)) != k1_xboole_0
      | k6_relat_1(A_12) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_26,c_112])).

tff(c_123,plain,(
    ! [A_33] :
      ( k1_xboole_0 != A_33
      | k6_relat_1(A_33) = k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_115])).

tff(c_132,plain,(
    ! [A_33] :
      ( k1_relat_1(k1_xboole_0) = A_33
      | k1_xboole_0 != A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_22])).

tff(c_724,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_617,c_132])).

tff(c_121,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_48,c_112])).

tff(c_150,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_121])).

tff(c_621,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_617,c_150])).

tff(c_728,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_724,c_621])).

tff(c_729,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_730,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_121])).

tff(c_743,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_730])).

tff(c_8,plain,(
    ! [A_3] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_736,plain,(
    ! [A_3] : m1_subset_1('#skF_1',k1_zfmisc_1(A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_8])).

tff(c_904,plain,(
    ! [A_127,B_128,C_129] :
      ( k1_relset_1(A_127,B_128,C_129) = k1_relat_1(C_129)
      | ~ m1_subset_1(C_129,k1_zfmisc_1(k2_zfmisc_1(A_127,B_128))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_908,plain,(
    ! [A_127,B_128] : k1_relset_1(A_127,B_128,'#skF_1') = k1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_736,c_904])).

tff(c_920,plain,(
    ! [A_127,B_128] : k1_relset_1(A_127,B_128,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_908])).

tff(c_6,plain,(
    ! [B_2] : k2_zfmisc_1(k1_xboole_0,B_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_36,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_53,plain,(
    ! [C_18,B_17] :
      ( v1_funct_2(C_18,k1_xboole_0,B_17)
      | k1_relset_1(k1_xboole_0,B_17,C_18) != k1_xboole_0
      | ~ m1_subset_1(C_18,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_36])).

tff(c_930,plain,(
    ! [C_132,B_133] :
      ( v1_funct_2(C_132,'#skF_1',B_133)
      | k1_relset_1('#skF_1',B_133,C_132) != '#skF_1'
      | ~ m1_subset_1(C_132,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_729,c_729,c_729,c_53])).

tff(c_933,plain,(
    ! [B_133] :
      ( v1_funct_2('#skF_1','#skF_1',B_133)
      | k1_relset_1('#skF_1',B_133,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_736,c_930])).

tff(c_939,plain,(
    ! [B_133] : v1_funct_2('#skF_1','#skF_1',B_133) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_933])).

tff(c_24,plain,(
    ! [A_11] : k2_relat_1(k6_relat_1(A_11)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_129,plain,(
    ! [A_33] :
      ( k2_relat_1(k1_xboole_0) = A_33
      | k1_xboole_0 != A_33 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_24])).

tff(c_828,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_729,c_729,c_129])).

tff(c_744,plain,(
    ~ v1_funct_2('#skF_1','#skF_1',k2_relat_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_99])).

tff(c_829,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_744])).

tff(c_943,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_939,c_829])).

tff(c_944,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_951,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k1_relat_1('#skF_1'),k2_relat_1('#skF_1'))) ),
    inference(resolution,[status(thm)],[c_947,c_944])).

tff(c_1058,plain,(
    ~ v1_relat_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_1055,c_951])).

tff(c_1068,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1058])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 20:03:24 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.23/1.51  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  
% 3.23/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.23/1.52  %$ v1_funct_2 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 3.23/1.52  
% 3.23/1.52  %Foreground sorts:
% 3.23/1.52  
% 3.23/1.52  
% 3.23/1.52  %Background operators:
% 3.23/1.52  
% 3.23/1.52  
% 3.23/1.52  %Foreground operators:
% 3.23/1.52  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.23/1.52  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.23/1.52  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.23/1.52  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.23/1.52  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.23/1.52  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.23/1.52  tff('#skF_1', type, '#skF_1': $i).
% 3.23/1.52  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 3.23/1.52  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.23/1.52  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.23/1.52  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.23/1.52  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 3.23/1.52  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.23/1.52  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.23/1.52  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.23/1.52  
% 3.43/1.54  tff(f_96, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 3.43/1.54  tff(f_47, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 3.43/1.54  tff(f_37, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 3.43/1.54  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 3.43/1.54  tff(f_55, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 3.43/1.54  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 3.43/1.54  tff(f_59, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 3.43/1.54  tff(f_63, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 3.43/1.54  tff(f_33, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.43/1.54  tff(f_31, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.43/1.54  tff(c_48, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.43/1.54  tff(c_1055, plain, (![A_147]: (r1_tarski(A_147, k2_zfmisc_1(k1_relat_1(A_147), k2_relat_1(A_147))) | ~v1_relat_1(A_147))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.43/1.54  tff(c_947, plain, (![A_135, B_136]: (m1_subset_1(A_135, k1_zfmisc_1(B_136)) | ~r1_tarski(A_135, B_136))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.54  tff(c_16, plain, (![A_9]: (r1_tarski(A_9, k2_zfmisc_1(k1_relat_1(A_9), k2_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.43/1.54  tff(c_12, plain, (![A_4, B_5]: (m1_subset_1(A_4, k1_zfmisc_1(B_5)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.43/1.54  tff(c_246, plain, (![A_51, B_52, C_53]: (k1_relset_1(A_51, B_52, C_53)=k1_relat_1(C_53) | ~m1_subset_1(C_53, k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.43/1.54  tff(c_345, plain, (![A_71, B_72, A_73]: (k1_relset_1(A_71, B_72, A_73)=k1_relat_1(A_73) | ~r1_tarski(A_73, k2_zfmisc_1(A_71, B_72)))), inference(resolution, [status(thm)], [c_12, c_246])).
% 3.43/1.54  tff(c_364, plain, (![A_9]: (k1_relset_1(k1_relat_1(A_9), k2_relat_1(A_9), A_9)=k1_relat_1(A_9) | ~v1_relat_1(A_9))), inference(resolution, [status(thm)], [c_16, c_345])).
% 3.43/1.54  tff(c_164, plain, (![A_34]: (k2_relat_1(A_34)!=k1_xboole_0 | k1_xboole_0=A_34 | ~v1_relat_1(A_34))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.43/1.54  tff(c_178, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_164])).
% 3.43/1.54  tff(c_179, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_178])).
% 3.43/1.54  tff(c_264, plain, (![B_54, C_55, A_56]: (k1_xboole_0=B_54 | v1_funct_2(C_55, A_56, B_54) | k1_relset_1(A_56, B_54, C_55)!=A_56 | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_56, B_54))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.54  tff(c_535, plain, (![B_91, A_92, A_93]: (k1_xboole_0=B_91 | v1_funct_2(A_92, A_93, B_91) | k1_relset_1(A_93, B_91, A_92)!=A_93 | ~r1_tarski(A_92, k2_zfmisc_1(A_93, B_91)))), inference(resolution, [status(thm)], [c_12, c_264])).
% 3.43/1.54  tff(c_559, plain, (![A_94]: (k2_relat_1(A_94)=k1_xboole_0 | v1_funct_2(A_94, k1_relat_1(A_94), k2_relat_1(A_94)) | k1_relset_1(k1_relat_1(A_94), k2_relat_1(A_94), A_94)!=k1_relat_1(A_94) | ~v1_relat_1(A_94))), inference(resolution, [status(thm)], [c_16, c_535])).
% 3.43/1.54  tff(c_46, plain, (v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.43/1.54  tff(c_44, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1')) | ~v1_funct_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.43/1.54  tff(c_50, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))) | ~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 3.43/1.54  tff(c_99, plain, (~v1_funct_2('#skF_1', k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_50])).
% 3.43/1.54  tff(c_566, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1') | ~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_559, c_99])).
% 3.43/1.54  tff(c_578, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_566])).
% 3.43/1.54  tff(c_579, plain, (k1_relset_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'), '#skF_1')!=k1_relat_1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_179, c_578])).
% 3.43/1.54  tff(c_612, plain, (~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_364, c_579])).
% 3.43/1.54  tff(c_616, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_612])).
% 3.43/1.54  tff(c_617, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_178])).
% 3.43/1.54  tff(c_22, plain, (![A_11]: (k1_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.43/1.54  tff(c_26, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.43/1.54  tff(c_112, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.43/1.54  tff(c_115, plain, (![A_12]: (k1_relat_1(k6_relat_1(A_12))!=k1_xboole_0 | k6_relat_1(A_12)=k1_xboole_0)), inference(resolution, [status(thm)], [c_26, c_112])).
% 3.43/1.54  tff(c_123, plain, (![A_33]: (k1_xboole_0!=A_33 | k6_relat_1(A_33)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_22, c_115])).
% 3.43/1.54  tff(c_132, plain, (![A_33]: (k1_relat_1(k1_xboole_0)=A_33 | k1_xboole_0!=A_33)), inference(superposition, [status(thm), theory('equality')], [c_123, c_22])).
% 3.43/1.54  tff(c_724, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_617, c_617, c_132])).
% 3.43/1.54  tff(c_121, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_48, c_112])).
% 3.43/1.54  tff(c_150, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_121])).
% 3.43/1.54  tff(c_621, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_617, c_150])).
% 3.43/1.54  tff(c_728, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_724, c_621])).
% 3.43/1.54  tff(c_729, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_121])).
% 3.43/1.54  tff(c_730, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_121])).
% 3.43/1.54  tff(c_743, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_729, c_730])).
% 3.43/1.54  tff(c_8, plain, (![A_3]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.43/1.54  tff(c_736, plain, (![A_3]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_729, c_8])).
% 3.43/1.54  tff(c_904, plain, (![A_127, B_128, C_129]: (k1_relset_1(A_127, B_128, C_129)=k1_relat_1(C_129) | ~m1_subset_1(C_129, k1_zfmisc_1(k2_zfmisc_1(A_127, B_128))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.43/1.54  tff(c_908, plain, (![A_127, B_128]: (k1_relset_1(A_127, B_128, '#skF_1')=k1_relat_1('#skF_1'))), inference(resolution, [status(thm)], [c_736, c_904])).
% 3.43/1.54  tff(c_920, plain, (![A_127, B_128]: (k1_relset_1(A_127, B_128, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_743, c_908])).
% 3.43/1.54  tff(c_6, plain, (![B_2]: (k2_zfmisc_1(k1_xboole_0, B_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.43/1.54  tff(c_36, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_17))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.43/1.54  tff(c_53, plain, (![C_18, B_17]: (v1_funct_2(C_18, k1_xboole_0, B_17) | k1_relset_1(k1_xboole_0, B_17, C_18)!=k1_xboole_0 | ~m1_subset_1(C_18, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_36])).
% 3.43/1.54  tff(c_930, plain, (![C_132, B_133]: (v1_funct_2(C_132, '#skF_1', B_133) | k1_relset_1('#skF_1', B_133, C_132)!='#skF_1' | ~m1_subset_1(C_132, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_729, c_729, c_729, c_729, c_53])).
% 3.43/1.54  tff(c_933, plain, (![B_133]: (v1_funct_2('#skF_1', '#skF_1', B_133) | k1_relset_1('#skF_1', B_133, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_736, c_930])).
% 3.43/1.54  tff(c_939, plain, (![B_133]: (v1_funct_2('#skF_1', '#skF_1', B_133))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_933])).
% 3.43/1.54  tff(c_24, plain, (![A_11]: (k2_relat_1(k6_relat_1(A_11))=A_11)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.43/1.54  tff(c_129, plain, (![A_33]: (k2_relat_1(k1_xboole_0)=A_33 | k1_xboole_0!=A_33)), inference(superposition, [status(thm), theory('equality')], [c_123, c_24])).
% 3.43/1.54  tff(c_828, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_729, c_729, c_129])).
% 3.43/1.54  tff(c_744, plain, (~v1_funct_2('#skF_1', '#skF_1', k2_relat_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_743, c_99])).
% 3.43/1.54  tff(c_829, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_828, c_744])).
% 3.43/1.54  tff(c_943, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_939, c_829])).
% 3.43/1.54  tff(c_944, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1'))))), inference(splitRight, [status(thm)], [c_50])).
% 3.43/1.54  tff(c_951, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k1_relat_1('#skF_1'), k2_relat_1('#skF_1')))), inference(resolution, [status(thm)], [c_947, c_944])).
% 3.43/1.54  tff(c_1058, plain, (~v1_relat_1('#skF_1')), inference(resolution, [status(thm)], [c_1055, c_951])).
% 3.43/1.54  tff(c_1068, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_1058])).
% 3.43/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.43/1.54  
% 3.43/1.54  Inference rules
% 3.43/1.54  ----------------------
% 3.43/1.54  #Ref     : 5
% 3.43/1.54  #Sup     : 187
% 3.43/1.54  #Fact    : 0
% 3.43/1.54  #Define  : 0
% 3.43/1.54  #Split   : 9
% 3.43/1.54  #Chain   : 0
% 3.43/1.54  #Close   : 0
% 3.43/1.54  
% 3.43/1.54  Ordering : KBO
% 3.43/1.54  
% 3.43/1.54  Simplification rules
% 3.43/1.54  ----------------------
% 3.43/1.54  #Subsume      : 27
% 3.43/1.54  #Demod        : 209
% 3.43/1.54  #Tautology    : 129
% 3.43/1.54  #SimpNegUnit  : 23
% 3.43/1.54  #BackRed      : 36
% 3.43/1.54  
% 3.43/1.54  #Partial instantiations: 0
% 3.43/1.54  #Strategies tried      : 1
% 3.43/1.54  
% 3.43/1.54  Timing (in seconds)
% 3.43/1.54  ----------------------
% 3.43/1.54  Preprocessing        : 0.35
% 3.43/1.54  Parsing              : 0.19
% 3.43/1.54  CNF conversion       : 0.02
% 3.43/1.54  Main loop            : 0.38
% 3.43/1.54  Inferencing          : 0.14
% 3.43/1.54  Reduction            : 0.13
% 3.43/1.54  Demodulation         : 0.09
% 3.43/1.54  BG Simplification    : 0.02
% 3.43/1.54  Subsumption          : 0.06
% 3.43/1.54  Abstraction          : 0.02
% 3.43/1.54  MUC search           : 0.00
% 3.43/1.54  Cooper               : 0.00
% 3.43/1.54  Total                : 0.77
% 3.43/1.54  Index Insertion      : 0.00
% 3.43/1.54  Index Deletion       : 0.00
% 3.43/1.54  Index Matching       : 0.00
% 3.43/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
