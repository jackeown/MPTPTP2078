%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:32 EST 2020

% Result     : Theorem 6.11s
% Output     : CNFRefutation 6.11s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 528 expanded)
%              Number of leaves         :   45 ( 176 expanded)
%              Depth                    :   13
%              Number of atoms          :  248 (1435 expanded)
%              Number of equality atoms :   85 ( 314 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k3_relset_1,type,(
    k3_relset_1: ( $i * $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(k4_relat_1,type,(
    k4_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( ( v2_funct_1(C)
            & k2_relset_1(A,B,C) = B )
         => ( v1_funct_1(k2_funct_1(C))
            & v1_funct_2(k2_funct_1(C),B,A)
            & m1_subset_1(k2_funct_1(C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

tff(f_59,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_81,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => k2_funct_1(A) = k4_relat_1(A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

tff(f_91,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A)
        & v2_funct_1(A) )
     => ( v1_relat_1(k4_relat_1(A))
        & v1_funct_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_funct_1)).

tff(f_103,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k3_relset_1(A,B,C) = k4_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k3_relset_1(A,B,C),k1_zfmisc_1(k2_zfmisc_1(B,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

tff(f_126,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(f_72,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_109,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( k1_relset_1(B,A,k3_relset_1(A,B,C)) = k2_relset_1(A,B,C)
        & k2_relset_1(B,A,k3_relset_1(A,B,C)) = k1_relset_1(A,B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_relset_1)).

tff(f_63,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k4_relat_1(k4_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',involutiveness_k4_relat_1)).

tff(f_144,axiom,(
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

tff(f_40,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_69,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( k2_relat_1(A) = k1_relat_1(k4_relat_1(A))
        & k1_relat_1(A) = k2_relat_1(k4_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_119,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( ( v1_funct_1(C)
          & v1_partfun1(C,A) )
       => ( v1_funct_1(C)
          & v1_funct_2(C,A,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_funct_2)).

tff(c_74,plain,
    ( ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_178,plain,(
    ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_74])).

tff(c_26,plain,(
    ! [A_14,B_15] : v1_relat_1(k2_zfmisc_1(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_210,plain,(
    ! [B_57,A_58] :
      ( v1_relat_1(B_57)
      | ~ m1_subset_1(B_57,k1_zfmisc_1(A_58))
      | ~ v1_relat_1(A_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_216,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_210])).

tff(c_223,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_216])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_78,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_311,plain,(
    ! [A_77] :
      ( k4_relat_1(A_77) = k2_funct_1(A_77)
      | ~ v2_funct_1(A_77)
      | ~ v1_funct_1(A_77)
      | ~ v1_relat_1(A_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_314,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_311])).

tff(c_317,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_84,c_314])).

tff(c_42,plain,(
    ! [A_19] :
      ( v1_funct_1(k4_relat_1(A_19))
      | ~ v2_funct_1(A_19)
      | ~ v1_funct_1(A_19)
      | ~ v1_relat_1(A_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_324,plain,
    ( v1_funct_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_42])).

tff(c_339,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_223,c_84,c_78,c_324])).

tff(c_341,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_178,c_339])).

tff(c_342,plain,
    ( ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_412,plain,(
    ~ m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_342])).

tff(c_417,plain,(
    ! [B_87,A_88] :
      ( v1_relat_1(B_87)
      | ~ m1_subset_1(B_87,k1_zfmisc_1(A_88))
      | ~ v1_relat_1(A_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_423,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_417])).

tff(c_430,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_423])).

tff(c_481,plain,(
    ! [A_102] :
      ( k4_relat_1(A_102) = k2_funct_1(A_102)
      | ~ v2_funct_1(A_102)
      | ~ v1_funct_1(A_102)
      | ~ v1_relat_1(A_102) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_484,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_481])).

tff(c_487,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_430,c_84,c_484])).

tff(c_581,plain,(
    ! [A_107,B_108,C_109] :
      ( k3_relset_1(A_107,B_108,C_109) = k4_relat_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_107,B_108))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_588,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_581])).

tff(c_601,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_588])).

tff(c_798,plain,(
    ! [A_144,B_145,C_146] :
      ( m1_subset_1(k3_relset_1(A_144,B_145,C_146),k1_zfmisc_1(k2_zfmisc_1(B_145,A_144)))
      | ~ m1_subset_1(C_146,k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_821,plain,
    ( m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_601,c_798])).

tff(c_841,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_821])).

tff(c_843,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_412,c_841])).

tff(c_844,plain,(
    ~ v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_343,plain,(
    v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_74])).

tff(c_845,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(splitRight,[status(thm)],[c_342])).

tff(c_1008,plain,(
    ! [C_164,A_165,B_166] :
      ( v1_partfun1(C_164,A_165)
      | ~ m1_subset_1(C_164,k1_zfmisc_1(k2_zfmisc_1(A_165,B_166)))
      | ~ v1_xboole_0(A_165) ) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_1029,plain,
    ( v1_partfun1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_845,c_1008])).

tff(c_2028,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_1029])).

tff(c_853,plain,(
    ! [B_147,A_148] :
      ( v1_relat_1(B_147)
      | ~ m1_subset_1(B_147,k1_zfmisc_1(A_148))
      | ~ v1_relat_1(A_148) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_862,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_80,c_853])).

tff(c_872,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_862])).

tff(c_36,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_76,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_2033,plain,(
    ! [A_274,B_275,C_276] :
      ( k2_relset_1(A_274,B_275,C_276) = k2_relat_1(C_276)
      | ~ m1_subset_1(C_276,k1_zfmisc_1(k2_zfmisc_1(A_274,B_275))) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_2043,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_2033])).

tff(c_2058,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_2043])).

tff(c_916,plain,(
    ! [A_153] :
      ( k4_relat_1(A_153) = k2_funct_1(A_153)
      | ~ v2_funct_1(A_153)
      | ~ v1_funct_1(A_153)
      | ~ v1_relat_1(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_919,plain,
    ( k4_relat_1('#skF_3') = k2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_916])).

tff(c_922,plain,(
    k4_relat_1('#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_84,c_919])).

tff(c_1035,plain,(
    ! [A_167,B_168,C_169] :
      ( k3_relset_1(A_167,B_168,C_169) = k4_relat_1(C_169)
      | ~ m1_subset_1(C_169,k1_zfmisc_1(k2_zfmisc_1(A_167,B_168))) ) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_1045,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k4_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_1035])).

tff(c_1060,plain,(
    k3_relset_1('#skF_1','#skF_2','#skF_3') = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_922,c_1045])).

tff(c_3916,plain,(
    ! [B_462,A_463,C_464] :
      ( k1_relset_1(B_462,A_463,k3_relset_1(A_463,B_462,C_464)) = k2_relset_1(A_463,B_462,C_464)
      | ~ m1_subset_1(C_464,k1_zfmisc_1(k2_zfmisc_1(A_463,B_462))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_3925,plain,(
    k1_relset_1('#skF_2','#skF_1',k3_relset_1('#skF_1','#skF_2','#skF_3')) = k2_relset_1('#skF_1','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_3916])).

tff(c_3936,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1060,c_3925])).

tff(c_28,plain,(
    ! [A_16] :
      ( k4_relat_1(k4_relat_1(A_16)) = A_16
      | ~ v1_relat_1(A_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_938,plain,
    ( k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_922,c_28])).

tff(c_950,plain,(
    k4_relat_1(k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_938])).

tff(c_1038,plain,(
    k3_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = k4_relat_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_845,c_1035])).

tff(c_1057,plain,(
    k3_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_950,c_1038])).

tff(c_2522,plain,(
    ! [B_340,A_341,C_342] :
      ( k2_relset_1(B_340,A_341,k3_relset_1(A_341,B_340,C_342)) = k1_relset_1(A_341,B_340,C_342)
      | ~ m1_subset_1(C_342,k1_zfmisc_1(k2_zfmisc_1(A_341,B_340))) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_2526,plain,(
    k2_relset_1('#skF_1','#skF_2',k3_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3'))) = k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_845,c_2522])).

tff(c_2541,plain,(
    k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_1057,c_2526])).

tff(c_2826,plain,(
    ! [B_367,C_368,A_369] :
      ( k1_xboole_0 = B_367
      | v1_funct_2(C_368,A_369,B_367)
      | k1_relset_1(A_369,B_367,C_368) != A_369
      | ~ m1_subset_1(C_368,k1_zfmisc_1(k2_zfmisc_1(A_369,B_367))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_2832,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_845,c_2826])).

tff(c_2853,plain,
    ( k1_xboole_0 = '#skF_1'
    | v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2541,c_2832])).

tff(c_2854,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_2853])).

tff(c_16,plain,(
    ! [A_5] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_5)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_344,plain,(
    ! [A_78,B_79] :
      ( r1_tarski(A_78,B_79)
      | ~ m1_subset_1(A_78,k1_zfmisc_1(B_79)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_356,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(resolution,[status(thm)],[c_16,c_344])).

tff(c_2898,plain,(
    ! [A_5] : r1_tarski('#skF_1',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2854,c_356])).

tff(c_12,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2901,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2854,c_2854,c_12])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_849,plain,(
    r1_tarski(k2_funct_1('#skF_3'),k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_845,c_18])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_852,plain,
    ( k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_849,c_4])).

tff(c_2160,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_1'),k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_852])).

tff(c_2986,plain,(
    ~ r1_tarski('#skF_1',k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2901,c_2160])).

tff(c_2992,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2898,c_2986])).

tff(c_2993,plain,(
    k2_zfmisc_1('#skF_2','#skF_1') = k2_funct_1('#skF_3') ),
    inference(splitRight,[status(thm)],[c_852])).

tff(c_2997,plain,(
    m1_subset_1(k2_funct_1('#skF_3'),k1_zfmisc_1(k2_funct_1('#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2993,c_845])).

tff(c_3625,plain,(
    ! [B_444,C_445,A_446] :
      ( k1_xboole_0 = B_444
      | v1_funct_2(C_445,A_446,B_444)
      | k1_relset_1(A_446,B_444,C_445) != A_446
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_zfmisc_1(A_446,B_444))) ) ),
    inference(cnfTransformation,[status(thm)],[f_144])).

tff(c_3631,plain,(
    ! [C_445] :
      ( k1_xboole_0 = '#skF_1'
      | v1_funct_2(C_445,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_445) != '#skF_2'
      | ~ m1_subset_1(C_445,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2993,c_3625])).

tff(c_3965,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_3631])).

tff(c_10,plain,(
    ! [B_4,A_3] :
      ( k1_xboole_0 = B_4
      | k1_xboole_0 = A_3
      | k2_zfmisc_1(A_3,B_4) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_3014,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2'
    | k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2993,c_10])).

tff(c_3048,plain,(
    k2_funct_1('#skF_3') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_3014])).

tff(c_3994,plain,(
    k2_funct_1('#skF_3') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_3048])).

tff(c_4012,plain,(
    ! [A_3] : k2_zfmisc_1(A_3,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3965,c_3965,c_12])).

tff(c_4208,plain,(
    k2_funct_1('#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4012,c_2993])).

tff(c_4210,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_3994,c_4208])).

tff(c_5787,plain,(
    ! [C_576] :
      ( v1_funct_2(C_576,'#skF_2','#skF_1')
      | k1_relset_1('#skF_2','#skF_1',C_576) != '#skF_2'
      | ~ m1_subset_1(C_576,k1_zfmisc_1(k2_funct_1('#skF_3'))) ) ),
    inference(splitRight,[status(thm)],[c_3631])).

tff(c_5793,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | k1_relset_1('#skF_2','#skF_1',k2_funct_1('#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_2997,c_5787])).

tff(c_5805,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_3936,c_5793])).

tff(c_5807,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_5805])).

tff(c_5809,plain,(
    k2_funct_1('#skF_3') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_3014])).

tff(c_5818,plain,(
    k4_relat_1('#skF_3') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5809,c_922])).

tff(c_32,plain,(
    ! [A_17] :
      ( k1_relat_1(k4_relat_1(A_17)) = k2_relat_1(A_17)
      | ~ v1_relat_1(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_5843,plain,
    ( k2_relat_1('#skF_3') = k1_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5818,c_32])).

tff(c_5857,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_872,c_36,c_2058,c_5843])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_5890,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5857,c_2])).

tff(c_5892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2028,c_5890])).

tff(c_5893,plain,(
    v1_partfun1(k2_funct_1('#skF_3'),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_1029])).

tff(c_6342,plain,(
    ! [C_632,A_633,B_634] :
      ( v1_funct_2(C_632,A_633,B_634)
      | ~ v1_partfun1(C_632,A_633)
      | ~ v1_funct_1(C_632)
      | ~ m1_subset_1(C_632,k1_zfmisc_1(k2_zfmisc_1(A_633,B_634))) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_6348,plain,
    ( v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1')
    | ~ v1_partfun1(k2_funct_1('#skF_3'),'#skF_2')
    | ~ v1_funct_1(k2_funct_1('#skF_3')) ),
    inference(resolution,[status(thm)],[c_845,c_6342])).

tff(c_6369,plain,(
    v1_funct_2(k2_funct_1('#skF_3'),'#skF_2','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_343,c_5893,c_6348])).

tff(c_6371,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_844,c_6369])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.02/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.02/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n006.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:22:22 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.11/2.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.11/2.21  
% 6.11/2.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.11/2.21  %$ v1_funct_2 > v1_partfun1 > r2_hidden > r1_tarski > m1_subset_1 > v2_funct_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k3_relset_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k4_relat_1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 6.11/2.21  
% 6.11/2.21  %Foreground sorts:
% 6.11/2.21  
% 6.11/2.21  
% 6.11/2.21  %Background operators:
% 6.11/2.21  
% 6.11/2.21  
% 6.11/2.21  %Foreground operators:
% 6.11/2.21  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.11/2.21  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.11/2.21  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 6.11/2.21  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 6.11/2.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.11/2.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.11/2.21  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.11/2.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.11/2.21  tff(k3_relset_1, type, k3_relset_1: ($i * $i * $i) > $i).
% 6.11/2.21  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.11/2.21  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.11/2.21  tff('#skF_2', type, '#skF_2': $i).
% 6.11/2.21  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 6.11/2.21  tff('#skF_3', type, '#skF_3': $i).
% 6.11/2.21  tff('#skF_1', type, '#skF_1': $i).
% 6.11/2.21  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.11/2.21  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.11/2.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.11/2.21  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.11/2.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.11/2.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.11/2.21  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 6.11/2.21  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.11/2.21  tff(k4_relat_1, type, k4_relat_1: $i > $i).
% 6.11/2.21  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.11/2.21  
% 6.11/2.23  tff(f_161, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((v2_funct_1(C) & (k2_relset_1(A, B, C) = B)) => ((v1_funct_1(k2_funct_1(C)) & v1_funct_2(k2_funct_1(C), B, A)) & m1_subset_1(k2_funct_1(C), k1_zfmisc_1(k2_zfmisc_1(B, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t31_funct_2)).
% 6.11/2.23  tff(f_59, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.11/2.23  tff(f_57, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 6.11/2.23  tff(f_81, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => (k2_funct_1(A) = k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d9_funct_1)).
% 6.11/2.23  tff(f_91, axiom, (![A]: (((v1_relat_1(A) & v1_funct_1(A)) & v2_funct_1(A)) => (v1_relat_1(k4_relat_1(A)) & v1_funct_1(k4_relat_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc5_funct_1)).
% 6.11/2.23  tff(f_103, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k3_relset_1(A, B, C) = k4_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k3_relset_1)).
% 6.11/2.23  tff(f_95, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k3_relset_1(A, B, C), k1_zfmisc_1(k2_zfmisc_1(B, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k3_relset_1)).
% 6.11/2.23  tff(f_126, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 6.11/2.23  tff(f_72, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 6.11/2.23  tff(f_99, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.11/2.23  tff(f_109, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((k1_relset_1(B, A, k3_relset_1(A, B, C)) = k2_relset_1(A, B, C)) & (k2_relset_1(B, A, k3_relset_1(A, B, C)) = k1_relset_1(A, B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_relset_1)).
% 6.11/2.23  tff(f_63, axiom, (![A]: (v1_relat_1(A) => (k4_relat_1(k4_relat_1(A)) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', involutiveness_k4_relat_1)).
% 6.11/2.23  tff(f_144, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 6.11/2.23  tff(f_40, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_subset_1)).
% 6.11/2.23  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 6.11/2.23  tff(f_38, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.11/2.23  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.11/2.23  tff(f_69, axiom, (![A]: (v1_relat_1(A) => ((k2_relat_1(A) = k1_relat_1(k4_relat_1(A))) & (k1_relat_1(A) = k2_relat_1(k4_relat_1(A)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_relat_1)).
% 6.11/2.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 6.11/2.23  tff(f_119, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_partfun1(C, A)) => (v1_funct_1(C) & v1_funct_2(C, A, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_funct_2)).
% 6.11/2.23  tff(c_74, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.11/2.23  tff(c_178, plain, (~v1_funct_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_74])).
% 6.11/2.23  tff(c_26, plain, (![A_14, B_15]: (v1_relat_1(k2_zfmisc_1(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.11/2.23  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.11/2.23  tff(c_210, plain, (![B_57, A_58]: (v1_relat_1(B_57) | ~m1_subset_1(B_57, k1_zfmisc_1(A_58)) | ~v1_relat_1(A_58))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.11/2.23  tff(c_216, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_210])).
% 6.11/2.23  tff(c_223, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_216])).
% 6.11/2.23  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.11/2.23  tff(c_78, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.11/2.23  tff(c_311, plain, (![A_77]: (k4_relat_1(A_77)=k2_funct_1(A_77) | ~v2_funct_1(A_77) | ~v1_funct_1(A_77) | ~v1_relat_1(A_77))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.11/2.23  tff(c_314, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_311])).
% 6.11/2.23  tff(c_317, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_223, c_84, c_314])).
% 6.11/2.23  tff(c_42, plain, (![A_19]: (v1_funct_1(k4_relat_1(A_19)) | ~v2_funct_1(A_19) | ~v1_funct_1(A_19) | ~v1_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_91])).
% 6.11/2.23  tff(c_324, plain, (v1_funct_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_317, c_42])).
% 6.11/2.23  tff(c_339, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_223, c_84, c_78, c_324])).
% 6.11/2.23  tff(c_341, plain, $false, inference(negUnitSimplification, [status(thm)], [c_178, c_339])).
% 6.11/2.23  tff(c_342, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_74])).
% 6.11/2.23  tff(c_412, plain, (~m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitLeft, [status(thm)], [c_342])).
% 6.11/2.23  tff(c_417, plain, (![B_87, A_88]: (v1_relat_1(B_87) | ~m1_subset_1(B_87, k1_zfmisc_1(A_88)) | ~v1_relat_1(A_88))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.11/2.23  tff(c_423, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_417])).
% 6.11/2.23  tff(c_430, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_423])).
% 6.11/2.23  tff(c_481, plain, (![A_102]: (k4_relat_1(A_102)=k2_funct_1(A_102) | ~v2_funct_1(A_102) | ~v1_funct_1(A_102) | ~v1_relat_1(A_102))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.11/2.23  tff(c_484, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_481])).
% 6.11/2.23  tff(c_487, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_430, c_84, c_484])).
% 6.11/2.23  tff(c_581, plain, (![A_107, B_108, C_109]: (k3_relset_1(A_107, B_108, C_109)=k4_relat_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_107, B_108))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.11/2.23  tff(c_588, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_581])).
% 6.11/2.23  tff(c_601, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_487, c_588])).
% 6.11/2.23  tff(c_798, plain, (![A_144, B_145, C_146]: (m1_subset_1(k3_relset_1(A_144, B_145, C_146), k1_zfmisc_1(k2_zfmisc_1(B_145, A_144))) | ~m1_subset_1(C_146, k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.11/2.23  tff(c_821, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_601, c_798])).
% 6.11/2.23  tff(c_841, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_821])).
% 6.11/2.23  tff(c_843, plain, $false, inference(negUnitSimplification, [status(thm)], [c_412, c_841])).
% 6.11/2.23  tff(c_844, plain, (~v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_342])).
% 6.11/2.23  tff(c_343, plain, (v1_funct_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_74])).
% 6.11/2.23  tff(c_845, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(splitRight, [status(thm)], [c_342])).
% 6.11/2.23  tff(c_1008, plain, (![C_164, A_165, B_166]: (v1_partfun1(C_164, A_165) | ~m1_subset_1(C_164, k1_zfmisc_1(k2_zfmisc_1(A_165, B_166))) | ~v1_xboole_0(A_165))), inference(cnfTransformation, [status(thm)], [f_126])).
% 6.11/2.23  tff(c_1029, plain, (v1_partfun1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_845, c_1008])).
% 6.11/2.23  tff(c_2028, plain, (~v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_1029])).
% 6.11/2.23  tff(c_853, plain, (![B_147, A_148]: (v1_relat_1(B_147) | ~m1_subset_1(B_147, k1_zfmisc_1(A_148)) | ~v1_relat_1(A_148))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.11/2.23  tff(c_862, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_80, c_853])).
% 6.11/2.23  tff(c_872, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_862])).
% 6.11/2.23  tff(c_36, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_72])).
% 6.11/2.23  tff(c_76, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_161])).
% 6.11/2.23  tff(c_2033, plain, (![A_274, B_275, C_276]: (k2_relset_1(A_274, B_275, C_276)=k2_relat_1(C_276) | ~m1_subset_1(C_276, k1_zfmisc_1(k2_zfmisc_1(A_274, B_275))))), inference(cnfTransformation, [status(thm)], [f_99])).
% 6.11/2.23  tff(c_2043, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_2033])).
% 6.11/2.23  tff(c_2058, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_2043])).
% 6.11/2.23  tff(c_916, plain, (![A_153]: (k4_relat_1(A_153)=k2_funct_1(A_153) | ~v2_funct_1(A_153) | ~v1_funct_1(A_153) | ~v1_relat_1(A_153))), inference(cnfTransformation, [status(thm)], [f_81])).
% 6.11/2.23  tff(c_919, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_78, c_916])).
% 6.11/2.23  tff(c_922, plain, (k4_relat_1('#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_872, c_84, c_919])).
% 6.11/2.23  tff(c_1035, plain, (![A_167, B_168, C_169]: (k3_relset_1(A_167, B_168, C_169)=k4_relat_1(C_169) | ~m1_subset_1(C_169, k1_zfmisc_1(k2_zfmisc_1(A_167, B_168))))), inference(cnfTransformation, [status(thm)], [f_103])).
% 6.11/2.23  tff(c_1045, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k4_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_1035])).
% 6.11/2.23  tff(c_1060, plain, (k3_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_922, c_1045])).
% 6.11/2.23  tff(c_3916, plain, (![B_462, A_463, C_464]: (k1_relset_1(B_462, A_463, k3_relset_1(A_463, B_462, C_464))=k2_relset_1(A_463, B_462, C_464) | ~m1_subset_1(C_464, k1_zfmisc_1(k2_zfmisc_1(A_463, B_462))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.11/2.23  tff(c_3925, plain, (k1_relset_1('#skF_2', '#skF_1', k3_relset_1('#skF_1', '#skF_2', '#skF_3'))=k2_relset_1('#skF_1', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_80, c_3916])).
% 6.11/2.23  tff(c_3936, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1060, c_3925])).
% 6.11/2.23  tff(c_28, plain, (![A_16]: (k4_relat_1(k4_relat_1(A_16))=A_16 | ~v1_relat_1(A_16))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.11/2.23  tff(c_938, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_922, c_28])).
% 6.11/2.23  tff(c_950, plain, (k4_relat_1(k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_872, c_938])).
% 6.11/2.23  tff(c_1038, plain, (k3_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))=k4_relat_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_845, c_1035])).
% 6.11/2.23  tff(c_1057, plain, (k3_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_950, c_1038])).
% 6.11/2.23  tff(c_2522, plain, (![B_340, A_341, C_342]: (k2_relset_1(B_340, A_341, k3_relset_1(A_341, B_340, C_342))=k1_relset_1(A_341, B_340, C_342) | ~m1_subset_1(C_342, k1_zfmisc_1(k2_zfmisc_1(A_341, B_340))))), inference(cnfTransformation, [status(thm)], [f_109])).
% 6.11/2.23  tff(c_2526, plain, (k2_relset_1('#skF_1', '#skF_2', k3_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3')))=k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_845, c_2522])).
% 6.11/2.23  tff(c_2541, plain, (k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_76, c_1057, c_2526])).
% 6.11/2.23  tff(c_2826, plain, (![B_367, C_368, A_369]: (k1_xboole_0=B_367 | v1_funct_2(C_368, A_369, B_367) | k1_relset_1(A_369, B_367, C_368)!=A_369 | ~m1_subset_1(C_368, k1_zfmisc_1(k2_zfmisc_1(A_369, B_367))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.11/2.23  tff(c_2832, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_845, c_2826])).
% 6.11/2.23  tff(c_2853, plain, (k1_xboole_0='#skF_1' | v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2541, c_2832])).
% 6.11/2.23  tff(c_2854, plain, (k1_xboole_0='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_844, c_2853])).
% 6.11/2.23  tff(c_16, plain, (![A_5]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_5)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 6.11/2.23  tff(c_344, plain, (![A_78, B_79]: (r1_tarski(A_78, B_79) | ~m1_subset_1(A_78, k1_zfmisc_1(B_79)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.11/2.23  tff(c_356, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(resolution, [status(thm)], [c_16, c_344])).
% 6.11/2.23  tff(c_2898, plain, (![A_5]: (r1_tarski('#skF_1', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_2854, c_356])).
% 6.11/2.23  tff(c_12, plain, (![A_3]: (k2_zfmisc_1(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.11/2.23  tff(c_2901, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_2854, c_2854, c_12])).
% 6.11/2.23  tff(c_18, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.11/2.23  tff(c_849, plain, (r1_tarski(k2_funct_1('#skF_3'), k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_845, c_18])).
% 6.11/2.23  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 6.11/2.23  tff(c_852, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_849, c_4])).
% 6.11/2.23  tff(c_2160, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_1'), k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_852])).
% 6.11/2.23  tff(c_2986, plain, (~r1_tarski('#skF_1', k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2901, c_2160])).
% 6.11/2.23  tff(c_2992, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2898, c_2986])).
% 6.11/2.23  tff(c_2993, plain, (k2_zfmisc_1('#skF_2', '#skF_1')=k2_funct_1('#skF_3')), inference(splitRight, [status(thm)], [c_852])).
% 6.11/2.23  tff(c_2997, plain, (m1_subset_1(k2_funct_1('#skF_3'), k1_zfmisc_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2993, c_845])).
% 6.11/2.23  tff(c_3625, plain, (![B_444, C_445, A_446]: (k1_xboole_0=B_444 | v1_funct_2(C_445, A_446, B_444) | k1_relset_1(A_446, B_444, C_445)!=A_446 | ~m1_subset_1(C_445, k1_zfmisc_1(k2_zfmisc_1(A_446, B_444))))), inference(cnfTransformation, [status(thm)], [f_144])).
% 6.11/2.23  tff(c_3631, plain, (![C_445]: (k1_xboole_0='#skF_1' | v1_funct_2(C_445, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_445)!='#skF_2' | ~m1_subset_1(C_445, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_2993, c_3625])).
% 6.11/2.23  tff(c_3965, plain, (k1_xboole_0='#skF_1'), inference(splitLeft, [status(thm)], [c_3631])).
% 6.11/2.23  tff(c_10, plain, (![B_4, A_3]: (k1_xboole_0=B_4 | k1_xboole_0=A_3 | k2_zfmisc_1(A_3, B_4)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_38])).
% 6.11/2.23  tff(c_3014, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2' | k2_funct_1('#skF_3')!=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_2993, c_10])).
% 6.11/2.23  tff(c_3048, plain, (k2_funct_1('#skF_3')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_3014])).
% 6.11/2.23  tff(c_3994, plain, (k2_funct_1('#skF_3')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_3048])).
% 6.11/2.23  tff(c_4012, plain, (![A_3]: (k2_zfmisc_1(A_3, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3965, c_3965, c_12])).
% 6.11/2.23  tff(c_4208, plain, (k2_funct_1('#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_4012, c_2993])).
% 6.11/2.23  tff(c_4210, plain, $false, inference(negUnitSimplification, [status(thm)], [c_3994, c_4208])).
% 6.11/2.23  tff(c_5787, plain, (![C_576]: (v1_funct_2(C_576, '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', C_576)!='#skF_2' | ~m1_subset_1(C_576, k1_zfmisc_1(k2_funct_1('#skF_3'))))), inference(splitRight, [status(thm)], [c_3631])).
% 6.11/2.23  tff(c_5793, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | k1_relset_1('#skF_2', '#skF_1', k2_funct_1('#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_2997, c_5787])).
% 6.11/2.23  tff(c_5805, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_3936, c_5793])).
% 6.11/2.23  tff(c_5807, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_5805])).
% 6.11/2.23  tff(c_5809, plain, (k2_funct_1('#skF_3')=k1_xboole_0), inference(splitRight, [status(thm)], [c_3014])).
% 6.11/2.23  tff(c_5818, plain, (k4_relat_1('#skF_3')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5809, c_922])).
% 6.11/2.23  tff(c_32, plain, (![A_17]: (k1_relat_1(k4_relat_1(A_17))=k2_relat_1(A_17) | ~v1_relat_1(A_17))), inference(cnfTransformation, [status(thm)], [f_69])).
% 6.11/2.23  tff(c_5843, plain, (k2_relat_1('#skF_3')=k1_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5818, c_32])).
% 6.11/2.23  tff(c_5857, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_872, c_36, c_2058, c_5843])).
% 6.11/2.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 6.11/2.23  tff(c_5890, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_5857, c_2])).
% 6.11/2.23  tff(c_5892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2028, c_5890])).
% 6.11/2.23  tff(c_5893, plain, (v1_partfun1(k2_funct_1('#skF_3'), '#skF_2')), inference(splitRight, [status(thm)], [c_1029])).
% 6.11/2.23  tff(c_6342, plain, (![C_632, A_633, B_634]: (v1_funct_2(C_632, A_633, B_634) | ~v1_partfun1(C_632, A_633) | ~v1_funct_1(C_632) | ~m1_subset_1(C_632, k1_zfmisc_1(k2_zfmisc_1(A_633, B_634))))), inference(cnfTransformation, [status(thm)], [f_119])).
% 6.11/2.23  tff(c_6348, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1') | ~v1_partfun1(k2_funct_1('#skF_3'), '#skF_2') | ~v1_funct_1(k2_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_845, c_6342])).
% 6.11/2.23  tff(c_6369, plain, (v1_funct_2(k2_funct_1('#skF_3'), '#skF_2', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_343, c_5893, c_6348])).
% 6.11/2.23  tff(c_6371, plain, $false, inference(negUnitSimplification, [status(thm)], [c_844, c_6369])).
% 6.11/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.11/2.23  
% 6.11/2.23  Inference rules
% 6.11/2.23  ----------------------
% 6.11/2.23  #Ref     : 0
% 6.11/2.23  #Sup     : 1357
% 6.11/2.23  #Fact    : 0
% 6.11/2.23  #Define  : 0
% 6.11/2.23  #Split   : 22
% 6.11/2.23  #Chain   : 0
% 6.11/2.23  #Close   : 0
% 6.11/2.23  
% 6.11/2.23  Ordering : KBO
% 6.11/2.23  
% 6.11/2.23  Simplification rules
% 6.11/2.23  ----------------------
% 6.11/2.23  #Subsume      : 152
% 6.11/2.23  #Demod        : 1613
% 6.11/2.23  #Tautology    : 688
% 6.11/2.23  #SimpNegUnit  : 21
% 6.11/2.23  #BackRed      : 209
% 6.11/2.23  
% 6.11/2.23  #Partial instantiations: 0
% 6.11/2.23  #Strategies tried      : 1
% 6.11/2.23  
% 6.11/2.23  Timing (in seconds)
% 6.11/2.23  ----------------------
% 6.11/2.23  Preprocessing        : 0.34
% 6.11/2.23  Parsing              : 0.18
% 6.11/2.23  CNF conversion       : 0.02
% 6.11/2.24  Main loop            : 1.17
% 6.11/2.24  Inferencing          : 0.39
% 6.11/2.24  Reduction            : 0.40
% 6.11/2.24  Demodulation         : 0.29
% 6.11/2.24  BG Simplification    : 0.05
% 6.39/2.24  Subsumption          : 0.23
% 6.39/2.24  Abstraction          : 0.05
% 6.39/2.24  MUC search           : 0.00
% 6.39/2.24  Cooper               : 0.00
% 6.39/2.24  Total                : 1.56
% 6.39/2.24  Index Insertion      : 0.00
% 6.39/2.24  Index Deletion       : 0.00
% 6.39/2.24  Index Matching       : 0.00
% 6.39/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
