%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:45 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.65s
% Verified   : 
% Statistics : Number of formulae       :   92 (1179 expanded)
%              Number of leaves         :   20 ( 414 expanded)
%              Depth                    :   12
%              Number of atoms          :  137 (3431 expanded)
%              Number of equality atoms :   52 (1029 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_74,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( k1_relset_1(A,B,C) = A
         => ( v1_funct_1(C)
            & v1_funct_2(C,A,B)
            & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_funct_2)).

tff(f_43,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_xboole_0(C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc3_relset_1)).

tff(f_61,axiom,(
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

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_30,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_82,plain,(
    ! [C_16,A_17,B_18] :
      ( v1_xboole_0(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18)))
      | ~ v1_xboole_0(A_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_92,plain,
    ( v1_xboole_0('#skF_3')
    | ~ v1_xboole_0('#skF_1') ),
    inference(resolution,[status(thm)],[c_30,c_82])).

tff(c_95,plain,(
    ~ v1_xboole_0('#skF_1') ),
    inference(splitLeft,[status(thm)],[c_92])).

tff(c_32,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_26,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_34,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_30,c_26])).

tff(c_28,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_296,plain,(
    ! [B_51,C_52,A_53] :
      ( k1_xboole_0 = B_51
      | v1_funct_2(C_52,A_53,B_51)
      | k1_relset_1(A_53,B_51,C_52) != A_53
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_299,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_296])).

tff(c_308,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_299])).

tff(c_309,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_308])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_321,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_8])).

tff(c_340,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_321,c_30])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_91,plain,(
    ! [C_16] :
      ( v1_xboole_0(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k1_xboole_0))
      | ~ v1_xboole_0(k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_82])).

tff(c_94,plain,(
    ! [C_16] :
      ( v1_xboole_0(C_16)
      | ~ m1_subset_1(C_16,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_91])).

tff(c_366,plain,(
    ! [C_58] :
      ( v1_xboole_0(C_58)
      | ~ m1_subset_1(C_58,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_94])).

tff(c_373,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_340,c_366])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_320,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_4])).

tff(c_390,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_373,c_320])).

tff(c_101,plain,(
    ! [B_26,C_27,A_28] :
      ( k1_xboole_0 = B_26
      | v1_funct_2(C_27,A_28,B_26)
      | k1_relset_1(A_28,B_26,C_27) != A_28
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_28,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_104,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_30,c_101])).

tff(c_113,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_104])).

tff(c_114,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_113])).

tff(c_124,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_114,c_8])).

tff(c_131,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_177,plain,(
    ! [C_35] :
      ( v1_xboole_0(C_35)
      | ~ m1_subset_1(C_35,k1_zfmisc_1('#skF_2')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_94])).

tff(c_181,plain,(
    v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_131,c_177])).

tff(c_123,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_4])).

tff(c_185,plain,(
    '#skF_2' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_181,c_123])).

tff(c_190,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_131])).

tff(c_14,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_8,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_38,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_14])).

tff(c_97,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_120,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_114,c_114,c_97])).

tff(c_187,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_185,c_185,c_120])).

tff(c_255,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_190,c_187])).

tff(c_256,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8 ) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_315,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_2',A_8,'#skF_2')
      | A_8 = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_309,c_309,c_309,c_256])).

tff(c_463,plain,(
    ! [A_66] :
      ( v1_funct_2('#skF_3',A_66,'#skF_3')
      | A_66 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_390,c_390,c_315])).

tff(c_402,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_390,c_34])).

tff(c_467,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_463,c_402])).

tff(c_479,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_467,c_373])).

tff(c_482,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_95,c_479])).

tff(c_484,plain,(
    v1_xboole_0('#skF_1') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_492,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_484,c_4])).

tff(c_483,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_92])).

tff(c_488,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_483,c_4])).

tff(c_572,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_488])).

tff(c_579,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_28])).

tff(c_505,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_488])).

tff(c_503,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_3',A_8,'#skF_3')
      | A_8 = '#skF_3'
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_488,c_488,c_488,c_488,c_38])).

tff(c_504,plain,(
    ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_503])).

tff(c_563,plain,(
    ~ m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_504])).

tff(c_496,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_488,c_488,c_10])).

tff(c_542,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_505,c_496])).

tff(c_511,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_505,c_30])).

tff(c_568,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_542,c_511])).

tff(c_569,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_563,c_568])).

tff(c_571,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_503])).

tff(c_628,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_572,c_571])).

tff(c_18,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,k1_xboole_0,B_9)
      | k1_relset_1(k1_xboole_0,B_9,C_10) != k1_xboole_0
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_36,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,k1_xboole_0,B_9)
      | k1_relset_1(k1_xboole_0,B_9,C_10) != k1_xboole_0
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_18])).

tff(c_672,plain,(
    ! [C_84,B_85] :
      ( v1_funct_2(C_84,'#skF_1',B_85)
      | k1_relset_1('#skF_1',B_85,C_84) != '#skF_1'
      | ~ m1_subset_1(C_84,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_492,c_492,c_492,c_492,c_36])).

tff(c_676,plain,(
    ! [B_86] :
      ( v1_funct_2('#skF_1','#skF_1',B_86)
      | k1_relset_1('#skF_1',B_86,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_628,c_672])).

tff(c_580,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_572,c_34])).

tff(c_684,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_676,c_580])).

tff(c_695,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_579,c_684])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:05 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.48  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.49  
% 2.43/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.49  %$ v1_funct_2 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.65/1.49  
% 2.65/1.49  %Foreground sorts:
% 2.65/1.49  
% 2.65/1.49  
% 2.65/1.49  %Background operators:
% 2.65/1.49  
% 2.65/1.49  
% 2.65/1.49  %Foreground operators:
% 2.65/1.49  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.65/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.65/1.49  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.65/1.49  tff('#skF_2', type, '#skF_2': $i).
% 2.65/1.49  tff('#skF_3', type, '#skF_3': $i).
% 2.65/1.49  tff('#skF_1', type, '#skF_1': $i).
% 2.65/1.49  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.65/1.49  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.65/1.49  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.65/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.65/1.49  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.65/1.49  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.65/1.49  
% 2.65/1.51  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.65/1.51  tff(f_43, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_xboole_0(C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc3_relset_1)).
% 2.65/1.51  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.65/1.51  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.65/1.51  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.65/1.51  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.65/1.51  tff(c_30, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.65/1.51  tff(c_82, plain, (![C_16, A_17, B_18]: (v1_xboole_0(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))) | ~v1_xboole_0(A_17))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.65/1.51  tff(c_92, plain, (v1_xboole_0('#skF_3') | ~v1_xboole_0('#skF_1')), inference(resolution, [status(thm)], [c_30, c_82])).
% 2.65/1.51  tff(c_95, plain, (~v1_xboole_0('#skF_1')), inference(splitLeft, [status(thm)], [c_92])).
% 2.65/1.51  tff(c_32, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.65/1.51  tff(c_26, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.65/1.51  tff(c_34, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_32, c_30, c_26])).
% 2.65/1.51  tff(c_28, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.65/1.51  tff(c_296, plain, (![B_51, C_52, A_53]: (k1_xboole_0=B_51 | v1_funct_2(C_52, A_53, B_51) | k1_relset_1(A_53, B_51, C_52)!=A_53 | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_51))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.51  tff(c_299, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_30, c_296])).
% 2.65/1.51  tff(c_308, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_299])).
% 2.65/1.51  tff(c_309, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_308])).
% 2.65/1.51  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.65/1.51  tff(c_321, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_8])).
% 2.65/1.51  tff(c_340, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_321, c_30])).
% 2.65/1.51  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.65/1.51  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.65/1.51  tff(c_91, plain, (![C_16]: (v1_xboole_0(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k1_xboole_0)) | ~v1_xboole_0(k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_82])).
% 2.65/1.51  tff(c_94, plain, (![C_16]: (v1_xboole_0(C_16) | ~m1_subset_1(C_16, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_91])).
% 2.65/1.51  tff(c_366, plain, (![C_58]: (v1_xboole_0(C_58) | ~m1_subset_1(C_58, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_94])).
% 2.65/1.51  tff(c_373, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_340, c_366])).
% 2.65/1.51  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.65/1.51  tff(c_320, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_309, c_4])).
% 2.65/1.51  tff(c_390, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_373, c_320])).
% 2.65/1.51  tff(c_101, plain, (![B_26, C_27, A_28]: (k1_xboole_0=B_26 | v1_funct_2(C_27, A_28, B_26) | k1_relset_1(A_28, B_26, C_27)!=A_28 | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_28, B_26))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.51  tff(c_104, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_30, c_101])).
% 2.65/1.51  tff(c_113, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_28, c_104])).
% 2.65/1.51  tff(c_114, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_34, c_113])).
% 2.65/1.51  tff(c_124, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_114, c_114, c_8])).
% 2.65/1.51  tff(c_131, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_124, c_30])).
% 2.65/1.51  tff(c_177, plain, (![C_35]: (v1_xboole_0(C_35) | ~m1_subset_1(C_35, k1_zfmisc_1('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_94])).
% 2.65/1.51  tff(c_181, plain, (v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_131, c_177])).
% 2.65/1.51  tff(c_123, plain, (![A_1]: (A_1='#skF_2' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_4])).
% 2.65/1.51  tff(c_185, plain, ('#skF_2'='#skF_3'), inference(resolution, [status(thm)], [c_181, c_123])).
% 2.65/1.51  tff(c_190, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_131])).
% 2.65/1.51  tff(c_14, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_8, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.51  tff(c_38, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_14])).
% 2.65/1.51  tff(c_97, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_38])).
% 2.65/1.51  tff(c_120, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_114, c_114, c_97])).
% 2.65/1.51  tff(c_187, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_185, c_185, c_120])).
% 2.65/1.51  tff(c_255, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_190, c_187])).
% 2.65/1.51  tff(c_256, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8)), inference(splitRight, [status(thm)], [c_38])).
% 2.65/1.51  tff(c_315, plain, (![A_8]: (v1_funct_2('#skF_2', A_8, '#skF_2') | A_8='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_309, c_309, c_309, c_256])).
% 2.65/1.51  tff(c_463, plain, (![A_66]: (v1_funct_2('#skF_3', A_66, '#skF_3') | A_66='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_390, c_390, c_315])).
% 2.65/1.51  tff(c_402, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_390, c_34])).
% 2.65/1.51  tff(c_467, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_463, c_402])).
% 2.65/1.51  tff(c_479, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_467, c_373])).
% 2.65/1.51  tff(c_482, plain, $false, inference(negUnitSimplification, [status(thm)], [c_95, c_479])).
% 2.65/1.51  tff(c_484, plain, (v1_xboole_0('#skF_1')), inference(splitRight, [status(thm)], [c_92])).
% 2.65/1.51  tff(c_492, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_484, c_4])).
% 2.65/1.51  tff(c_483, plain, (v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_92])).
% 2.65/1.51  tff(c_488, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_483, c_4])).
% 2.65/1.51  tff(c_572, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_488])).
% 2.65/1.51  tff(c_579, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_572, c_28])).
% 2.65/1.51  tff(c_505, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_492, c_488])).
% 2.65/1.51  tff(c_503, plain, (![A_8]: (v1_funct_2('#skF_3', A_8, '#skF_3') | A_8='#skF_3' | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_488, c_488, c_488, c_488, c_488, c_38])).
% 2.65/1.51  tff(c_504, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_503])).
% 2.65/1.51  tff(c_563, plain, (~m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_504])).
% 2.65/1.51  tff(c_496, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_488, c_488, c_10])).
% 2.65/1.51  tff(c_542, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_505, c_505, c_496])).
% 2.65/1.51  tff(c_511, plain, (m1_subset_1('#skF_1', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_505, c_30])).
% 2.65/1.51  tff(c_568, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_542, c_511])).
% 2.65/1.51  tff(c_569, plain, $false, inference(negUnitSimplification, [status(thm)], [c_563, c_568])).
% 2.65/1.51  tff(c_571, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(splitRight, [status(thm)], [c_503])).
% 2.65/1.51  tff(c_628, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_572, c_572, c_571])).
% 2.65/1.51  tff(c_18, plain, (![C_10, B_9]: (v1_funct_2(C_10, k1_xboole_0, B_9) | k1_relset_1(k1_xboole_0, B_9, C_10)!=k1_xboole_0 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_9))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.65/1.51  tff(c_36, plain, (![C_10, B_9]: (v1_funct_2(C_10, k1_xboole_0, B_9) | k1_relset_1(k1_xboole_0, B_9, C_10)!=k1_xboole_0 | ~m1_subset_1(C_10, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_18])).
% 2.65/1.51  tff(c_672, plain, (![C_84, B_85]: (v1_funct_2(C_84, '#skF_1', B_85) | k1_relset_1('#skF_1', B_85, C_84)!='#skF_1' | ~m1_subset_1(C_84, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_492, c_492, c_492, c_492, c_36])).
% 2.65/1.51  tff(c_676, plain, (![B_86]: (v1_funct_2('#skF_1', '#skF_1', B_86) | k1_relset_1('#skF_1', B_86, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_628, c_672])).
% 2.65/1.51  tff(c_580, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_572, c_34])).
% 2.65/1.51  tff(c_684, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_676, c_580])).
% 2.65/1.51  tff(c_695, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_579, c_684])).
% 2.65/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.65/1.51  
% 2.65/1.51  Inference rules
% 2.65/1.51  ----------------------
% 2.65/1.51  #Ref     : 0
% 2.65/1.51  #Sup     : 133
% 2.65/1.51  #Fact    : 0
% 2.65/1.51  #Define  : 0
% 2.65/1.51  #Split   : 3
% 2.65/1.51  #Chain   : 0
% 2.65/1.51  #Close   : 0
% 2.65/1.51  
% 2.65/1.51  Ordering : KBO
% 2.65/1.51  
% 2.65/1.51  Simplification rules
% 2.65/1.51  ----------------------
% 2.65/1.51  #Subsume      : 9
% 2.65/1.51  #Demod        : 226
% 2.65/1.51  #Tautology    : 108
% 2.65/1.51  #SimpNegUnit  : 4
% 2.65/1.51  #BackRed      : 79
% 2.65/1.51  
% 2.65/1.51  #Partial instantiations: 0
% 2.65/1.51  #Strategies tried      : 1
% 2.65/1.51  
% 2.65/1.51  Timing (in seconds)
% 2.65/1.51  ----------------------
% 2.65/1.51  Preprocessing        : 0.33
% 2.65/1.51  Parsing              : 0.18
% 2.65/1.51  CNF conversion       : 0.02
% 2.65/1.51  Main loop            : 0.30
% 2.65/1.51  Inferencing          : 0.10
% 2.65/1.51  Reduction            : 0.10
% 2.65/1.51  Demodulation         : 0.07
% 2.65/1.51  BG Simplification    : 0.02
% 2.65/1.51  Subsumption          : 0.05
% 2.65/1.51  Abstraction          : 0.01
% 2.65/1.51  MUC search           : 0.00
% 2.65/1.51  Cooper               : 0.00
% 2.65/1.51  Total                : 0.67
% 2.65/1.51  Index Insertion      : 0.00
% 2.65/1.51  Index Deletion       : 0.00
% 2.65/1.51  Index Matching       : 0.00
% 2.65/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------
