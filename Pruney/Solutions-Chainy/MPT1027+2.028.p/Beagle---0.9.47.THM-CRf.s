%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:45 EST 2020

% Result     : Theorem 2.43s
% Output     : CNFRefutation 2.72s
% Verified   : 
% Statistics : Number of formulae       :   90 (2108 expanded)
%              Number of leaves         :   20 ( 653 expanded)
%              Depth                    :   15
%              Number of atoms          :  143 (5191 expanded)
%              Number of equality atoms :   70 (2322 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_38,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_32,plain,
    ( ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_40,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_36,c_32])).

tff(c_34,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_192,plain,(
    ! [B_35,C_36,A_37] :
      ( k1_xboole_0 = B_35
      | v1_funct_2(C_36,A_37,B_35)
      | k1_relset_1(A_37,B_35,C_36) != A_37
      | ~ m1_subset_1(C_36,k1_zfmisc_1(k2_zfmisc_1(A_37,B_35))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_199,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2')
    | k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_36,c_192])).

tff(c_209,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_199])).

tff(c_210,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_209])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_224,plain,(
    ! [A_3] : r1_tarski('#skF_2',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_222,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_210,c_210,c_12])).

tff(c_74,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | ~ m1_subset_1(A_15,k1_zfmisc_1(B_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_78,plain,(
    r1_tarski('#skF_3',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_36,c_74])).

tff(c_84,plain,(
    ! [B_19,A_20] :
      ( B_19 = A_20
      | ~ r1_tarski(B_19,A_20)
      | ~ r1_tarski(A_20,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_91,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_78,c_84])).

tff(c_121,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_91])).

tff(c_245,plain,(
    ~ r1_tarski('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_222,c_121])).

tff(c_250,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_245])).

tff(c_251,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_91])).

tff(c_254,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_251,c_36])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_325,plain,(
    ! [B_50,C_51,A_52] :
      ( k1_xboole_0 = B_50
      | v1_funct_2(C_51,A_52,B_50)
      | k1_relset_1(A_52,B_50,C_51) != A_52
      | ~ m1_subset_1(C_51,k1_zfmisc_1(k2_zfmisc_1(A_52,B_50))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_328,plain,(
    ! [C_51] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(C_51,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',C_51) != '#skF_1'
      | ~ m1_subset_1(C_51,k1_zfmisc_1('#skF_3')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_325])).

tff(c_362,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_328])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_259,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_10])).

tff(c_269,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_259])).

tff(c_372,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_269])).

tff(c_386,plain,(
    ! [A_57] : k2_zfmisc_1(A_57,'#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_362,c_362,c_12])).

tff(c_390,plain,(
    '#skF_2' = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_386,c_251])).

tff(c_397,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_372,c_390])).

tff(c_399,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitRight,[status(thm)],[c_328])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_400,plain,(
    ! [B_58,A_59,A_60] :
      ( k1_xboole_0 = B_58
      | v1_funct_2(A_59,A_60,B_58)
      | k1_relset_1(A_60,B_58,A_59) != A_60
      | ~ r1_tarski(A_59,k2_zfmisc_1(A_60,B_58)) ) ),
    inference(resolution,[status(thm)],[c_18,c_325])).

tff(c_403,plain,(
    ! [A_59] :
      ( k1_xboole_0 = '#skF_2'
      | v1_funct_2(A_59,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',A_59) != '#skF_1'
      | ~ r1_tarski(A_59,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_400])).

tff(c_436,plain,(
    ! [A_63] :
      ( v1_funct_2(A_63,'#skF_1','#skF_2')
      | k1_relset_1('#skF_1','#skF_2',A_63) != '#skF_1'
      | ~ r1_tarski(A_63,'#skF_3') ) ),
    inference(negUnitSimplification,[status(thm)],[c_399,c_403])).

tff(c_439,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_436,c_40])).

tff(c_443,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_34,c_439])).

tff(c_445,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_20,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_8,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_8] :
      ( v1_funct_2(k1_xboole_0,A_8,k1_xboole_0)
      | k1_xboole_0 = A_8
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_20])).

tff(c_492,plain,(
    ! [A_8] :
      ( v1_funct_2('#skF_3',A_8,'#skF_3')
      | A_8 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_254,c_445,c_445,c_445,c_445,c_445,c_44])).

tff(c_444,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_259])).

tff(c_455,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_445,c_445,c_444])).

tff(c_456,plain,(
    '#skF_2' = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_455])).

tff(c_459,plain,(
    ~ v1_funct_2('#skF_3','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_40])).

tff(c_497,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_492,c_459])).

tff(c_458,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_456,c_34])).

tff(c_566,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_497,c_458])).

tff(c_505,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_497,c_254])).

tff(c_504,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_445])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_24,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,k1_xboole_0,B_9)
      | k1_relset_1(k1_xboole_0,B_9,C_10) != k1_xboole_0
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    ! [C_10,B_9] :
      ( v1_funct_2(C_10,k1_xboole_0,B_9)
      | k1_relset_1(k1_xboole_0,B_9,C_10) != k1_xboole_0
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_24])).

tff(c_620,plain,(
    ! [C_82,B_83] :
      ( v1_funct_2(C_82,'#skF_1',B_83)
      | k1_relset_1('#skF_1',B_83,C_82) != '#skF_1'
      | ~ m1_subset_1(C_82,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_504,c_504,c_504,c_504,c_41])).

tff(c_628,plain,(
    ! [B_84] :
      ( v1_funct_2('#skF_1','#skF_1',B_84)
      | k1_relset_1('#skF_1',B_84,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_505,c_620])).

tff(c_498,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_497,c_459])).

tff(c_636,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_628,c_498])).

tff(c_647,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_566,c_636])).

tff(c_648,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_455])).

tff(c_653,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_34])).

tff(c_651,plain,(
    m1_subset_1('#skF_1',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_648,c_254])).

tff(c_650,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_445])).

tff(c_751,plain,(
    ! [C_96,B_97] :
      ( v1_funct_2(C_96,'#skF_1',B_97)
      | k1_relset_1('#skF_1',B_97,C_96) != '#skF_1'
      | ~ m1_subset_1(C_96,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_650,c_650,c_650,c_650,c_41])).

tff(c_773,plain,(
    ! [B_101] :
      ( v1_funct_2('#skF_1','#skF_1',B_101)
      | k1_relset_1('#skF_1',B_101,'#skF_1') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_651,c_751])).

tff(c_654,plain,(
    ~ v1_funct_2('#skF_1','#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_648,c_40])).

tff(c_781,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_1') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_773,c_654])).

tff(c_792,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_653,c_781])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:30:05 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.43/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  
% 2.43/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.43/1.36  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.43/1.36  
% 2.43/1.36  %Foreground sorts:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Background operators:
% 2.43/1.36  
% 2.43/1.36  
% 2.43/1.36  %Foreground operators:
% 2.43/1.36  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.43/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.43/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.43/1.36  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 2.43/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.43/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.43/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.43/1.36  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 2.43/1.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.43/1.36  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.43/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.43/1.36  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 2.43/1.36  
% 2.72/1.38  tff(f_74, negated_conjecture, ~(![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => ((k1_relset_1(A, B, C) = A) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_funct_2)).
% 2.72/1.38  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 2.72/1.38  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.72/1.38  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.72/1.38  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 2.72/1.38  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.72/1.38  tff(c_38, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.38  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.38  tff(c_32, plain, (~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.38  tff(c_40, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_38, c_36, c_32])).
% 2.72/1.38  tff(c_34, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_1'), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.72/1.38  tff(c_192, plain, (![B_35, C_36, A_37]: (k1_xboole_0=B_35 | v1_funct_2(C_36, A_37, B_35) | k1_relset_1(A_37, B_35, C_36)!=A_37 | ~m1_subset_1(C_36, k1_zfmisc_1(k2_zfmisc_1(A_37, B_35))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.72/1.38  tff(c_199, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1'), inference(resolution, [status(thm)], [c_36, c_192])).
% 2.72/1.38  tff(c_209, plain, (k1_xboole_0='#skF_2' | v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_199])).
% 2.72/1.38  tff(c_210, plain, (k1_xboole_0='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_40, c_209])).
% 2.72/1.38  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.72/1.38  tff(c_224, plain, (![A_3]: (r1_tarski('#skF_2', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_210, c_8])).
% 2.72/1.38  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.38  tff(c_222, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_210, c_210, c_12])).
% 2.72/1.38  tff(c_74, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | ~m1_subset_1(A_15, k1_zfmisc_1(B_16)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.38  tff(c_78, plain, (r1_tarski('#skF_3', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_36, c_74])).
% 2.72/1.38  tff(c_84, plain, (![B_19, A_20]: (B_19=A_20 | ~r1_tarski(B_19, A_20) | ~r1_tarski(A_20, B_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.38  tff(c_91, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(resolution, [status(thm)], [c_78, c_84])).
% 2.72/1.38  tff(c_121, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_3')), inference(splitLeft, [status(thm)], [c_91])).
% 2.72/1.38  tff(c_245, plain, (~r1_tarski('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_222, c_121])).
% 2.72/1.38  tff(c_250, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_224, c_245])).
% 2.72/1.38  tff(c_251, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_91])).
% 2.72/1.38  tff(c_254, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_251, c_36])).
% 2.72/1.38  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.72/1.38  tff(c_325, plain, (![B_50, C_51, A_52]: (k1_xboole_0=B_50 | v1_funct_2(C_51, A_52, B_50) | k1_relset_1(A_52, B_50, C_51)!=A_52 | ~m1_subset_1(C_51, k1_zfmisc_1(k2_zfmisc_1(A_52, B_50))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.72/1.38  tff(c_328, plain, (![C_51]: (k1_xboole_0='#skF_2' | v1_funct_2(C_51, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', C_51)!='#skF_1' | ~m1_subset_1(C_51, k1_zfmisc_1('#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_251, c_325])).
% 2.72/1.38  tff(c_362, plain, (k1_xboole_0='#skF_2'), inference(splitLeft, [status(thm)], [c_328])).
% 2.72/1.38  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.38  tff(c_259, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_251, c_10])).
% 2.72/1.38  tff(c_269, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_259])).
% 2.72/1.38  tff(c_372, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_362, c_269])).
% 2.72/1.38  tff(c_386, plain, (![A_57]: (k2_zfmisc_1(A_57, '#skF_2')='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_362, c_362, c_12])).
% 2.72/1.38  tff(c_390, plain, ('#skF_2'='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_386, c_251])).
% 2.72/1.38  tff(c_397, plain, $false, inference(negUnitSimplification, [status(thm)], [c_372, c_390])).
% 2.72/1.38  tff(c_399, plain, (k1_xboole_0!='#skF_2'), inference(splitRight, [status(thm)], [c_328])).
% 2.72/1.38  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.72/1.38  tff(c_400, plain, (![B_58, A_59, A_60]: (k1_xboole_0=B_58 | v1_funct_2(A_59, A_60, B_58) | k1_relset_1(A_60, B_58, A_59)!=A_60 | ~r1_tarski(A_59, k2_zfmisc_1(A_60, B_58)))), inference(resolution, [status(thm)], [c_18, c_325])).
% 2.72/1.38  tff(c_403, plain, (![A_59]: (k1_xboole_0='#skF_2' | v1_funct_2(A_59, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', A_59)!='#skF_1' | ~r1_tarski(A_59, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_251, c_400])).
% 2.72/1.38  tff(c_436, plain, (![A_63]: (v1_funct_2(A_63, '#skF_1', '#skF_2') | k1_relset_1('#skF_1', '#skF_2', A_63)!='#skF_1' | ~r1_tarski(A_63, '#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_399, c_403])).
% 2.72/1.38  tff(c_439, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_436, c_40])).
% 2.72/1.38  tff(c_443, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_34, c_439])).
% 2.72/1.38  tff(c_445, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_259])).
% 2.72/1.38  tff(c_20, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_8, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.72/1.38  tff(c_44, plain, (![A_8]: (v1_funct_2(k1_xboole_0, A_8, k1_xboole_0) | k1_xboole_0=A_8 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_20])).
% 2.72/1.38  tff(c_492, plain, (![A_8]: (v1_funct_2('#skF_3', A_8, '#skF_3') | A_8='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_254, c_445, c_445, c_445, c_445, c_445, c_44])).
% 2.72/1.38  tff(c_444, plain, (k1_xboole_0='#skF_1' | k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_259])).
% 2.72/1.38  tff(c_455, plain, ('#skF_3'='#skF_1' | '#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_445, c_445, c_444])).
% 2.72/1.38  tff(c_456, plain, ('#skF_2'='#skF_3'), inference(splitLeft, [status(thm)], [c_455])).
% 2.72/1.38  tff(c_459, plain, (~v1_funct_2('#skF_3', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_456, c_40])).
% 2.72/1.38  tff(c_497, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_492, c_459])).
% 2.72/1.38  tff(c_458, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_456, c_34])).
% 2.72/1.38  tff(c_566, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_497, c_497, c_458])).
% 2.72/1.38  tff(c_505, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_497, c_497, c_254])).
% 2.72/1.38  tff(c_504, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_497, c_445])).
% 2.72/1.38  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.72/1.38  tff(c_24, plain, (![C_10, B_9]: (v1_funct_2(C_10, k1_xboole_0, B_9) | k1_relset_1(k1_xboole_0, B_9, C_10)!=k1_xboole_0 | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_9))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.72/1.38  tff(c_41, plain, (![C_10, B_9]: (v1_funct_2(C_10, k1_xboole_0, B_9) | k1_relset_1(k1_xboole_0, B_9, C_10)!=k1_xboole_0 | ~m1_subset_1(C_10, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_24])).
% 2.72/1.38  tff(c_620, plain, (![C_82, B_83]: (v1_funct_2(C_82, '#skF_1', B_83) | k1_relset_1('#skF_1', B_83, C_82)!='#skF_1' | ~m1_subset_1(C_82, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_504, c_504, c_504, c_504, c_41])).
% 2.72/1.38  tff(c_628, plain, (![B_84]: (v1_funct_2('#skF_1', '#skF_1', B_84) | k1_relset_1('#skF_1', B_84, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_505, c_620])).
% 2.72/1.38  tff(c_498, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_497, c_497, c_459])).
% 2.72/1.38  tff(c_636, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_628, c_498])).
% 2.72/1.38  tff(c_647, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_566, c_636])).
% 2.72/1.38  tff(c_648, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_455])).
% 2.72/1.38  tff(c_653, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_34])).
% 2.72/1.38  tff(c_651, plain, (m1_subset_1('#skF_1', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_648, c_648, c_254])).
% 2.72/1.38  tff(c_650, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_648, c_445])).
% 2.72/1.38  tff(c_751, plain, (![C_96, B_97]: (v1_funct_2(C_96, '#skF_1', B_97) | k1_relset_1('#skF_1', B_97, C_96)!='#skF_1' | ~m1_subset_1(C_96, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_650, c_650, c_650, c_650, c_41])).
% 2.72/1.38  tff(c_773, plain, (![B_101]: (v1_funct_2('#skF_1', '#skF_1', B_101) | k1_relset_1('#skF_1', B_101, '#skF_1')!='#skF_1')), inference(resolution, [status(thm)], [c_651, c_751])).
% 2.72/1.38  tff(c_654, plain, (~v1_funct_2('#skF_1', '#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_648, c_40])).
% 2.72/1.38  tff(c_781, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_1')!='#skF_1'), inference(resolution, [status(thm)], [c_773, c_654])).
% 2.72/1.38  tff(c_792, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_653, c_781])).
% 2.72/1.38  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.72/1.38  
% 2.72/1.38  Inference rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Ref     : 0
% 2.72/1.38  #Sup     : 147
% 2.72/1.38  #Fact    : 0
% 2.72/1.38  #Define  : 0
% 2.72/1.38  #Split   : 6
% 2.72/1.38  #Chain   : 0
% 2.72/1.38  #Close   : 0
% 2.72/1.38  
% 2.72/1.38  Ordering : KBO
% 2.72/1.38  
% 2.72/1.38  Simplification rules
% 2.72/1.38  ----------------------
% 2.72/1.38  #Subsume      : 10
% 2.72/1.38  #Demod        : 221
% 2.72/1.38  #Tautology    : 105
% 2.72/1.38  #SimpNegUnit  : 3
% 2.72/1.38  #BackRed      : 56
% 2.72/1.38  
% 2.72/1.38  #Partial instantiations: 0
% 2.72/1.38  #Strategies tried      : 1
% 2.72/1.38  
% 2.72/1.38  Timing (in seconds)
% 2.72/1.38  ----------------------
% 2.72/1.38  Preprocessing        : 0.28
% 2.72/1.38  Parsing              : 0.15
% 2.72/1.38  CNF conversion       : 0.02
% 2.72/1.38  Main loop            : 0.32
% 2.72/1.38  Inferencing          : 0.11
% 2.72/1.38  Reduction            : 0.10
% 2.72/1.38  Demodulation         : 0.07
% 2.72/1.38  BG Simplification    : 0.02
% 2.72/1.38  Subsumption          : 0.07
% 2.72/1.38  Abstraction          : 0.02
% 2.72/1.38  MUC search           : 0.00
% 2.72/1.38  Cooper               : 0.00
% 2.72/1.38  Total                : 0.64
% 2.72/1.38  Index Insertion      : 0.00
% 2.72/1.38  Index Deletion       : 0.00
% 2.72/1.38  Index Matching       : 0.00
% 2.72/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------
