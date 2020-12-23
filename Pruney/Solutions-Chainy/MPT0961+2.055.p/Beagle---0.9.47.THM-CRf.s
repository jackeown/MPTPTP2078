%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:10:49 EST 2020

% Result     : Theorem 6.88s
% Output     : CNFRefutation 7.03s
% Verified   : 
% Statistics : Number of formulae       :   85 ( 219 expanded)
%              Number of leaves         :   27 (  82 expanded)
%              Depth                    :   10
%              Number of atoms          :  136 ( 521 expanded)
%              Number of equality atoms :   58 ( 182 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(k1_relset_1,type,(
    k1_relset_1: ( $i * $i * $i ) > $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_97,negated_conjecture,(
    ~ ! [A] :
        ( ( v1_relat_1(A)
          & v1_funct_1(A) )
       => ( v1_funct_1(A)
          & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
          & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => r1_tarski(A,k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_86,axiom,(
    ! [A,B] :
    ? [C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
      & v1_relat_1(C)
      & v4_relat_1(C,A)
      & v5_relat_1(C,B)
      & v1_funct_1(C)
      & v1_funct_2(C,A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc1_funct_2)).

tff(f_39,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_73,axiom,(
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

tff(f_29,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(c_48,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_9655,plain,(
    ! [A_9251] :
      ( r1_tarski(A_9251,k2_zfmisc_1(k1_relat_1(A_9251),k2_relat_1(A_9251)))
      | ~ v1_relat_1(A_9251) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_6,plain,(
    ! [A_2,B_3] :
      ( m1_subset_1(A_2,k1_zfmisc_1(B_3))
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_40,plain,(
    ! [A_14,B_15] : v1_relat_1('#skF_1'(A_14,B_15)) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_38,plain,(
    ! [A_14,B_15] : v4_relat_1('#skF_1'(A_14,B_15),A_14) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9427,plain,(
    ! [B_9222,A_9223] :
      ( r1_tarski(k1_relat_1(B_9222),A_9223)
      | ~ v4_relat_1(B_9222,A_9223)
      | ~ v1_relat_1(B_9222) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_12,plain,(
    ! [A_6] :
      ( r1_tarski(A_6,k2_zfmisc_1(k1_relat_1(A_6),k2_relat_1(A_6)))
      | ~ v1_relat_1(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_233,plain,(
    ! [A_54,B_55,C_56] :
      ( k1_relset_1(A_54,B_55,C_56) = k1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_947,plain,(
    ! [A_459,B_460,A_461] :
      ( k1_relset_1(A_459,B_460,A_461) = k1_relat_1(A_461)
      | ~ r1_tarski(A_461,k2_zfmisc_1(A_459,B_460)) ) ),
    inference(resolution,[status(thm)],[c_6,c_233])).

tff(c_985,plain,(
    ! [A_6] :
      ( k1_relset_1(k1_relat_1(A_6),k2_relat_1(A_6),A_6) = k1_relat_1(A_6)
      | ~ v1_relat_1(A_6) ) ),
    inference(resolution,[status(thm)],[c_12,c_947])).

tff(c_74,plain,(
    ! [A_33] :
      ( k2_relat_1(A_33) != k1_xboole_0
      | k1_xboole_0 = A_33
      | ~ v1_relat_1(A_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_82,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_74])).

tff(c_83,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_82])).

tff(c_517,plain,(
    ! [B_83,C_84,A_85] :
      ( k1_xboole_0 = B_83
      | v1_funct_2(C_84,A_85,B_83)
      | k1_relset_1(A_85,B_83,C_84) != A_85
      | ~ m1_subset_1(C_84,k1_zfmisc_1(k2_zfmisc_1(A_85,B_83))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_6087,plain,(
    ! [B_8434,A_8435,A_8436] :
      ( k1_xboole_0 = B_8434
      | v1_funct_2(A_8435,A_8436,B_8434)
      | k1_relset_1(A_8436,B_8434,A_8435) != A_8436
      | ~ r1_tarski(A_8435,k2_zfmisc_1(A_8436,B_8434)) ) ),
    inference(resolution,[status(thm)],[c_6,c_517])).

tff(c_9177,plain,(
    ! [A_9190] :
      ( k2_relat_1(A_9190) = k1_xboole_0
      | v1_funct_2(A_9190,k1_relat_1(A_9190),k2_relat_1(A_9190))
      | k1_relset_1(k1_relat_1(A_9190),k2_relat_1(A_9190),A_9190) != k1_relat_1(A_9190)
      | ~ v1_relat_1(A_9190) ) ),
    inference(resolution,[status(thm)],[c_12,c_6087])).

tff(c_46,plain,(
    v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_44,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))
    | ~ v1_funct_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))))
    | ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_44])).

tff(c_58,plain,(
    ~ v1_funct_2('#skF_2',k1_relat_1('#skF_2'),k2_relat_1('#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_9180,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2')
    | ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9177,c_58])).

tff(c_9204,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_9180])).

tff(c_9205,plain,(
    k1_relset_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'),'#skF_2') != k1_relat_1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_83,c_9204])).

tff(c_9231,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_985,c_9205])).

tff(c_9239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_9231])).

tff(c_9240,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_82])).

tff(c_64,plain,(
    ! [A_32] :
      ( k1_relat_1(A_32) != k1_xboole_0
      | k1_xboole_0 = A_32
      | ~ v1_relat_1(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_72,plain,
    ( k1_relat_1('#skF_2') != k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_48,c_64])).

tff(c_73,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_9243,plain,(
    k1_relat_1('#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9240,c_73])).

tff(c_9296,plain,(
    ! [B_9201,A_9202] :
      ( r1_tarski(k1_relat_1(B_9201),A_9202)
      | ~ v4_relat_1(B_9201,A_9202)
      | ~ v1_relat_1(B_9201) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ r1_tarski(A_1,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_9245,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ r1_tarski(A_1,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9240,c_9240,c_2])).

tff(c_9306,plain,(
    ! [B_9203] :
      ( k1_relat_1(B_9203) = '#skF_2'
      | ~ v4_relat_1(B_9203,'#skF_2')
      | ~ v1_relat_1(B_9203) ) ),
    inference(resolution,[status(thm)],[c_9296,c_9245])).

tff(c_9310,plain,(
    ! [B_15] :
      ( k1_relat_1('#skF_1'('#skF_2',B_15)) = '#skF_2'
      | ~ v1_relat_1('#skF_1'('#skF_2',B_15)) ) ),
    inference(resolution,[status(thm)],[c_38,c_9306])).

tff(c_9313,plain,(
    ! [B_15] : k1_relat_1('#skF_1'('#skF_2',B_15)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9310])).

tff(c_71,plain,(
    ! [A_14,B_15] :
      ( k1_relat_1('#skF_1'(A_14,B_15)) != k1_xboole_0
      | '#skF_1'(A_14,B_15) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_40,c_64])).

tff(c_9366,plain,(
    ! [A_9210,B_9211] :
      ( k1_relat_1('#skF_1'(A_9210,B_9211)) != '#skF_2'
      | '#skF_1'(A_9210,B_9211) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9240,c_9240,c_71])).

tff(c_9370,plain,(
    ! [B_15] : '#skF_1'('#skF_2',B_15) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_9313,c_9366])).

tff(c_9373,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9370,c_9313])).

tff(c_9375,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_9243,c_9373])).

tff(c_9376,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_9379,plain,(
    ! [A_1] :
      ( A_1 = '#skF_2'
      | ~ r1_tarski(A_1,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9376,c_9376,c_2])).

tff(c_9447,plain,(
    ! [B_9225] :
      ( k1_relat_1(B_9225) = '#skF_2'
      | ~ v4_relat_1(B_9225,'#skF_2')
      | ~ v1_relat_1(B_9225) ) ),
    inference(resolution,[status(thm)],[c_9427,c_9379])).

tff(c_9455,plain,(
    ! [B_15] :
      ( k1_relat_1('#skF_1'('#skF_2',B_15)) = '#skF_2'
      | ~ v1_relat_1('#skF_1'('#skF_2',B_15)) ) ),
    inference(resolution,[status(thm)],[c_38,c_9447])).

tff(c_9461,plain,(
    ! [B_15] : k1_relat_1('#skF_1'('#skF_2',B_15)) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_9455])).

tff(c_9519,plain,(
    ! [A_9232,B_9233] :
      ( k1_relat_1('#skF_1'(A_9232,B_9233)) != '#skF_2'
      | '#skF_1'(A_9232,B_9233) = '#skF_2' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9376,c_9376,c_71])).

tff(c_9528,plain,(
    ! [B_9234] : '#skF_1'('#skF_2',B_9234) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_9461,c_9519])).

tff(c_32,plain,(
    ! [A_14,B_15] : v1_funct_2('#skF_1'(A_14,B_15),A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_9542,plain,(
    ! [B_9234] : v1_funct_2('#skF_2','#skF_2',B_9234) ),
    inference(superposition,[status(thm),theory(equality)],[c_9528,c_32])).

tff(c_9377,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_9384,plain,(
    k1_relat_1('#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_9376,c_9377])).

tff(c_9385,plain,(
    ~ v1_funct_2('#skF_2','#skF_2',k2_relat_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_9384,c_58])).

tff(c_9581,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_9542,c_9385])).

tff(c_9582,plain,(
    ~ m1_subset_1('#skF_2',k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2')))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_9618,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k1_relat_1('#skF_2'),k2_relat_1('#skF_2'))) ),
    inference(resolution,[status(thm)],[c_6,c_9582])).

tff(c_9662,plain,(
    ~ v1_relat_1('#skF_2') ),
    inference(resolution,[status(thm)],[c_9655,c_9618])).

tff(c_9670,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_9662])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:20:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.88/2.38  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.39  
% 6.88/2.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.88/2.39  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 6.88/2.39  
% 6.88/2.39  %Foreground sorts:
% 6.88/2.39  
% 6.88/2.39  
% 6.88/2.39  %Background operators:
% 6.88/2.39  
% 6.88/2.39  
% 6.88/2.39  %Foreground operators:
% 6.88/2.39  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.88/2.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.88/2.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.88/2.39  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.88/2.39  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.88/2.39  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.88/2.39  tff('#skF_2', type, '#skF_2': $i).
% 6.88/2.39  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.88/2.39  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 6.88/2.39  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.88/2.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.88/2.39  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.88/2.39  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.88/2.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.88/2.39  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 6.88/2.39  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.88/2.39  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.88/2.39  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.88/2.39  
% 7.03/2.41  tff(f_97, negated_conjecture, ~(![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_funct_2)).
% 7.03/2.41  tff(f_43, axiom, (![A]: (v1_relat_1(A) => r1_tarski(A, k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_relat_1)).
% 7.03/2.41  tff(f_33, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 7.03/2.41  tff(f_86, axiom, (![A, B]: (?[C]: (((((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & v1_relat_1(C)) & v4_relat_1(C, A)) & v5_relat_1(C, B)) & v1_funct_1(C)) & v1_funct_2(C, A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc1_funct_2)).
% 7.03/2.41  tff(f_39, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d18_relat_1)).
% 7.03/2.41  tff(f_55, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 7.03/2.41  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 7.03/2.41  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 7.03/2.41  tff(f_29, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.03/2.41  tff(c_48, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.03/2.41  tff(c_9655, plain, (![A_9251]: (r1_tarski(A_9251, k2_zfmisc_1(k1_relat_1(A_9251), k2_relat_1(A_9251))) | ~v1_relat_1(A_9251))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.03/2.41  tff(c_6, plain, (![A_2, B_3]: (m1_subset_1(A_2, k1_zfmisc_1(B_3)) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.03/2.41  tff(c_40, plain, (![A_14, B_15]: (v1_relat_1('#skF_1'(A_14, B_15)))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.03/2.41  tff(c_38, plain, (![A_14, B_15]: (v4_relat_1('#skF_1'(A_14, B_15), A_14))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.03/2.41  tff(c_9427, plain, (![B_9222, A_9223]: (r1_tarski(k1_relat_1(B_9222), A_9223) | ~v4_relat_1(B_9222, A_9223) | ~v1_relat_1(B_9222))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.03/2.41  tff(c_12, plain, (![A_6]: (r1_tarski(A_6, k2_zfmisc_1(k1_relat_1(A_6), k2_relat_1(A_6))) | ~v1_relat_1(A_6))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.03/2.41  tff(c_233, plain, (![A_54, B_55, C_56]: (k1_relset_1(A_54, B_55, C_56)=k1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.03/2.41  tff(c_947, plain, (![A_459, B_460, A_461]: (k1_relset_1(A_459, B_460, A_461)=k1_relat_1(A_461) | ~r1_tarski(A_461, k2_zfmisc_1(A_459, B_460)))), inference(resolution, [status(thm)], [c_6, c_233])).
% 7.03/2.41  tff(c_985, plain, (![A_6]: (k1_relset_1(k1_relat_1(A_6), k2_relat_1(A_6), A_6)=k1_relat_1(A_6) | ~v1_relat_1(A_6))), inference(resolution, [status(thm)], [c_12, c_947])).
% 7.03/2.41  tff(c_74, plain, (![A_33]: (k2_relat_1(A_33)!=k1_xboole_0 | k1_xboole_0=A_33 | ~v1_relat_1(A_33))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.03/2.41  tff(c_82, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_48, c_74])).
% 7.03/2.41  tff(c_83, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_82])).
% 7.03/2.41  tff(c_517, plain, (![B_83, C_84, A_85]: (k1_xboole_0=B_83 | v1_funct_2(C_84, A_85, B_83) | k1_relset_1(A_85, B_83, C_84)!=A_85 | ~m1_subset_1(C_84, k1_zfmisc_1(k2_zfmisc_1(A_85, B_83))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 7.03/2.41  tff(c_6087, plain, (![B_8434, A_8435, A_8436]: (k1_xboole_0=B_8434 | v1_funct_2(A_8435, A_8436, B_8434) | k1_relset_1(A_8436, B_8434, A_8435)!=A_8436 | ~r1_tarski(A_8435, k2_zfmisc_1(A_8436, B_8434)))), inference(resolution, [status(thm)], [c_6, c_517])).
% 7.03/2.41  tff(c_9177, plain, (![A_9190]: (k2_relat_1(A_9190)=k1_xboole_0 | v1_funct_2(A_9190, k1_relat_1(A_9190), k2_relat_1(A_9190)) | k1_relset_1(k1_relat_1(A_9190), k2_relat_1(A_9190), A_9190)!=k1_relat_1(A_9190) | ~v1_relat_1(A_9190))), inference(resolution, [status(thm)], [c_12, c_6087])).
% 7.03/2.41  tff(c_46, plain, (v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.03/2.41  tff(c_44, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2')) | ~v1_funct_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_97])).
% 7.03/2.41  tff(c_50, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))) | ~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_44])).
% 7.03/2.41  tff(c_58, plain, (~v1_funct_2('#skF_2', k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))), inference(splitLeft, [status(thm)], [c_50])).
% 7.03/2.41  tff(c_9180, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2') | ~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_9177, c_58])).
% 7.03/2.41  tff(c_9204, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_9180])).
% 7.03/2.41  tff(c_9205, plain, (k1_relset_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'), '#skF_2')!=k1_relat_1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_83, c_9204])).
% 7.03/2.41  tff(c_9231, plain, (~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_985, c_9205])).
% 7.03/2.41  tff(c_9239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_9231])).
% 7.03/2.41  tff(c_9240, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_82])).
% 7.03/2.41  tff(c_64, plain, (![A_32]: (k1_relat_1(A_32)!=k1_xboole_0 | k1_xboole_0=A_32 | ~v1_relat_1(A_32))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.03/2.41  tff(c_72, plain, (k1_relat_1('#skF_2')!=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_48, c_64])).
% 7.03/2.41  tff(c_73, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_72])).
% 7.03/2.41  tff(c_9243, plain, (k1_relat_1('#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9240, c_73])).
% 7.03/2.41  tff(c_9296, plain, (![B_9201, A_9202]: (r1_tarski(k1_relat_1(B_9201), A_9202) | ~v4_relat_1(B_9201, A_9202) | ~v1_relat_1(B_9201))), inference(cnfTransformation, [status(thm)], [f_39])).
% 7.03/2.41  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~r1_tarski(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.03/2.41  tff(c_9245, plain, (![A_1]: (A_1='#skF_2' | ~r1_tarski(A_1, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9240, c_9240, c_2])).
% 7.03/2.41  tff(c_9306, plain, (![B_9203]: (k1_relat_1(B_9203)='#skF_2' | ~v4_relat_1(B_9203, '#skF_2') | ~v1_relat_1(B_9203))), inference(resolution, [status(thm)], [c_9296, c_9245])).
% 7.03/2.41  tff(c_9310, plain, (![B_15]: (k1_relat_1('#skF_1'('#skF_2', B_15))='#skF_2' | ~v1_relat_1('#skF_1'('#skF_2', B_15)))), inference(resolution, [status(thm)], [c_38, c_9306])).
% 7.03/2.41  tff(c_9313, plain, (![B_15]: (k1_relat_1('#skF_1'('#skF_2', B_15))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_9310])).
% 7.03/2.41  tff(c_71, plain, (![A_14, B_15]: (k1_relat_1('#skF_1'(A_14, B_15))!=k1_xboole_0 | '#skF_1'(A_14, B_15)=k1_xboole_0)), inference(resolution, [status(thm)], [c_40, c_64])).
% 7.03/2.41  tff(c_9366, plain, (![A_9210, B_9211]: (k1_relat_1('#skF_1'(A_9210, B_9211))!='#skF_2' | '#skF_1'(A_9210, B_9211)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9240, c_9240, c_71])).
% 7.03/2.41  tff(c_9370, plain, (![B_15]: ('#skF_1'('#skF_2', B_15)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9313, c_9366])).
% 7.03/2.41  tff(c_9373, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9370, c_9313])).
% 7.03/2.41  tff(c_9375, plain, $false, inference(negUnitSimplification, [status(thm)], [c_9243, c_9373])).
% 7.03/2.41  tff(c_9376, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_72])).
% 7.03/2.41  tff(c_9379, plain, (![A_1]: (A_1='#skF_2' | ~r1_tarski(A_1, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9376, c_9376, c_2])).
% 7.03/2.41  tff(c_9447, plain, (![B_9225]: (k1_relat_1(B_9225)='#skF_2' | ~v4_relat_1(B_9225, '#skF_2') | ~v1_relat_1(B_9225))), inference(resolution, [status(thm)], [c_9427, c_9379])).
% 7.03/2.41  tff(c_9455, plain, (![B_15]: (k1_relat_1('#skF_1'('#skF_2', B_15))='#skF_2' | ~v1_relat_1('#skF_1'('#skF_2', B_15)))), inference(resolution, [status(thm)], [c_38, c_9447])).
% 7.03/2.41  tff(c_9461, plain, (![B_15]: (k1_relat_1('#skF_1'('#skF_2', B_15))='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_9455])).
% 7.03/2.41  tff(c_9519, plain, (![A_9232, B_9233]: (k1_relat_1('#skF_1'(A_9232, B_9233))!='#skF_2' | '#skF_1'(A_9232, B_9233)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_9376, c_9376, c_71])).
% 7.03/2.41  tff(c_9528, plain, (![B_9234]: ('#skF_1'('#skF_2', B_9234)='#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_9461, c_9519])).
% 7.03/2.41  tff(c_32, plain, (![A_14, B_15]: (v1_funct_2('#skF_1'(A_14, B_15), A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_86])).
% 7.03/2.41  tff(c_9542, plain, (![B_9234]: (v1_funct_2('#skF_2', '#skF_2', B_9234))), inference(superposition, [status(thm), theory('equality')], [c_9528, c_32])).
% 7.03/2.41  tff(c_9377, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_72])).
% 7.03/2.41  tff(c_9384, plain, (k1_relat_1('#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_9376, c_9377])).
% 7.03/2.41  tff(c_9385, plain, (~v1_funct_2('#skF_2', '#skF_2', k2_relat_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_9384, c_58])).
% 7.03/2.41  tff(c_9581, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_9542, c_9385])).
% 7.03/2.41  tff(c_9582, plain, (~m1_subset_1('#skF_2', k1_zfmisc_1(k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2'))))), inference(splitRight, [status(thm)], [c_50])).
% 7.03/2.41  tff(c_9618, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k1_relat_1('#skF_2'), k2_relat_1('#skF_2')))), inference(resolution, [status(thm)], [c_6, c_9582])).
% 7.03/2.41  tff(c_9662, plain, (~v1_relat_1('#skF_2')), inference(resolution, [status(thm)], [c_9655, c_9618])).
% 7.03/2.41  tff(c_9670, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_48, c_9662])).
% 7.03/2.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.03/2.41  
% 7.03/2.41  Inference rules
% 7.03/2.41  ----------------------
% 7.03/2.41  #Ref     : 0
% 7.03/2.41  #Sup     : 1879
% 7.03/2.41  #Fact    : 12
% 7.03/2.41  #Define  : 0
% 7.03/2.41  #Split   : 13
% 7.03/2.41  #Chain   : 0
% 7.03/2.41  #Close   : 0
% 7.03/2.41  
% 7.03/2.41  Ordering : KBO
% 7.03/2.41  
% 7.03/2.41  Simplification rules
% 7.03/2.41  ----------------------
% 7.03/2.41  #Subsume      : 749
% 7.03/2.41  #Demod        : 1137
% 7.03/2.41  #Tautology    : 700
% 7.03/2.41  #SimpNegUnit  : 3
% 7.03/2.41  #BackRed      : 19
% 7.03/2.41  
% 7.03/2.41  #Partial instantiations: 884
% 7.03/2.41  #Strategies tried      : 1
% 7.03/2.41  
% 7.03/2.41  Timing (in seconds)
% 7.03/2.41  ----------------------
% 7.03/2.41  Preprocessing        : 0.30
% 7.03/2.41  Parsing              : 0.16
% 7.03/2.41  CNF conversion       : 0.02
% 7.03/2.41  Main loop            : 1.34
% 7.03/2.41  Inferencing          : 0.53
% 7.03/2.41  Reduction            : 0.39
% 7.03/2.41  Demodulation         : 0.28
% 7.03/2.41  BG Simplification    : 0.04
% 7.03/2.41  Subsumption          : 0.28
% 7.03/2.41  Abstraction          : 0.06
% 7.03/2.41  MUC search           : 0.00
% 7.03/2.41  Cooper               : 0.00
% 7.03/2.41  Total                : 1.68
% 7.03/2.41  Index Insertion      : 0.00
% 7.03/2.41  Index Deletion       : 0.00
% 7.03/2.41  Index Matching       : 0.00
% 7.03/2.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------
