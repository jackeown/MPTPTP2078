%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:50 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.08s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 307 expanded)
%              Number of leaves         :   25 ( 111 expanded)
%              Depth                    :    7
%              Number of atoms          :  166 (1150 expanded)
%              Number of equality atoms :   28 ( 322 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,A,B)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
           => ( r1_partfun1(C,D)
             => ( ( B = k1_xboole_0
                  & A != k1_xboole_0 )
                | r2_relset_1(A,B,C,D) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_44,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_82,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [D] :
          ( ( v1_funct_1(D)
            & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
         => ( ( v1_partfun1(C,A)
              & v1_partfun1(D,A)
              & r1_partfun1(C,D) )
           => C = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] :
      ( v1_xboole_0(A)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => v1_partfun1(C,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_partfun1)).

tff(c_30,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_81,plain,(
    ! [A_27,B_28,D_29] :
      ( r2_relset_1(A_27,B_28,D_29,D_29)
      | ~ m1_subset_1(D_29,k1_zfmisc_1(k2_zfmisc_1(A_27,B_28))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_91,plain,(
    r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_30,c_81])).

tff(c_26,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_47,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_40,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_38,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_36,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_113,plain,(
    ! [C_38,A_39,B_40] :
      ( v1_partfun1(C_38,A_39)
      | ~ v1_funct_2(C_38,A_39,B_40)
      | ~ v1_funct_1(C_38)
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(A_39,B_40)))
      | v1_xboole_0(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_116,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_36,c_113])).

tff(c_128,plain,
    ( v1_partfun1('#skF_3','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_38,c_116])).

tff(c_133,plain,(
    v1_xboole_0('#skF_2') ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_136,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_133,c_4])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_136])).

tff(c_141,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_142,plain,(
    ~ v1_xboole_0('#skF_2') ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_34,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_32,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_119,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_2') ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_131,plain,
    ( v1_partfun1('#skF_4','#skF_1')
    | v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_32,c_119])).

tff(c_143,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_142,c_131])).

tff(c_28,plain,(
    r1_partfun1('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_158,plain,(
    ! [D_47,C_48,A_49,B_50] :
      ( D_47 = C_48
      | ~ r1_partfun1(C_48,D_47)
      | ~ v1_partfun1(D_47,A_49)
      | ~ v1_partfun1(C_48,A_49)
      | ~ m1_subset_1(D_47,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1(D_47)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1(C_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_160,plain,(
    ! [A_49,B_50] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_49)
      | ~ v1_partfun1('#skF_3',A_49)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_158])).

tff(c_163,plain,(
    ! [A_49,B_50] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_49)
      | ~ v1_partfun1('#skF_3',A_49)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_49,B_50)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_49,B_50))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_160])).

tff(c_165,plain,(
    ! [A_51,B_52] :
      ( ~ v1_partfun1('#skF_4',A_51)
      | ~ v1_partfun1('#skF_3',A_51)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_51,B_52)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_51,B_52))) ) ),
    inference(splitLeft,[status(thm)],[c_163])).

tff(c_168,plain,
    ( ~ v1_partfun1('#skF_4','#skF_1')
    | ~ v1_partfun1('#skF_3','#skF_1')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_36,c_165])).

tff(c_178,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_141,c_143,c_168])).

tff(c_179,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_163])).

tff(c_24,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_183,plain,(
    ~ r2_relset_1('#skF_1','#skF_2','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_24])).

tff(c_192,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_183])).

tff(c_193,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_8,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_207,plain,(
    ! [A_2] : k2_zfmisc_1(A_2,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_193,c_8])).

tff(c_194,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_201,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_194])).

tff(c_240,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_201,c_30])).

tff(c_253,plain,(
    ! [A_58,B_59,D_60] :
      ( r2_relset_1(A_58,B_59,D_60,D_60)
      | ~ m1_subset_1(D_60,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_267,plain,(
    ! [A_65,D_66] :
      ( r2_relset_1(A_65,'#skF_1',D_66,D_66)
      | ~ m1_subset_1(D_66,k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_253])).

tff(c_272,plain,(
    ! [A_65] : r2_relset_1(A_65,'#skF_1','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_240,c_267])).

tff(c_239,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_207,c_201,c_36])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_215,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_1',B_3) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_193,c_10])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_196,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_193,c_2])).

tff(c_275,plain,(
    ! [C_68,A_69,B_70] :
      ( v1_partfun1(C_68,A_69)
      | ~ m1_subset_1(C_68,k1_zfmisc_1(k2_zfmisc_1(A_69,B_70)))
      | ~ v1_xboole_0(A_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_278,plain,(
    ! [C_68] :
      ( v1_partfun1(C_68,'#skF_1')
      | ~ m1_subset_1(C_68,k1_zfmisc_1('#skF_1'))
      | ~ v1_xboole_0('#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_275])).

tff(c_285,plain,(
    ! [C_72] :
      ( v1_partfun1(C_72,'#skF_1')
      | ~ m1_subset_1(C_72,k1_zfmisc_1('#skF_1')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_278])).

tff(c_293,plain,(
    v1_partfun1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_239,c_285])).

tff(c_292,plain,(
    v1_partfun1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_240,c_285])).

tff(c_336,plain,(
    ! [D_84,C_85,A_86,B_87] :
      ( D_84 = C_85
      | ~ r1_partfun1(C_85,D_84)
      | ~ v1_partfun1(D_84,A_86)
      | ~ v1_partfun1(C_85,A_86)
      | ~ m1_subset_1(D_84,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(D_84)
      | ~ m1_subset_1(C_85,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_85) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_338,plain,(
    ! [A_86,B_87] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_86)
      | ~ v1_partfun1('#skF_3',A_86)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1('#skF_3') ) ),
    inference(resolution,[status(thm)],[c_28,c_336])).

tff(c_341,plain,(
    ! [A_86,B_87] :
      ( '#skF_3' = '#skF_4'
      | ~ v1_partfun1('#skF_4',A_86)
      | ~ v1_partfun1('#skF_3',A_86)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_86,B_87))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_34,c_338])).

tff(c_343,plain,(
    ! [A_88,B_89] :
      ( ~ v1_partfun1('#skF_4',A_88)
      | ~ v1_partfun1('#skF_3',A_88)
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_88,B_89)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1(A_88,B_89))) ) ),
    inference(splitLeft,[status(thm)],[c_341])).

tff(c_346,plain,(
    ! [B_3] :
      ( ~ v1_partfun1('#skF_4','#skF_1')
      | ~ v1_partfun1('#skF_3','#skF_1')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_3)))
      | ~ m1_subset_1('#skF_3',k1_zfmisc_1('#skF_1')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_343])).

tff(c_352,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_240,c_215,c_293,c_292,c_346])).

tff(c_353,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_341])).

tff(c_238,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_24])).

tff(c_359,plain,(
    ~ r2_relset_1('#skF_1','#skF_1','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_353,c_238])).

tff(c_369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_272,c_359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:20:19 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.81  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.83  
% 3.08/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.84  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.08/1.84  
% 3.08/1.84  %Foreground sorts:
% 3.08/1.84  
% 3.08/1.84  
% 3.08/1.84  %Background operators:
% 3.08/1.84  
% 3.08/1.84  
% 3.08/1.84  %Foreground operators:
% 3.08/1.84  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.08/1.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.08/1.84  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.08/1.84  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.08/1.84  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.08/1.84  tff('#skF_2', type, '#skF_2': $i).
% 3.08/1.84  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.08/1.84  tff('#skF_3', type, '#skF_3': $i).
% 3.08/1.84  tff('#skF_1', type, '#skF_1': $i).
% 3.08/1.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.08/1.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.08/1.84  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.08/1.84  tff('#skF_4', type, '#skF_4': $i).
% 3.08/1.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.08/1.84  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.08/1.84  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.08/1.84  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.08/1.84  
% 3.08/1.87  tff(f_105, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t142_funct_2)).
% 3.08/1.87  tff(f_44, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 3.08/1.87  tff(f_65, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.08/1.87  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.08/1.87  tff(f_82, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_partfun1)).
% 3.08/1.87  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.08/1.87  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.08/1.87  tff(f_51, axiom, (![A, B]: (v1_xboole_0(A) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_partfun1(C, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_partfun1)).
% 3.08/1.87  tff(c_30, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_81, plain, (![A_27, B_28, D_29]: (r2_relset_1(A_27, B_28, D_29, D_29) | ~m1_subset_1(D_29, k1_zfmisc_1(k2_zfmisc_1(A_27, B_28))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.87  tff(c_91, plain, (r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_30, c_81])).
% 3.08/1.87  tff(c_26, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_47, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_26])).
% 3.08/1.87  tff(c_40, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_38, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_36, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_113, plain, (![C_38, A_39, B_40]: (v1_partfun1(C_38, A_39) | ~v1_funct_2(C_38, A_39, B_40) | ~v1_funct_1(C_38) | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(A_39, B_40))) | v1_xboole_0(B_40))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.08/1.87  tff(c_116, plain, (v1_partfun1('#skF_3', '#skF_1') | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_36, c_113])).
% 3.08/1.87  tff(c_128, plain, (v1_partfun1('#skF_3', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_40, c_38, c_116])).
% 3.08/1.87  tff(c_133, plain, (v1_xboole_0('#skF_2')), inference(splitLeft, [status(thm)], [c_128])).
% 3.08/1.87  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.08/1.87  tff(c_136, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_133, c_4])).
% 3.08/1.87  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_136])).
% 3.08/1.87  tff(c_141, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_128])).
% 3.08/1.87  tff(c_142, plain, (~v1_xboole_0('#skF_2')), inference(splitRight, [status(thm)], [c_128])).
% 3.08/1.87  tff(c_34, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_32, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_119, plain, (v1_partfun1('#skF_4', '#skF_1') | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_2')), inference(resolution, [status(thm)], [c_30, c_113])).
% 3.08/1.87  tff(c_131, plain, (v1_partfun1('#skF_4', '#skF_1') | v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_34, c_32, c_119])).
% 3.08/1.87  tff(c_143, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(negUnitSimplification, [status(thm)], [c_142, c_131])).
% 3.08/1.87  tff(c_28, plain, (r1_partfun1('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_158, plain, (![D_47, C_48, A_49, B_50]: (D_47=C_48 | ~r1_partfun1(C_48, D_47) | ~v1_partfun1(D_47, A_49) | ~v1_partfun1(C_48, A_49) | ~m1_subset_1(D_47, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1(D_47) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1(C_48))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.08/1.87  tff(c_160, plain, (![A_49, B_50]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_49) | ~v1_partfun1('#skF_3', A_49) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_158])).
% 3.08/1.87  tff(c_163, plain, (![A_49, B_50]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_49) | ~v1_partfun1('#skF_3', A_49) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_49, B_50))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_160])).
% 3.08/1.87  tff(c_165, plain, (![A_51, B_52]: (~v1_partfun1('#skF_4', A_51) | ~v1_partfun1('#skF_3', A_51) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_51, B_52))))), inference(splitLeft, [status(thm)], [c_163])).
% 3.08/1.87  tff(c_168, plain, (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_36, c_165])).
% 3.08/1.87  tff(c_178, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_141, c_143, c_168])).
% 3.08/1.87  tff(c_179, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_163])).
% 3.08/1.87  tff(c_24, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_105])).
% 3.08/1.87  tff(c_183, plain, (~r2_relset_1('#skF_1', '#skF_2', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_24])).
% 3.08/1.87  tff(c_192, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_91, c_183])).
% 3.08/1.87  tff(c_193, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 3.08/1.87  tff(c_8, plain, (![A_2]: (k2_zfmisc_1(A_2, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.08/1.87  tff(c_207, plain, (![A_2]: (k2_zfmisc_1(A_2, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_193, c_8])).
% 3.08/1.87  tff(c_194, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_26])).
% 3.08/1.87  tff(c_201, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_193, c_194])).
% 3.08/1.87  tff(c_240, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_201, c_30])).
% 3.08/1.87  tff(c_253, plain, (![A_58, B_59, D_60]: (r2_relset_1(A_58, B_59, D_60, D_60) | ~m1_subset_1(D_60, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_44])).
% 3.08/1.87  tff(c_267, plain, (![A_65, D_66]: (r2_relset_1(A_65, '#skF_1', D_66, D_66) | ~m1_subset_1(D_66, k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_207, c_253])).
% 3.08/1.87  tff(c_272, plain, (![A_65]: (r2_relset_1(A_65, '#skF_1', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_240, c_267])).
% 3.08/1.87  tff(c_239, plain, (m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_207, c_201, c_36])).
% 3.08/1.87  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.08/1.87  tff(c_215, plain, (![B_3]: (k2_zfmisc_1('#skF_1', B_3)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_193, c_10])).
% 3.08/1.87  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.08/1.87  tff(c_196, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_193, c_2])).
% 3.08/1.87  tff(c_275, plain, (![C_68, A_69, B_70]: (v1_partfun1(C_68, A_69) | ~m1_subset_1(C_68, k1_zfmisc_1(k2_zfmisc_1(A_69, B_70))) | ~v1_xboole_0(A_69))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.08/1.87  tff(c_278, plain, (![C_68]: (v1_partfun1(C_68, '#skF_1') | ~m1_subset_1(C_68, k1_zfmisc_1('#skF_1')) | ~v1_xboole_0('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_215, c_275])).
% 3.08/1.87  tff(c_285, plain, (![C_72]: (v1_partfun1(C_72, '#skF_1') | ~m1_subset_1(C_72, k1_zfmisc_1('#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_196, c_278])).
% 3.08/1.87  tff(c_293, plain, (v1_partfun1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_239, c_285])).
% 3.08/1.87  tff(c_292, plain, (v1_partfun1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_240, c_285])).
% 3.08/1.87  tff(c_336, plain, (![D_84, C_85, A_86, B_87]: (D_84=C_85 | ~r1_partfun1(C_85, D_84) | ~v1_partfun1(D_84, A_86) | ~v1_partfun1(C_85, A_86) | ~m1_subset_1(D_84, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(D_84) | ~m1_subset_1(C_85, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_85))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.08/1.87  tff(c_338, plain, (![A_86, B_87]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_86) | ~v1_partfun1('#skF_3', A_86) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1('#skF_3'))), inference(resolution, [status(thm)], [c_28, c_336])).
% 3.08/1.87  tff(c_341, plain, (![A_86, B_87]: ('#skF_3'='#skF_4' | ~v1_partfun1('#skF_4', A_86) | ~v1_partfun1('#skF_3', A_86) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_34, c_338])).
% 3.08/1.87  tff(c_343, plain, (![A_88, B_89]: (~v1_partfun1('#skF_4', A_88) | ~v1_partfun1('#skF_3', A_88) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1(A_88, B_89))))), inference(splitLeft, [status(thm)], [c_341])).
% 3.08/1.87  tff(c_346, plain, (![B_3]: (~v1_partfun1('#skF_4', '#skF_1') | ~v1_partfun1('#skF_3', '#skF_1') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_3))) | ~m1_subset_1('#skF_3', k1_zfmisc_1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_215, c_343])).
% 3.08/1.87  tff(c_352, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_239, c_240, c_215, c_293, c_292, c_346])).
% 3.08/1.87  tff(c_353, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_341])).
% 3.08/1.87  tff(c_238, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_201, c_24])).
% 3.08/1.87  tff(c_359, plain, (~r2_relset_1('#skF_1', '#skF_1', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_353, c_238])).
% 3.08/1.87  tff(c_369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_272, c_359])).
% 3.08/1.87  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.08/1.87  
% 3.08/1.87  Inference rules
% 3.08/1.87  ----------------------
% 3.08/1.87  #Ref     : 0
% 3.08/1.87  #Sup     : 62
% 3.08/1.87  #Fact    : 0
% 3.08/1.87  #Define  : 0
% 3.08/1.87  #Split   : 5
% 3.08/1.87  #Chain   : 0
% 3.08/1.87  #Close   : 0
% 3.08/1.87  
% 3.08/1.87  Ordering : KBO
% 3.08/1.87  
% 3.08/1.87  Simplification rules
% 3.08/1.87  ----------------------
% 3.08/1.87  #Subsume      : 4
% 3.08/1.87  #Demod        : 75
% 3.08/1.87  #Tautology    : 38
% 3.08/1.87  #SimpNegUnit  : 2
% 3.08/1.87  #BackRed      : 18
% 3.08/1.87  
% 3.08/1.87  #Partial instantiations: 0
% 3.08/1.87  #Strategies tried      : 1
% 3.08/1.87  
% 3.08/1.87  Timing (in seconds)
% 3.08/1.87  ----------------------
% 3.08/1.87  Preprocessing        : 0.50
% 3.08/1.87  Parsing              : 0.26
% 3.08/1.87  CNF conversion       : 0.04
% 3.08/1.87  Main loop            : 0.41
% 3.08/1.87  Inferencing          : 0.15
% 3.08/1.87  Reduction            : 0.13
% 3.08/1.88  Demodulation         : 0.10
% 3.08/1.88  BG Simplification    : 0.02
% 3.08/1.88  Subsumption          : 0.06
% 3.08/1.88  Abstraction          : 0.02
% 3.08/1.88  MUC search           : 0.00
% 3.08/1.88  Cooper               : 0.00
% 3.08/1.88  Total                : 0.99
% 3.08/1.88  Index Insertion      : 0.00
% 3.08/1.88  Index Deletion       : 0.00
% 3.08/1.88  Index Matching       : 0.00
% 3.08/1.88  BG Taut test         : 0.00
%------------------------------------------------------------------------------
