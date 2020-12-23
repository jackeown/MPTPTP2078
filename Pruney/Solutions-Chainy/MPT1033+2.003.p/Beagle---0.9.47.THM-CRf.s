%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:16:50 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.47s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 363 expanded)
%              Number of leaves         :   36 ( 130 expanded)
%              Depth                    :   10
%              Number of atoms          :  149 (1206 expanded)
%              Number of equality atoms :   24 ( 346 expanded)
%              Maximal formula depth    :   13 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(v1_subset_1,type,(
    v1_subset_1: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(r1_partfun1,type,(
    r1_partfun1: ( $i * $i ) > $o )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_145,negated_conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t142_funct_2)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => r2_relset_1(A,B,C,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_relset_1)).

tff(f_93,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ! [C] :
          ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
         => ( ( v1_funct_1(C)
              & v1_funct_2(C,A,B) )
           => ( v1_funct_1(C)
              & v1_partfun1(C,A) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_110,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_partfun1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_xboole_0(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

tff(f_38,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(f_51,axiom,(
    ! [A] :
    ? [B] :
      ( m1_subset_1(B,k1_zfmisc_1(A))
      & ~ v1_subset_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',rc3_subset_1)).

tff(c_58,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_52,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_418,plain,(
    ! [A_95,B_96,C_97,D_98] :
      ( r2_relset_1(A_95,B_96,C_97,C_97)
      | ~ m1_subset_1(D_98,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96)))
      | ~ m1_subset_1(C_97,k1_zfmisc_1(k2_zfmisc_1(A_95,B_96))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_440,plain,(
    ! [C_99] :
      ( r2_relset_1('#skF_2','#skF_3',C_99,C_99)
      | ~ m1_subset_1(C_99,k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ) ),
    inference(resolution,[status(thm)],[c_52,c_418])).

tff(c_452,plain,(
    r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_58,c_440])).

tff(c_48,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_63,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_56,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_54,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_503,plain,(
    ! [C_109,A_110,B_111] :
      ( v1_partfun1(C_109,A_110)
      | ~ v1_funct_2(C_109,A_110,B_111)
      | ~ v1_funct_1(C_109)
      | ~ m1_subset_1(C_109,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111)))
      | v1_xboole_0(B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_509,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_5')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_52,c_503])).

tff(c_530,plain,
    ( v1_partfun1('#skF_5','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_54,c_509])).

tff(c_537,plain,(
    v1_xboole_0('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_530])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_543,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_537,c_4])).

tff(c_548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_63,c_543])).

tff(c_550,plain,(
    ~ v1_xboole_0('#skF_3') ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_62,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_60,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_512,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_3')
    | ~ v1_funct_1('#skF_4')
    | v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_503])).

tff(c_533,plain,
    ( v1_partfun1('#skF_4','#skF_2')
    | v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_60,c_512])).

tff(c_551,plain,(
    v1_partfun1('#skF_4','#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_550,c_533])).

tff(c_549,plain,(
    v1_partfun1('#skF_5','#skF_2') ),
    inference(splitRight,[status(thm)],[c_530])).

tff(c_50,plain,(
    r1_partfun1('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_579,plain,(
    ! [D_113,C_114,A_115,B_116] :
      ( D_113 = C_114
      | ~ r1_partfun1(C_114,D_113)
      | ~ v1_partfun1(D_113,A_115)
      | ~ v1_partfun1(C_114,A_115)
      | ~ m1_subset_1(D_113,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(D_113)
      | ~ m1_subset_1(C_114,k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1(C_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_581,plain,(
    ! [A_115,B_116] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_115)
      | ~ v1_partfun1('#skF_4',A_115)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_50,c_579])).

tff(c_584,plain,(
    ! [A_115,B_116] :
      ( '#skF_5' = '#skF_4'
      | ~ v1_partfun1('#skF_5',A_115)
      | ~ v1_partfun1('#skF_4',A_115)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_115,B_116)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_115,B_116))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_56,c_581])).

tff(c_686,plain,(
    ! [A_144,B_145] :
      ( ~ v1_partfun1('#skF_5',A_144)
      | ~ v1_partfun1('#skF_4',A_144)
      | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1(A_144,B_145)))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(A_144,B_145))) ) ),
    inference(splitLeft,[status(thm)],[c_584])).

tff(c_693,plain,
    ( ~ v1_partfun1('#skF_5','#skF_2')
    | ~ v1_partfun1('#skF_4','#skF_2')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(resolution,[status(thm)],[c_52,c_686])).

tff(c_706,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_551,c_549,c_693])).

tff(c_707,plain,(
    '#skF_5' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_584])).

tff(c_46,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_145])).

tff(c_716,plain,(
    ~ r2_relset_1('#skF_2','#skF_3','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_707,c_46])).

tff(c_729,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_452,c_716])).

tff(c_731,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_730,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_737,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_730])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_732,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_730,c_2])).

tff(c_743,plain,(
    v1_xboole_0('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_732])).

tff(c_10,plain,(
    ! [B_3] : k2_zfmisc_1(k1_xboole_0,B_3) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_757,plain,(
    ! [B_3] : k2_zfmisc_1('#skF_3',B_3) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_731,c_10])).

tff(c_785,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_737,c_58])).

tff(c_787,plain,(
    ! [B_152,A_153] :
      ( v1_xboole_0(B_152)
      | ~ m1_subset_1(B_152,k1_zfmisc_1(A_153))
      | ~ v1_xboole_0(A_153) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_793,plain,
    ( v1_xboole_0('#skF_4')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_785,c_787])).

tff(c_805,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_793])).

tff(c_749,plain,(
    ! [A_1] :
      ( A_1 = '#skF_3'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_4])).

tff(c_828,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_805,c_749])).

tff(c_12,plain,(
    ! [A_4] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_4)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_765,plain,(
    ! [A_4] : m1_subset_1('#skF_3',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_731,c_12])).

tff(c_846,plain,(
    ! [A_4] : m1_subset_1('#skF_4',k1_zfmisc_1(A_4)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_765])).

tff(c_18,plain,(
    ! [A_8] : m1_subset_1('#skF_1'(A_8),k1_zfmisc_1(A_8)) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1183,plain,(
    ! [A_208,B_209,C_210,D_211] :
      ( r2_relset_1(A_208,B_209,C_210,C_210)
      | ~ m1_subset_1(D_211,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209)))
      | ~ m1_subset_1(C_210,k1_zfmisc_1(k2_zfmisc_1(A_208,B_209))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1199,plain,(
    ! [A_212,B_213,C_214] :
      ( r2_relset_1(A_212,B_213,C_214,C_214)
      | ~ m1_subset_1(C_214,k1_zfmisc_1(k2_zfmisc_1(A_212,B_213))) ) ),
    inference(resolution,[status(thm)],[c_18,c_1183])).

tff(c_1213,plain,(
    ! [A_212,B_213] : r2_relset_1(A_212,B_213,'#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_846,c_1199])).

tff(c_786,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_757,c_737,c_52])).

tff(c_790,plain,
    ( v1_xboole_0('#skF_5')
    | ~ v1_xboole_0('#skF_3') ),
    inference(resolution,[status(thm)],[c_786,c_787])).

tff(c_802,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_743,c_790])).

tff(c_812,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_802,c_749])).

tff(c_783,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_737,c_46])).

tff(c_831,plain,(
    ~ r2_relset_1('#skF_3','#skF_3','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_812,c_783])).

tff(c_940,plain,(
    ~ r2_relset_1('#skF_4','#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_828,c_828,c_828,c_831])).

tff(c_1217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1213,c_940])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 18:57:36 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.53  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.54  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_subset_1 > v1_partfun1 > r2_hidden > r1_tarski > r1_partfun1 > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 3.47/1.54  
% 3.47/1.54  %Foreground sorts:
% 3.47/1.54  
% 3.47/1.54  
% 3.47/1.54  %Background operators:
% 3.47/1.54  
% 3.47/1.54  
% 3.47/1.54  %Foreground operators:
% 3.47/1.54  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 3.47/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.47/1.54  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 3.47/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.47/1.54  tff(v1_subset_1, type, v1_subset_1: ($i * $i) > $o).
% 3.47/1.54  tff('#skF_1', type, '#skF_1': $i > $i).
% 3.47/1.54  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.47/1.54  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.47/1.54  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 3.47/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.47/1.54  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 3.47/1.54  tff('#skF_2', type, '#skF_2': $i).
% 3.47/1.54  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 3.47/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.47/1.54  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 3.47/1.54  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 3.47/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.47/1.54  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 3.47/1.54  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.47/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.47/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.47/1.54  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 3.47/1.54  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.47/1.54  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 3.47/1.54  tff(r1_partfun1, type, r1_partfun1: ($i * $i) > $o).
% 3.47/1.54  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 3.47/1.54  
% 3.47/1.55  tff(f_145, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_partfun1(C, D) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | r2_relset_1(A, B, C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t142_funct_2)).
% 3.47/1.55  tff(f_79, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => r2_relset_1(A, B, C, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', reflexivity_r2_relset_1)).
% 3.47/1.55  tff(f_93, axiom, (![A, B]: (~v1_xboole_0(B) => (![C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((v1_funct_1(C) & v1_funct_2(C, A, B)) => (v1_funct_1(C) & v1_partfun1(C, A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc5_funct_2)).
% 3.47/1.55  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.47/1.55  tff(f_110, axiom, (![A, B, C]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: ((v1_funct_1(D) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((v1_partfun1(C, A) & v1_partfun1(D, A)) & r1_partfun1(C, D)) => (C = D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_partfun1)).
% 3.47/1.55  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 3.47/1.55  tff(f_36, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.47/1.55  tff(f_45, axiom, (![A]: (v1_xboole_0(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_xboole_0(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_subset_1)).
% 3.47/1.55  tff(f_38, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 3.47/1.55  tff(f_51, axiom, (![A]: (?[B]: (m1_subset_1(B, k1_zfmisc_1(A)) & ~v1_subset_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', rc3_subset_1)).
% 3.47/1.55  tff(c_58, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_52, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_418, plain, (![A_95, B_96, C_97, D_98]: (r2_relset_1(A_95, B_96, C_97, C_97) | ~m1_subset_1(D_98, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))) | ~m1_subset_1(C_97, k1_zfmisc_1(k2_zfmisc_1(A_95, B_96))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.55  tff(c_440, plain, (![C_99]: (r2_relset_1('#skF_2', '#skF_3', C_99, C_99) | ~m1_subset_1(C_99, k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))))), inference(resolution, [status(thm)], [c_52, c_418])).
% 3.47/1.55  tff(c_452, plain, (r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_58, c_440])).
% 3.47/1.55  tff(c_48, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_63, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_48])).
% 3.47/1.55  tff(c_56, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_54, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_503, plain, (![C_109, A_110, B_111]: (v1_partfun1(C_109, A_110) | ~v1_funct_2(C_109, A_110, B_111) | ~v1_funct_1(C_109) | ~m1_subset_1(C_109, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))) | v1_xboole_0(B_111))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.47/1.55  tff(c_509, plain, (v1_partfun1('#skF_5', '#skF_2') | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_5') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_52, c_503])).
% 3.47/1.55  tff(c_530, plain, (v1_partfun1('#skF_5', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_54, c_509])).
% 3.47/1.55  tff(c_537, plain, (v1_xboole_0('#skF_3')), inference(splitLeft, [status(thm)], [c_530])).
% 3.47/1.55  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 3.47/1.55  tff(c_543, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_537, c_4])).
% 3.47/1.55  tff(c_548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_63, c_543])).
% 3.47/1.55  tff(c_550, plain, (~v1_xboole_0('#skF_3')), inference(splitRight, [status(thm)], [c_530])).
% 3.47/1.55  tff(c_62, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_60, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_512, plain, (v1_partfun1('#skF_4', '#skF_2') | ~v1_funct_2('#skF_4', '#skF_2', '#skF_3') | ~v1_funct_1('#skF_4') | v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_58, c_503])).
% 3.47/1.55  tff(c_533, plain, (v1_partfun1('#skF_4', '#skF_2') | v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_62, c_60, c_512])).
% 3.47/1.55  tff(c_551, plain, (v1_partfun1('#skF_4', '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_550, c_533])).
% 3.47/1.55  tff(c_549, plain, (v1_partfun1('#skF_5', '#skF_2')), inference(splitRight, [status(thm)], [c_530])).
% 3.47/1.55  tff(c_50, plain, (r1_partfun1('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_579, plain, (![D_113, C_114, A_115, B_116]: (D_113=C_114 | ~r1_partfun1(C_114, D_113) | ~v1_partfun1(D_113, A_115) | ~v1_partfun1(C_114, A_115) | ~m1_subset_1(D_113, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(D_113) | ~m1_subset_1(C_114, k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1(C_114))), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.47/1.55  tff(c_581, plain, (![A_115, B_116]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_115) | ~v1_partfun1('#skF_4', A_115) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_50, c_579])).
% 3.47/1.55  tff(c_584, plain, (![A_115, B_116]: ('#skF_5'='#skF_4' | ~v1_partfun1('#skF_5', A_115) | ~v1_partfun1('#skF_4', A_115) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_115, B_116))))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_56, c_581])).
% 3.47/1.55  tff(c_686, plain, (![A_144, B_145]: (~v1_partfun1('#skF_5', A_144) | ~v1_partfun1('#skF_4', A_144) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(A_144, B_145))))), inference(splitLeft, [status(thm)], [c_584])).
% 3.47/1.55  tff(c_693, plain, (~v1_partfun1('#skF_5', '#skF_2') | ~v1_partfun1('#skF_4', '#skF_2') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(resolution, [status(thm)], [c_52, c_686])).
% 3.47/1.55  tff(c_706, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_551, c_549, c_693])).
% 3.47/1.55  tff(c_707, plain, ('#skF_5'='#skF_4'), inference(splitRight, [status(thm)], [c_584])).
% 3.47/1.55  tff(c_46, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_145])).
% 3.47/1.55  tff(c_716, plain, (~r2_relset_1('#skF_2', '#skF_3', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_707, c_46])).
% 3.47/1.55  tff(c_729, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_452, c_716])).
% 3.47/1.55  tff(c_731, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 3.47/1.55  tff(c_730, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.47/1.55  tff(c_737, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_731, c_730])).
% 3.47/1.55  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 3.47/1.55  tff(c_732, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_730, c_2])).
% 3.47/1.55  tff(c_743, plain, (v1_xboole_0('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_732])).
% 3.47/1.55  tff(c_10, plain, (![B_3]: (k2_zfmisc_1(k1_xboole_0, B_3)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 3.47/1.55  tff(c_757, plain, (![B_3]: (k2_zfmisc_1('#skF_3', B_3)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_731, c_731, c_10])).
% 3.47/1.55  tff(c_785, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_757, c_737, c_58])).
% 3.47/1.55  tff(c_787, plain, (![B_152, A_153]: (v1_xboole_0(B_152) | ~m1_subset_1(B_152, k1_zfmisc_1(A_153)) | ~v1_xboole_0(A_153))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.47/1.55  tff(c_793, plain, (v1_xboole_0('#skF_4') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_785, c_787])).
% 3.47/1.55  tff(c_805, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_743, c_793])).
% 3.47/1.55  tff(c_749, plain, (![A_1]: (A_1='#skF_3' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_4])).
% 3.47/1.55  tff(c_828, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_805, c_749])).
% 3.47/1.55  tff(c_12, plain, (![A_4]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_4)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.47/1.55  tff(c_765, plain, (![A_4]: (m1_subset_1('#skF_3', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_731, c_12])).
% 3.47/1.55  tff(c_846, plain, (![A_4]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_4)))), inference(demodulation, [status(thm), theory('equality')], [c_828, c_765])).
% 3.47/1.55  tff(c_18, plain, (![A_8]: (m1_subset_1('#skF_1'(A_8), k1_zfmisc_1(A_8)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.47/1.55  tff(c_1183, plain, (![A_208, B_209, C_210, D_211]: (r2_relset_1(A_208, B_209, C_210, C_210) | ~m1_subset_1(D_211, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))) | ~m1_subset_1(C_210, k1_zfmisc_1(k2_zfmisc_1(A_208, B_209))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.47/1.55  tff(c_1199, plain, (![A_212, B_213, C_214]: (r2_relset_1(A_212, B_213, C_214, C_214) | ~m1_subset_1(C_214, k1_zfmisc_1(k2_zfmisc_1(A_212, B_213))))), inference(resolution, [status(thm)], [c_18, c_1183])).
% 3.47/1.55  tff(c_1213, plain, (![A_212, B_213]: (r2_relset_1(A_212, B_213, '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_846, c_1199])).
% 3.47/1.55  tff(c_786, plain, (m1_subset_1('#skF_5', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_757, c_737, c_52])).
% 3.47/1.55  tff(c_790, plain, (v1_xboole_0('#skF_5') | ~v1_xboole_0('#skF_3')), inference(resolution, [status(thm)], [c_786, c_787])).
% 3.47/1.55  tff(c_802, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_743, c_790])).
% 3.47/1.55  tff(c_812, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_802, c_749])).
% 3.47/1.55  tff(c_783, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_737, c_46])).
% 3.47/1.55  tff(c_831, plain, (~r2_relset_1('#skF_3', '#skF_3', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_812, c_783])).
% 3.47/1.55  tff(c_940, plain, (~r2_relset_1('#skF_4', '#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_828, c_828, c_828, c_831])).
% 3.47/1.55  tff(c_1217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1213, c_940])).
% 3.47/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.47/1.55  
% 3.47/1.55  Inference rules
% 3.47/1.55  ----------------------
% 3.47/1.55  #Ref     : 0
% 3.47/1.55  #Sup     : 250
% 3.47/1.55  #Fact    : 0
% 3.47/1.55  #Define  : 0
% 3.47/1.55  #Split   : 5
% 3.47/1.55  #Chain   : 0
% 3.47/1.55  #Close   : 0
% 3.47/1.55  
% 3.47/1.55  Ordering : KBO
% 3.47/1.55  
% 3.47/1.55  Simplification rules
% 3.47/1.55  ----------------------
% 3.47/1.55  #Subsume      : 36
% 3.47/1.55  #Demod        : 249
% 3.47/1.55  #Tautology    : 130
% 3.47/1.55  #SimpNegUnit  : 2
% 3.47/1.55  #BackRed      : 37
% 3.47/1.55  
% 3.47/1.55  #Partial instantiations: 0
% 3.47/1.55  #Strategies tried      : 1
% 3.47/1.55  
% 3.47/1.55  Timing (in seconds)
% 3.47/1.55  ----------------------
% 3.47/1.56  Preprocessing        : 0.34
% 3.47/1.56  Parsing              : 0.19
% 3.47/1.56  CNF conversion       : 0.02
% 3.47/1.56  Main loop            : 0.42
% 3.47/1.56  Inferencing          : 0.16
% 3.47/1.56  Reduction            : 0.14
% 3.47/1.56  Demodulation         : 0.10
% 3.47/1.56  BG Simplification    : 0.02
% 3.47/1.56  Subsumption          : 0.06
% 3.47/1.56  Abstraction          : 0.02
% 3.47/1.56  MUC search           : 0.00
% 3.47/1.56  Cooper               : 0.00
% 3.47/1.56  Total                : 0.80
% 3.47/1.56  Index Insertion      : 0.00
% 3.47/1.56  Index Deletion       : 0.00
% 3.47/1.56  Index Matching       : 0.00
% 3.47/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------
