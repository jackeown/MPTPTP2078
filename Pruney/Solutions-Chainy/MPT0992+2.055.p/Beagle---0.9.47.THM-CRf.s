%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:39 EST 2020

% Result     : Theorem 6.50s
% Output     : CNFRefutation 6.50s
% Verified   : 
% Statistics : Number of formulae       :  158 (2710 expanded)
%              Number of leaves         :   35 ( 848 expanded)
%              Depth                    :   15
%              Number of atoms          :  252 (8514 expanded)
%              Number of equality atoms :   81 (3430 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_131,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(C,A)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(k2_partfun1(A,B,D,C))
              & v1_funct_2(k2_partfun1(A,B,D,C),C,B)
              & m1_subset_1(k2_partfun1(A,B,D,C),k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_funct_2)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_97,axiom,(
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
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_111,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_105,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_73,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C)))
     => ( r1_tarski(k1_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_relset_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_37,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => r1_tarski(k7_relat_1(B,A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_relat_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,C)))
     => ( r1_tarski(A,D)
       => m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_relset_1)).

tff(c_58,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_60,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_452,plain,(
    ! [C_91,A_92,B_93] :
      ( v1_relat_1(C_91)
      | ~ m1_subset_1(C_91,k1_zfmisc_1(k2_zfmisc_1(A_92,B_93))) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_465,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_452])).

tff(c_56,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_72,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_62,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4523,plain,(
    ! [A_475,B_476,C_477] :
      ( k1_relset_1(A_475,B_476,C_477) = k1_relat_1(C_477)
      | ~ m1_subset_1(C_477,k1_zfmisc_1(k2_zfmisc_1(A_475,B_476))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_4542,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_4523])).

tff(c_5029,plain,(
    ! [B_550,A_551,C_552] :
      ( k1_xboole_0 = B_550
      | k1_relset_1(A_551,B_550,C_552) = A_551
      | ~ v1_funct_2(C_552,A_551,B_550)
      | ~ m1_subset_1(C_552,k1_zfmisc_1(k2_zfmisc_1(A_551,B_550))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_5042,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_5029])).

tff(c_5058,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_4542,c_5042])).

tff(c_5059,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_5058])).

tff(c_26,plain,(
    ! [B_14,A_13] :
      ( k1_relat_1(k7_relat_1(B_14,A_13)) = A_13
      | ~ r1_tarski(A_13,k1_relat_1(B_14))
      | ~ v1_relat_1(B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_5078,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5059,c_26])).

tff(c_5175,plain,(
    ! [A_556] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_556)) = A_556
      | ~ r1_tarski(A_556,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_5078])).

tff(c_64,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_4822,plain,(
    ! [A_528,B_529,C_530,D_531] :
      ( k2_partfun1(A_528,B_529,C_530,D_531) = k7_relat_1(C_530,D_531)
      | ~ m1_subset_1(C_530,k1_zfmisc_1(k2_zfmisc_1(A_528,B_529)))
      | ~ v1_funct_1(C_530) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_4829,plain,(
    ! [D_531] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_531) = k7_relat_1('#skF_4',D_531)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_4822])).

tff(c_4840,plain,(
    ! [D_531] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_531) = k7_relat_1('#skF_4',D_531) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_4829])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_620,plain,(
    ! [A_110,B_111,C_112] :
      ( k1_relset_1(A_110,B_111,C_112) = k1_relat_1(C_112)
      | ~ m1_subset_1(C_112,k1_zfmisc_1(k2_zfmisc_1(A_110,B_111))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_635,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_60,c_620])).

tff(c_1176,plain,(
    ! [B_190,A_191,C_192] :
      ( k1_xboole_0 = B_190
      | k1_relset_1(A_191,B_190,C_192) = A_191
      | ~ v1_funct_2(C_192,A_191,B_190)
      | ~ m1_subset_1(C_192,k1_zfmisc_1(k2_zfmisc_1(A_191,B_190))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_1189,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_60,c_1176])).

tff(c_1204,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_635,c_1189])).

tff(c_1205,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_1204])).

tff(c_1225,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1205,c_26])).

tff(c_1231,plain,(
    ! [A_13] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_13)) = A_13
      | ~ r1_tarski(A_13,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_465,c_1225])).

tff(c_1112,plain,(
    ! [A_178,B_179,C_180,D_181] :
      ( k2_partfun1(A_178,B_179,C_180,D_181) = k7_relat_1(C_180,D_181)
      | ~ m1_subset_1(C_180,k1_zfmisc_1(k2_zfmisc_1(A_178,B_179)))
      | ~ v1_funct_1(C_180) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_1121,plain,(
    ! [D_181] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_181) = k7_relat_1('#skF_4',D_181)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_1112])).

tff(c_1134,plain,(
    ! [D_181] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_181) = k7_relat_1('#skF_4',D_181) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_1121])).

tff(c_1578,plain,(
    ! [A_219,B_220,C_221,D_222] :
      ( m1_subset_1(k2_partfun1(A_219,B_220,C_221,D_222),k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ m1_subset_1(C_221,k1_zfmisc_1(k2_zfmisc_1(A_219,B_220)))
      | ~ v1_funct_1(C_221) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_1602,plain,(
    ! [D_181] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_181),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1134,c_1578])).

tff(c_1621,plain,(
    ! [D_223] : m1_subset_1(k7_relat_1('#skF_4',D_223),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_60,c_1602])).

tff(c_32,plain,(
    ! [D_24,B_22,C_23,A_21] :
      ( m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(B_22,C_23)))
      | ~ r1_tarski(k1_relat_1(D_24),B_22)
      | ~ m1_subset_1(D_24,k1_zfmisc_1(k2_zfmisc_1(A_21,C_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_4225,plain,(
    ! [D_456,B_457] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_456),k1_zfmisc_1(k2_zfmisc_1(B_457,'#skF_2')))
      | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4',D_456)),B_457) ) ),
    inference(resolution,[status(thm)],[c_1621,c_32])).

tff(c_418,plain,(
    ! [A_86,B_87,C_88,D_89] :
      ( v1_funct_1(k2_partfun1(A_86,B_87,C_88,D_89))
      | ~ m1_subset_1(C_88,k1_zfmisc_1(k2_zfmisc_1(A_86,B_87)))
      | ~ v1_funct_1(C_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_423,plain,(
    ! [D_89] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_89))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_60,c_418])).

tff(c_431,plain,(
    ! [D_89] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_89)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_423])).

tff(c_54,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_144,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_449,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_431,c_144])).

tff(c_450,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_503,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_450])).

tff(c_1137,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1134,c_503])).

tff(c_4280,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_3') ),
    inference(resolution,[status(thm)],[c_4225,c_1137])).

tff(c_4334,plain,
    ( ~ r1_tarski('#skF_3','#skF_3')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_4280])).

tff(c_4337,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_6,c_4334])).

tff(c_4339,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_4540,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_4339,c_4523])).

tff(c_4848,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_4840,c_4540])).

tff(c_4338,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_450])).

tff(c_4853,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_4338])).

tff(c_4852,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_4339])).

tff(c_4974,plain,(
    ! [B_543,C_544,A_545] :
      ( k1_xboole_0 = B_543
      | v1_funct_2(C_544,A_545,B_543)
      | k1_relset_1(A_545,B_543,C_544) != A_545
      | ~ m1_subset_1(C_544,k1_zfmisc_1(k2_zfmisc_1(A_545,B_543))) ) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_4980,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_4852,c_4974])).

tff(c_4999,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_4853,c_72,c_4980])).

tff(c_5009,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4848,c_4999])).

tff(c_5184,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5175,c_5009])).

tff(c_5220,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_5184])).

tff(c_5221,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_14,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5235,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_5221,c_14])).

tff(c_5222,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_5228,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_5222])).

tff(c_5243,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5235,c_5228,c_60])).

tff(c_5290,plain,(
    ! [A_563,B_564] :
      ( r1_tarski(A_563,B_564)
      | ~ m1_subset_1(A_563,k1_zfmisc_1(B_564)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5294,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_5243,c_5290])).

tff(c_10,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ r1_tarski(A_4,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5266,plain,(
    ! [A_4] :
      ( A_4 = '#skF_1'
      | ~ r1_tarski(A_4,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_5221,c_10])).

tff(c_5298,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_5294,c_5266])).

tff(c_5229,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5228,c_62])).

tff(c_5306,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5298,c_5229])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_5223,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_8])).

tff(c_5307,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5223])).

tff(c_5244,plain,(
    ! [A_559,B_560] : v1_relat_1(k2_zfmisc_1(A_559,B_560)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_5246,plain,(
    v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5235,c_5244])).

tff(c_5303,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5246])).

tff(c_24,plain,(
    ! [B_12,A_11] :
      ( r1_tarski(k7_relat_1(B_12,A_11),B_12)
      | ~ v1_relat_1(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_5843,plain,(
    ! [A_639] :
      ( A_639 = '#skF_4'
      | ~ r1_tarski(A_639,'#skF_4') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5298,c_5266])).

tff(c_5851,plain,(
    ! [A_11] :
      ( k7_relat_1('#skF_4',A_11) = '#skF_4'
      | ~ v1_relat_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_24,c_5843])).

tff(c_5860,plain,(
    ! [A_11] : k7_relat_1('#skF_4',A_11) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5303,c_5851])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6247,plain,(
    ! [A_696,B_697,C_698,D_699] :
      ( m1_subset_1(A_696,k1_zfmisc_1(k2_zfmisc_1(B_697,C_698)))
      | ~ r1_tarski(A_696,D_699)
      | ~ m1_subset_1(D_699,k1_zfmisc_1(k2_zfmisc_1(B_697,C_698))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_6270,plain,(
    ! [B_711,C_712,A_713] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_711,C_712)))
      | ~ m1_subset_1(A_713,k1_zfmisc_1(k2_zfmisc_1(B_711,C_712))) ) ),
    inference(resolution,[status(thm)],[c_5307,c_6247])).

tff(c_6301,plain,(
    ! [B_717,C_718,A_719] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_717,C_718)))
      | ~ r1_tarski(A_719,k2_zfmisc_1(B_717,C_718)) ) ),
    inference(resolution,[status(thm)],[c_20,c_6270])).

tff(c_6315,plain,(
    ! [B_717,C_718] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1(B_717,C_718))) ),
    inference(resolution,[status(thm)],[c_5307,c_6301])).

tff(c_6391,plain,(
    ! [A_733,B_734,C_735,D_736] :
      ( k2_partfun1(A_733,B_734,C_735,D_736) = k7_relat_1(C_735,D_736)
      | ~ m1_subset_1(C_735,k1_zfmisc_1(k2_zfmisc_1(A_733,B_734)))
      | ~ v1_funct_1(C_735) ) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_6393,plain,(
    ! [B_717,C_718,D_736] :
      ( k2_partfun1(B_717,C_718,'#skF_4',D_736) = k7_relat_1('#skF_4',D_736)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6315,c_6391])).

tff(c_6403,plain,(
    ! [B_717,C_718,D_736] : k2_partfun1(B_717,C_718,'#skF_4',D_736) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5860,c_6393])).

tff(c_5305,plain,(
    ! [A_5] : k2_zfmisc_1(A_5,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5298,c_5235])).

tff(c_5308,plain,(
    '#skF_2' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5228])).

tff(c_5304,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5243])).

tff(c_16,plain,(
    ! [B_6] : k2_zfmisc_1(k1_xboole_0,B_6) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5247,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_1',B_6) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_5221,c_16])).

tff(c_5302,plain,(
    ! [B_6] : k2_zfmisc_1('#skF_4',B_6) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5298,c_5247])).

tff(c_5616,plain,(
    ! [A_601,B_602,C_603,D_604] :
      ( v1_funct_1(k2_partfun1(A_601,B_602,C_603,D_604))
      | ~ m1_subset_1(C_603,k1_zfmisc_1(k2_zfmisc_1(A_601,B_602)))
      | ~ v1_funct_1(C_603) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_5785,plain,(
    ! [B_631,C_632,D_633] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_631,C_632,D_633))
      | ~ m1_subset_1(C_632,k1_zfmisc_1('#skF_4'))
      | ~ v1_funct_1(C_632) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5302,c_5616])).

tff(c_5790,plain,(
    ! [B_631,D_633] :
      ( v1_funct_1(k2_partfun1('#skF_4',B_631,'#skF_4',D_633))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_5304,c_5785])).

tff(c_5794,plain,(
    ! [B_631,D_633] : v1_funct_1(k2_partfun1('#skF_4',B_631,'#skF_4',D_633)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_5790])).

tff(c_5267,plain,(
    ! [A_562] :
      ( A_562 = '#skF_1'
      | ~ r1_tarski(A_562,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5221,c_5221,c_10])).

tff(c_5283,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_58,c_5267])).

tff(c_5300,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5298,c_5283])).

tff(c_5319,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5300,c_5298,c_5300,c_5300,c_5298,c_5300,c_5300,c_5298,c_54])).

tff(c_5320,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5319])).

tff(c_5364,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5308,c_5320])).

tff(c_5797,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5794,c_5364])).

tff(c_5798,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),'#skF_4','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_2','#skF_4','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_5319])).

tff(c_5894,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4')
    | ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5305,c_5308,c_5308,c_5308,c_5308,c_5798])).

tff(c_5895,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5894])).

tff(c_5986,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_5895])).

tff(c_6406,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6403,c_5986])).

tff(c_6411,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_6406])).

tff(c_6413,plain,(
    m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_5894])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_6439,plain,(
    r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_6413,c_18])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6513,plain,
    ( k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(resolution,[status(thm)],[c_6439,c_2])).

tff(c_6521,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5307,c_6513])).

tff(c_6412,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4','#skF_4') ),
    inference(splitRight,[status(thm)],[c_5894])).

tff(c_6536,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5306,c_6521,c_6412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:34:30 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.50/2.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.31  
% 6.50/2.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.32  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.50/2.32  
% 6.50/2.32  %Foreground sorts:
% 6.50/2.32  
% 6.50/2.32  
% 6.50/2.32  %Background operators:
% 6.50/2.32  
% 6.50/2.32  
% 6.50/2.32  %Foreground operators:
% 6.50/2.32  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.50/2.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.50/2.32  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 6.50/2.32  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.50/2.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.50/2.32  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.50/2.32  tff('#skF_2', type, '#skF_2': $i).
% 6.50/2.32  tff('#skF_3', type, '#skF_3': $i).
% 6.50/2.32  tff('#skF_1', type, '#skF_1': $i).
% 6.50/2.32  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.50/2.32  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.50/2.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.50/2.32  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 6.50/2.32  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.50/2.32  tff('#skF_4', type, '#skF_4': $i).
% 6.50/2.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.50/2.32  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 6.50/2.32  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.50/2.32  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.50/2.32  
% 6.50/2.34  tff(f_131, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 6.50/2.34  tff(f_63, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 6.50/2.34  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.50/2.34  tff(f_97, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.50/2.34  tff(f_59, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 6.50/2.34  tff(f_111, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 6.50/2.34  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.50/2.34  tff(f_105, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 6.50/2.34  tff(f_73, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C))) => (r1_tarski(k1_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_relset_1)).
% 6.50/2.34  tff(f_43, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.50/2.34  tff(f_47, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.50/2.34  tff(f_37, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.50/2.34  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.50/2.34  tff(f_49, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 6.50/2.34  tff(f_53, axiom, (![A, B]: (v1_relat_1(B) => r1_tarski(k7_relat_1(B, A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_relat_1)).
% 6.50/2.34  tff(f_79, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, C))) => (r1_tarski(A, D) => m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(B, C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_relset_1)).
% 6.50/2.34  tff(c_58, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.50/2.34  tff(c_60, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.50/2.34  tff(c_452, plain, (![C_91, A_92, B_93]: (v1_relat_1(C_91) | ~m1_subset_1(C_91, k1_zfmisc_1(k2_zfmisc_1(A_92, B_93))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.50/2.34  tff(c_465, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_452])).
% 6.50/2.34  tff(c_56, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.50/2.34  tff(c_72, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_56])).
% 6.50/2.34  tff(c_62, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.50/2.34  tff(c_4523, plain, (![A_475, B_476, C_477]: (k1_relset_1(A_475, B_476, C_477)=k1_relat_1(C_477) | ~m1_subset_1(C_477, k1_zfmisc_1(k2_zfmisc_1(A_475, B_476))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.50/2.34  tff(c_4542, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_4523])).
% 6.50/2.34  tff(c_5029, plain, (![B_550, A_551, C_552]: (k1_xboole_0=B_550 | k1_relset_1(A_551, B_550, C_552)=A_551 | ~v1_funct_2(C_552, A_551, B_550) | ~m1_subset_1(C_552, k1_zfmisc_1(k2_zfmisc_1(A_551, B_550))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.50/2.34  tff(c_5042, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_5029])).
% 6.50/2.34  tff(c_5058, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_4542, c_5042])).
% 6.50/2.34  tff(c_5059, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_5058])).
% 6.50/2.34  tff(c_26, plain, (![B_14, A_13]: (k1_relat_1(k7_relat_1(B_14, A_13))=A_13 | ~r1_tarski(A_13, k1_relat_1(B_14)) | ~v1_relat_1(B_14))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.50/2.34  tff(c_5078, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_5059, c_26])).
% 6.50/2.34  tff(c_5175, plain, (![A_556]: (k1_relat_1(k7_relat_1('#skF_4', A_556))=A_556 | ~r1_tarski(A_556, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_5078])).
% 6.50/2.34  tff(c_64, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.50/2.34  tff(c_4822, plain, (![A_528, B_529, C_530, D_531]: (k2_partfun1(A_528, B_529, C_530, D_531)=k7_relat_1(C_530, D_531) | ~m1_subset_1(C_530, k1_zfmisc_1(k2_zfmisc_1(A_528, B_529))) | ~v1_funct_1(C_530))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.50/2.34  tff(c_4829, plain, (![D_531]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_531)=k7_relat_1('#skF_4', D_531) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_4822])).
% 6.50/2.34  tff(c_4840, plain, (![D_531]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_531)=k7_relat_1('#skF_4', D_531))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_4829])).
% 6.50/2.34  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.50/2.34  tff(c_620, plain, (![A_110, B_111, C_112]: (k1_relset_1(A_110, B_111, C_112)=k1_relat_1(C_112) | ~m1_subset_1(C_112, k1_zfmisc_1(k2_zfmisc_1(A_110, B_111))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 6.50/2.34  tff(c_635, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_60, c_620])).
% 6.50/2.34  tff(c_1176, plain, (![B_190, A_191, C_192]: (k1_xboole_0=B_190 | k1_relset_1(A_191, B_190, C_192)=A_191 | ~v1_funct_2(C_192, A_191, B_190) | ~m1_subset_1(C_192, k1_zfmisc_1(k2_zfmisc_1(A_191, B_190))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.50/2.34  tff(c_1189, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_60, c_1176])).
% 6.50/2.34  tff(c_1204, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_635, c_1189])).
% 6.50/2.34  tff(c_1205, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_72, c_1204])).
% 6.50/2.34  tff(c_1225, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1205, c_26])).
% 6.50/2.34  tff(c_1231, plain, (![A_13]: (k1_relat_1(k7_relat_1('#skF_4', A_13))=A_13 | ~r1_tarski(A_13, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_465, c_1225])).
% 6.50/2.34  tff(c_1112, plain, (![A_178, B_179, C_180, D_181]: (k2_partfun1(A_178, B_179, C_180, D_181)=k7_relat_1(C_180, D_181) | ~m1_subset_1(C_180, k1_zfmisc_1(k2_zfmisc_1(A_178, B_179))) | ~v1_funct_1(C_180))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.50/2.34  tff(c_1121, plain, (![D_181]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_181)=k7_relat_1('#skF_4', D_181) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_1112])).
% 6.50/2.34  tff(c_1134, plain, (![D_181]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_181)=k7_relat_1('#skF_4', D_181))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_1121])).
% 6.50/2.34  tff(c_1578, plain, (![A_219, B_220, C_221, D_222]: (m1_subset_1(k2_partfun1(A_219, B_220, C_221, D_222), k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~m1_subset_1(C_221, k1_zfmisc_1(k2_zfmisc_1(A_219, B_220))) | ~v1_funct_1(C_221))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.50/2.34  tff(c_1602, plain, (![D_181]: (m1_subset_1(k7_relat_1('#skF_4', D_181), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_1134, c_1578])).
% 6.50/2.34  tff(c_1621, plain, (![D_223]: (m1_subset_1(k7_relat_1('#skF_4', D_223), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_60, c_1602])).
% 6.50/2.34  tff(c_32, plain, (![D_24, B_22, C_23, A_21]: (m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(B_22, C_23))) | ~r1_tarski(k1_relat_1(D_24), B_22) | ~m1_subset_1(D_24, k1_zfmisc_1(k2_zfmisc_1(A_21, C_23))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 6.50/2.34  tff(c_4225, plain, (![D_456, B_457]: (m1_subset_1(k7_relat_1('#skF_4', D_456), k1_zfmisc_1(k2_zfmisc_1(B_457, '#skF_2'))) | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', D_456)), B_457))), inference(resolution, [status(thm)], [c_1621, c_32])).
% 6.50/2.34  tff(c_418, plain, (![A_86, B_87, C_88, D_89]: (v1_funct_1(k2_partfun1(A_86, B_87, C_88, D_89)) | ~m1_subset_1(C_88, k1_zfmisc_1(k2_zfmisc_1(A_86, B_87))) | ~v1_funct_1(C_88))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.50/2.34  tff(c_423, plain, (![D_89]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_89)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_60, c_418])).
% 6.50/2.34  tff(c_431, plain, (![D_89]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_89)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_423])).
% 6.50/2.34  tff(c_54, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_131])).
% 6.50/2.34  tff(c_144, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_54])).
% 6.50/2.34  tff(c_449, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_431, c_144])).
% 6.50/2.34  tff(c_450, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_54])).
% 6.50/2.34  tff(c_503, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_450])).
% 6.50/2.34  tff(c_1137, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1134, c_503])).
% 6.50/2.34  tff(c_4280, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_3')), inference(resolution, [status(thm)], [c_4225, c_1137])).
% 6.50/2.34  tff(c_4334, plain, (~r1_tarski('#skF_3', '#skF_3') | ~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1231, c_4280])).
% 6.50/2.34  tff(c_4337, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_6, c_4334])).
% 6.50/2.34  tff(c_4339, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_450])).
% 6.50/2.34  tff(c_4540, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_4339, c_4523])).
% 6.50/2.34  tff(c_4848, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_4840, c_4840, c_4540])).
% 6.50/2.34  tff(c_4338, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_450])).
% 6.50/2.34  tff(c_4853, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4840, c_4338])).
% 6.50/2.34  tff(c_4852, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4840, c_4339])).
% 6.50/2.34  tff(c_4974, plain, (![B_543, C_544, A_545]: (k1_xboole_0=B_543 | v1_funct_2(C_544, A_545, B_543) | k1_relset_1(A_545, B_543, C_544)!=A_545 | ~m1_subset_1(C_544, k1_zfmisc_1(k2_zfmisc_1(A_545, B_543))))), inference(cnfTransformation, [status(thm)], [f_97])).
% 6.50/2.34  tff(c_4980, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_4852, c_4974])).
% 6.50/2.34  tff(c_4999, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_4853, c_72, c_4980])).
% 6.50/2.34  tff(c_5009, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_4848, c_4999])).
% 6.50/2.34  tff(c_5184, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5175, c_5009])).
% 6.50/2.34  tff(c_5220, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_58, c_5184])).
% 6.50/2.34  tff(c_5221, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_56])).
% 6.50/2.34  tff(c_14, plain, (![A_5]: (k2_zfmisc_1(A_5, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.50/2.34  tff(c_5235, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_5221, c_14])).
% 6.50/2.34  tff(c_5222, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_56])).
% 6.50/2.34  tff(c_5228, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_5222])).
% 6.50/2.34  tff(c_5243, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5235, c_5228, c_60])).
% 6.50/2.34  tff(c_5290, plain, (![A_563, B_564]: (r1_tarski(A_563, B_564) | ~m1_subset_1(A_563, k1_zfmisc_1(B_564)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.50/2.34  tff(c_5294, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_5243, c_5290])).
% 6.50/2.34  tff(c_10, plain, (![A_4]: (k1_xboole_0=A_4 | ~r1_tarski(A_4, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 6.50/2.34  tff(c_5266, plain, (![A_4]: (A_4='#skF_1' | ~r1_tarski(A_4, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_5221, c_10])).
% 6.50/2.34  tff(c_5298, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_5294, c_5266])).
% 6.50/2.34  tff(c_5229, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5228, c_62])).
% 6.50/2.34  tff(c_5306, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5298, c_5229])).
% 6.50/2.34  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.50/2.34  tff(c_5223, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_8])).
% 6.50/2.34  tff(c_5307, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5223])).
% 6.50/2.34  tff(c_5244, plain, (![A_559, B_560]: (v1_relat_1(k2_zfmisc_1(A_559, B_560)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.50/2.34  tff(c_5246, plain, (v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5235, c_5244])).
% 6.50/2.34  tff(c_5303, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5246])).
% 6.50/2.34  tff(c_24, plain, (![B_12, A_11]: (r1_tarski(k7_relat_1(B_12, A_11), B_12) | ~v1_relat_1(B_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.50/2.34  tff(c_5843, plain, (![A_639]: (A_639='#skF_4' | ~r1_tarski(A_639, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5298, c_5266])).
% 6.50/2.34  tff(c_5851, plain, (![A_11]: (k7_relat_1('#skF_4', A_11)='#skF_4' | ~v1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_24, c_5843])).
% 6.50/2.34  tff(c_5860, plain, (![A_11]: (k7_relat_1('#skF_4', A_11)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5303, c_5851])).
% 6.50/2.34  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.50/2.34  tff(c_6247, plain, (![A_696, B_697, C_698, D_699]: (m1_subset_1(A_696, k1_zfmisc_1(k2_zfmisc_1(B_697, C_698))) | ~r1_tarski(A_696, D_699) | ~m1_subset_1(D_699, k1_zfmisc_1(k2_zfmisc_1(B_697, C_698))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.50/2.34  tff(c_6270, plain, (![B_711, C_712, A_713]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_711, C_712))) | ~m1_subset_1(A_713, k1_zfmisc_1(k2_zfmisc_1(B_711, C_712))))), inference(resolution, [status(thm)], [c_5307, c_6247])).
% 6.50/2.34  tff(c_6301, plain, (![B_717, C_718, A_719]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_717, C_718))) | ~r1_tarski(A_719, k2_zfmisc_1(B_717, C_718)))), inference(resolution, [status(thm)], [c_20, c_6270])).
% 6.50/2.34  tff(c_6315, plain, (![B_717, C_718]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1(B_717, C_718))))), inference(resolution, [status(thm)], [c_5307, c_6301])).
% 6.50/2.34  tff(c_6391, plain, (![A_733, B_734, C_735, D_736]: (k2_partfun1(A_733, B_734, C_735, D_736)=k7_relat_1(C_735, D_736) | ~m1_subset_1(C_735, k1_zfmisc_1(k2_zfmisc_1(A_733, B_734))) | ~v1_funct_1(C_735))), inference(cnfTransformation, [status(thm)], [f_111])).
% 6.50/2.34  tff(c_6393, plain, (![B_717, C_718, D_736]: (k2_partfun1(B_717, C_718, '#skF_4', D_736)=k7_relat_1('#skF_4', D_736) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_6315, c_6391])).
% 6.50/2.34  tff(c_6403, plain, (![B_717, C_718, D_736]: (k2_partfun1(B_717, C_718, '#skF_4', D_736)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5860, c_6393])).
% 6.50/2.34  tff(c_5305, plain, (![A_5]: (k2_zfmisc_1(A_5, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5298, c_5235])).
% 6.50/2.34  tff(c_5308, plain, ('#skF_2'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5228])).
% 6.50/2.34  tff(c_5304, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5243])).
% 6.50/2.34  tff(c_16, plain, (![B_6]: (k2_zfmisc_1(k1_xboole_0, B_6)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.50/2.34  tff(c_5247, plain, (![B_6]: (k2_zfmisc_1('#skF_1', B_6)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_5221, c_16])).
% 6.50/2.34  tff(c_5302, plain, (![B_6]: (k2_zfmisc_1('#skF_4', B_6)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5298, c_5247])).
% 6.50/2.34  tff(c_5616, plain, (![A_601, B_602, C_603, D_604]: (v1_funct_1(k2_partfun1(A_601, B_602, C_603, D_604)) | ~m1_subset_1(C_603, k1_zfmisc_1(k2_zfmisc_1(A_601, B_602))) | ~v1_funct_1(C_603))), inference(cnfTransformation, [status(thm)], [f_105])).
% 6.50/2.34  tff(c_5785, plain, (![B_631, C_632, D_633]: (v1_funct_1(k2_partfun1('#skF_4', B_631, C_632, D_633)) | ~m1_subset_1(C_632, k1_zfmisc_1('#skF_4')) | ~v1_funct_1(C_632))), inference(superposition, [status(thm), theory('equality')], [c_5302, c_5616])).
% 6.50/2.34  tff(c_5790, plain, (![B_631, D_633]: (v1_funct_1(k2_partfun1('#skF_4', B_631, '#skF_4', D_633)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_5304, c_5785])).
% 6.50/2.34  tff(c_5794, plain, (![B_631, D_633]: (v1_funct_1(k2_partfun1('#skF_4', B_631, '#skF_4', D_633)))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_5790])).
% 6.50/2.34  tff(c_5267, plain, (![A_562]: (A_562='#skF_1' | ~r1_tarski(A_562, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5221, c_5221, c_10])).
% 6.50/2.34  tff(c_5283, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_58, c_5267])).
% 6.50/2.34  tff(c_5300, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5298, c_5283])).
% 6.50/2.34  tff(c_5319, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5300, c_5298, c_5300, c_5300, c_5298, c_5300, c_5300, c_5298, c_54])).
% 6.50/2.34  tff(c_5320, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'))), inference(splitLeft, [status(thm)], [c_5319])).
% 6.50/2.34  tff(c_5364, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5308, c_5320])).
% 6.50/2.34  tff(c_5797, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5794, c_5364])).
% 6.50/2.34  tff(c_5798, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), '#skF_4', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_2', '#skF_4', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_2')))), inference(splitRight, [status(thm)], [c_5319])).
% 6.50/2.34  tff(c_5894, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4') | ~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5305, c_5308, c_5308, c_5308, c_5308, c_5798])).
% 6.50/2.34  tff(c_5895, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_5894])).
% 6.50/2.34  tff(c_5986, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_5895])).
% 6.50/2.34  tff(c_6406, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6403, c_5986])).
% 6.50/2.34  tff(c_6411, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_6406])).
% 6.50/2.34  tff(c_6413, plain, (m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(splitRight, [status(thm)], [c_5894])).
% 6.50/2.34  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.50/2.34  tff(c_6439, plain, (r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_6413, c_18])).
% 6.50/2.34  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.50/2.34  tff(c_6513, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(resolution, [status(thm)], [c_6439, c_2])).
% 6.50/2.34  tff(c_6521, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5307, c_6513])).
% 6.50/2.34  tff(c_6412, plain, (~v1_funct_2(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4', '#skF_4')), inference(splitRight, [status(thm)], [c_5894])).
% 6.50/2.34  tff(c_6536, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5306, c_6521, c_6412])).
% 6.50/2.34  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.50/2.34  
% 6.50/2.34  Inference rules
% 6.50/2.34  ----------------------
% 6.50/2.34  #Ref     : 0
% 6.50/2.34  #Sup     : 1463
% 6.50/2.34  #Fact    : 0
% 6.50/2.34  #Define  : 0
% 6.50/2.34  #Split   : 31
% 6.50/2.34  #Chain   : 0
% 6.50/2.34  #Close   : 0
% 6.50/2.34  
% 6.50/2.34  Ordering : KBO
% 6.50/2.34  
% 6.50/2.34  Simplification rules
% 6.50/2.34  ----------------------
% 6.50/2.34  #Subsume      : 234
% 6.50/2.34  #Demod        : 1178
% 6.50/2.34  #Tautology    : 583
% 6.50/2.34  #SimpNegUnit  : 40
% 6.50/2.34  #BackRed      : 60
% 6.50/2.34  
% 6.50/2.34  #Partial instantiations: 0
% 6.50/2.34  #Strategies tried      : 1
% 6.50/2.34  
% 6.50/2.34  Timing (in seconds)
% 6.50/2.34  ----------------------
% 6.50/2.34  Preprocessing        : 0.33
% 6.50/2.34  Parsing              : 0.17
% 6.50/2.34  CNF conversion       : 0.02
% 6.50/2.35  Main loop            : 1.22
% 6.50/2.35  Inferencing          : 0.42
% 6.50/2.35  Reduction            : 0.42
% 6.50/2.35  Demodulation         : 0.30
% 6.50/2.35  BG Simplification    : 0.05
% 6.50/2.35  Subsumption          : 0.23
% 6.50/2.35  Abstraction          : 0.05
% 6.50/2.35  MUC search           : 0.00
% 6.50/2.35  Cooper               : 0.00
% 6.50/2.35  Total                : 1.60
% 6.50/2.35  Index Insertion      : 0.00
% 6.50/2.35  Index Deletion       : 0.00
% 6.50/2.35  Index Matching       : 0.00
% 6.50/2.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------
