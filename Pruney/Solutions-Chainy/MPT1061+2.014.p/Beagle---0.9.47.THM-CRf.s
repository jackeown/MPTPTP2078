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
% DateTime   : Thu Dec  3 10:17:38 EST 2020

% Result     : Theorem 8.77s
% Output     : CNFRefutation 9.14s
% Verified   : 
% Statistics : Number of formulae       :  266 (1439 expanded)
%              Number of leaves         :   45 ( 446 expanded)
%              Depth                    :   15
%              Number of atoms          :  430 (4247 expanded)
%              Number of equality atoms :  164 ( 839 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k7_relset_1,type,(
    k7_relset_1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

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

tff(k2_partfun1,type,(
    k2_partfun1: ( $i * $i * $i * $i ) > $i )).

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_152,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ~ v1_xboole_0(D)
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,A,D)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,D))) )
           => ( ( r1_tarski(B,A)
                & r1_tarski(k7_relset_1(A,D,E,B),C) )
             => ( v1_funct_1(k2_partfun1(A,D,E,B))
                & v1_funct_2(k2_partfun1(A,D,E,B),B,C)
                & m1_subset_1(k2_partfun1(A,D,E,B),k1_zfmisc_1(k2_zfmisc_1(B,C))) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t178_funct_2)).

tff(f_63,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_51,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_117,axiom,(
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

tff(f_77,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_131,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_91,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k7_relset_1(A,B,C,D) = k9_relat_1(C,D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

tff(f_67,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( v1_relat_1(A)
     => v1_relat_1(k7_relat_1(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_relat_1)).

tff(f_99,axiom,(
    ! [A,B,C] :
      ( v1_relat_1(C)
     => ( ( r1_tarski(k1_relat_1(C),A)
          & r1_tarski(k2_relat_1(C),B) )
       => m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_relset_1)).

tff(f_125,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v4_relat_1(B,A)
      <=> r1_tarski(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

tff(c_78,plain,(
    ~ v1_xboole_0('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_70,plain,(
    r1_tarski('#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_30,plain,(
    ! [A_15,B_16] : v1_relat_1(k2_zfmisc_1(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_72,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_910,plain,(
    ! [B_144,A_145] :
      ( v1_relat_1(B_144)
      | ~ m1_subset_1(B_144,k1_zfmisc_1(A_145))
      | ~ v1_relat_1(A_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_916,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_910])).

tff(c_920,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_916])).

tff(c_74,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_10603,plain,(
    ! [A_926,B_927,C_928] :
      ( k1_relset_1(A_926,B_927,C_928) = k1_relat_1(C_928)
      | ~ m1_subset_1(C_928,k1_zfmisc_1(k2_zfmisc_1(A_926,B_927))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_10622,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_10603])).

tff(c_11404,plain,(
    ! [B_1007,A_1008,C_1009] :
      ( k1_xboole_0 = B_1007
      | k1_relset_1(A_1008,B_1007,C_1009) = A_1008
      | ~ v1_funct_2(C_1009,A_1008,B_1007)
      | ~ m1_subset_1(C_1009,k1_zfmisc_1(k2_zfmisc_1(A_1008,B_1007))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11417,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_11404])).

tff(c_11430,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10622,c_11417])).

tff(c_11432,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_11430])).

tff(c_36,plain,(
    ! [B_22,A_21] :
      ( k1_relat_1(k7_relat_1(B_22,A_21)) = A_21
      | ~ r1_tarski(A_21,k1_relat_1(B_22))
      | ~ v1_relat_1(B_22) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_11449,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11432,c_36])).

tff(c_11618,plain,(
    ! [A_1016] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1016)) = A_1016
      | ~ r1_tarski(A_1016,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_11449])).

tff(c_76,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_11109,plain,(
    ! [A_987,B_988,C_989,D_990] :
      ( k2_partfun1(A_987,B_988,C_989,D_990) = k7_relat_1(C_989,D_990)
      | ~ m1_subset_1(C_989,k1_zfmisc_1(k2_zfmisc_1(A_987,B_988)))
      | ~ v1_funct_1(C_989) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_11116,plain,(
    ! [D_990] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_990) = k7_relat_1('#skF_5',D_990)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_11109])).

tff(c_11127,plain,(
    ! [D_990] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_990) = k7_relat_1('#skF_5',D_990) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_11116])).

tff(c_8,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8657,plain,(
    ! [A_767,B_768,C_769] :
      ( k1_relset_1(A_767,B_768,C_769) = k1_relat_1(C_769)
      | ~ m1_subset_1(C_769,k1_zfmisc_1(k2_zfmisc_1(A_767,B_768))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_8672,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_8657])).

tff(c_9151,plain,(
    ! [B_829,A_830,C_831] :
      ( k1_xboole_0 = B_829
      | k1_relset_1(A_830,B_829,C_831) = A_830
      | ~ v1_funct_2(C_831,A_830,B_829)
      | ~ m1_subset_1(C_831,k1_zfmisc_1(k2_zfmisc_1(A_830,B_829))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_9161,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_9151])).

tff(c_9172,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_8672,c_9161])).

tff(c_9174,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_9172])).

tff(c_9185,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_9174,c_36])).

tff(c_9203,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_9185])).

tff(c_8854,plain,(
    ! [A_796,B_797,C_798,D_799] :
      ( k7_relset_1(A_796,B_797,C_798,D_799) = k9_relat_1(C_798,D_799)
      | ~ m1_subset_1(C_798,k1_zfmisc_1(k2_zfmisc_1(A_796,B_797))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_8866,plain,(
    ! [D_800] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_800) = k9_relat_1('#skF_5',D_800) ),
    inference(resolution,[status(thm)],[c_72,c_8854])).

tff(c_6806,plain,(
    ! [A_619,B_620,C_621] :
      ( k1_relset_1(A_619,B_620,C_621) = k1_relat_1(C_621)
      | ~ m1_subset_1(C_621,k1_zfmisc_1(k2_zfmisc_1(A_619,B_620))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_6825,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_6806])).

tff(c_7633,plain,(
    ! [B_702,A_703,C_704] :
      ( k1_xboole_0 = B_702
      | k1_relset_1(A_703,B_702,C_704) = A_703
      | ~ v1_funct_2(C_704,A_703,B_702)
      | ~ m1_subset_1(C_704,k1_zfmisc_1(k2_zfmisc_1(A_703,B_702))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7646,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_7633])).

tff(c_7660,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_6825,c_7646])).

tff(c_7662,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_7660])).

tff(c_7679,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7662,c_36])).

tff(c_7950,plain,(
    ! [A_719] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_719)) = A_719
      | ~ r1_tarski(A_719,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_7679])).

tff(c_7272,plain,(
    ! [A_675,B_676,C_677,D_678] :
      ( k2_partfun1(A_675,B_676,C_677,D_678) = k7_relat_1(C_677,D_678)
      | ~ m1_subset_1(C_677,k1_zfmisc_1(k2_zfmisc_1(A_675,B_676)))
      | ~ v1_funct_1(C_677) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_7279,plain,(
    ! [D_678] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_678) = k7_relat_1('#skF_5',D_678)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_7272])).

tff(c_7290,plain,(
    ! [D_678] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_678) = k7_relat_1('#skF_5',D_678) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_7279])).

tff(c_5133,plain,(
    ! [A_479,B_480,C_481] :
      ( k1_relset_1(A_479,B_480,C_481) = k1_relat_1(C_481)
      | ~ m1_subset_1(C_481,k1_zfmisc_1(k2_zfmisc_1(A_479,B_480))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_5148,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_5133])).

tff(c_5708,plain,(
    ! [B_552,A_553,C_554] :
      ( k1_xboole_0 = B_552
      | k1_relset_1(A_553,B_552,C_554) = A_553
      | ~ v1_funct_2(C_554,A_553,B_552)
      | ~ m1_subset_1(C_554,k1_zfmisc_1(k2_zfmisc_1(A_553,B_552))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_5718,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_5708])).

tff(c_5729,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_5148,c_5718])).

tff(c_5731,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5729])).

tff(c_5742,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5731,c_36])).

tff(c_5760,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_5742])).

tff(c_5159,plain,(
    ! [A_482,B_483,C_484,D_485] :
      ( k7_relset_1(A_482,B_483,C_484,D_485) = k9_relat_1(C_484,D_485)
      | ~ m1_subset_1(C_484,k1_zfmisc_1(k2_zfmisc_1(A_482,B_483))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_5170,plain,(
    ! [D_485] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_485) = k9_relat_1('#skF_5',D_485) ),
    inference(resolution,[status(thm)],[c_72,c_5159])).

tff(c_68,plain,(
    r1_tarski(k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_5173,plain,(
    r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5170,c_68])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( k2_relat_1(k7_relat_1(B_18,A_17)) = k9_relat_1(B_18,A_17)
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_28,plain,(
    ! [A_13,B_14] :
      ( v1_relat_1(k7_relat_1(A_13,B_14))
      | ~ v1_relat_1(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_5435,plain,(
    ! [C_526,A_527,B_528] :
      ( m1_subset_1(C_526,k1_zfmisc_1(k2_zfmisc_1(A_527,B_528)))
      | ~ r1_tarski(k2_relat_1(C_526),B_528)
      | ~ r1_tarski(k1_relat_1(C_526),A_527)
      | ~ v1_relat_1(C_526) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_5341,plain,(
    ! [A_512,B_513,C_514,D_515] :
      ( k2_partfun1(A_512,B_513,C_514,D_515) = k7_relat_1(C_514,D_515)
      | ~ m1_subset_1(C_514,k1_zfmisc_1(k2_zfmisc_1(A_512,B_513)))
      | ~ v1_funct_1(C_514) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_5346,plain,(
    ! [D_515] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_515) = k7_relat_1('#skF_5',D_515)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_5341])).

tff(c_5354,plain,(
    ! [D_515] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_515) = k7_relat_1('#skF_5',D_515) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_5346])).

tff(c_826,plain,(
    ! [A_134,B_135,C_136,D_137] :
      ( v1_funct_1(k2_partfun1(A_134,B_135,C_136,D_137))
      | ~ m1_subset_1(C_136,k1_zfmisc_1(k2_zfmisc_1(A_134,B_135)))
      | ~ v1_funct_1(C_136) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_831,plain,(
    ! [D_137] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_137))
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_826])).

tff(c_839,plain,(
    ! [D_137] : v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5',D_137)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_831])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_152])).

tff(c_126,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_842,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_839,c_126])).

tff(c_843,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_4672,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_5357,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5354,c_4672])).

tff(c_5466,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_5435,c_5357])).

tff(c_5629,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_5466])).

tff(c_5632,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_5629])).

tff(c_5636,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_5632])).

tff(c_5637,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_5466])).

tff(c_6203,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_5637])).

tff(c_6206,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_6203])).

tff(c_6209,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_5173,c_6206])).

tff(c_6210,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_5637])).

tff(c_6233,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_5760,c_6210])).

tff(c_6242,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8,c_6233])).

tff(c_6243,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_5729])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_6281,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6243,c_2])).

tff(c_6283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_6281])).

tff(c_6284,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_7301,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7290,c_6284])).

tff(c_6285,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_6823,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_6285,c_6806])).

tff(c_7294,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7290,c_7290,c_6823])).

tff(c_7300,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7290,c_6285])).

tff(c_7424,plain,(
    ! [B_685,C_686,A_687] :
      ( k1_xboole_0 = B_685
      | v1_funct_2(C_686,A_687,B_685)
      | k1_relset_1(A_687,B_685,C_686) != A_687
      | ~ m1_subset_1(C_686,k1_zfmisc_1(k2_zfmisc_1(A_687,B_685))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_7427,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_7300,c_7424])).

tff(c_7445,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7294,c_7427])).

tff(c_7446,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_7301,c_7445])).

tff(c_7452,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_7446])).

tff(c_7965,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_7950,c_7452])).

tff(c_8039,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_7965])).

tff(c_8040,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_7660])).

tff(c_8080,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8040,c_2])).

tff(c_8082,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_8080])).

tff(c_8083,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_7446])).

tff(c_10,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_8128,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8083,c_10])).

tff(c_7020,plain,(
    ! [A_647,B_648,C_649,D_650] :
      ( k7_relset_1(A_647,B_648,C_649,D_650) = k9_relat_1(C_649,D_650)
      | ~ m1_subset_1(C_649,k1_zfmisc_1(k2_zfmisc_1(A_647,B_648))) ) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_7034,plain,(
    ! [D_650] : k7_relset_1('#skF_1','#skF_4','#skF_5',D_650) = k9_relat_1('#skF_5',D_650) ),
    inference(resolution,[status(thm)],[c_72,c_7020])).

tff(c_845,plain,(
    ! [B_138,A_139] :
      ( B_138 = A_139
      | ~ r1_tarski(B_138,A_139)
      | ~ r1_tarski(A_139,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_859,plain,
    ( k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3'
    | ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_68,c_845])).

tff(c_921,plain,(
    ~ r1_tarski('#skF_3',k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_859])).

tff(c_7036,plain,(
    ~ r1_tarski('#skF_3',k9_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7034,c_921])).

tff(c_8144,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8128,c_7036])).

tff(c_8145,plain,(
    k7_relset_1('#skF_1','#skF_4','#skF_5','#skF_2') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_859])).

tff(c_8872,plain,(
    k9_relat_1('#skF_5','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_8866,c_8145])).

tff(c_9013,plain,(
    ! [C_818,A_819,B_820] :
      ( m1_subset_1(C_818,k1_zfmisc_1(k2_zfmisc_1(A_819,B_820)))
      | ~ r1_tarski(k2_relat_1(C_818),B_820)
      | ~ r1_tarski(k1_relat_1(C_818),A_819)
      | ~ v1_relat_1(C_818) ) ),
    inference(cnfTransformation,[status(thm)],[f_99])).

tff(c_8949,plain,(
    ! [A_810,B_811,C_812,D_813] :
      ( k2_partfun1(A_810,B_811,C_812,D_813) = k7_relat_1(C_812,D_813)
      | ~ m1_subset_1(C_812,k1_zfmisc_1(k2_zfmisc_1(A_810,B_811)))
      | ~ v1_funct_1(C_812) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_8954,plain,(
    ! [D_813] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_813) = k7_relat_1('#skF_5',D_813)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_8949])).

tff(c_8962,plain,(
    ! [D_813] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_813) = k7_relat_1('#skF_5',D_813) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_8954])).

tff(c_8169,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitLeft,[status(thm)],[c_843])).

tff(c_8965,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8962,c_8169])).

tff(c_9044,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3')
    | ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_9013,c_8965])).

tff(c_9078,plain,(
    ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_9044])).

tff(c_9081,plain,(
    ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_28,c_9078])).

tff(c_9085,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_9081])).

tff(c_9086,plain,
    ( ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2')
    | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitRight,[status(thm)],[c_9044])).

tff(c_9983,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_9086])).

tff(c_9986,plain,
    ( ~ r1_tarski(k9_relat_1('#skF_5','#skF_2'),'#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_9983])).

tff(c_9989,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_8,c_8872,c_9986])).

tff(c_9990,plain,(
    ~ r1_tarski(k1_relat_1(k7_relat_1('#skF_5','#skF_2')),'#skF_2') ),
    inference(splitRight,[status(thm)],[c_9086])).

tff(c_10006,plain,
    ( ~ r1_tarski('#skF_2','#skF_2')
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_9203,c_9990])).

tff(c_10015,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_8,c_10006])).

tff(c_10016,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_9172])).

tff(c_10053,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10016,c_2])).

tff(c_10055,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_10053])).

tff(c_10056,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_11138,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11127,c_10056])).

tff(c_10057,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_843])).

tff(c_10620,plain,(
    k1_relset_1('#skF_2','#skF_3',k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) = k1_relat_1(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10057,c_10603])).

tff(c_11131,plain,(
    k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) = k1_relat_1(k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11127,c_11127,c_10620])).

tff(c_11137,plain,(
    m1_subset_1(k7_relat_1('#skF_5','#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11127,c_10057])).

tff(c_11578,plain,(
    ! [B_1013,C_1014,A_1015] :
      ( k1_xboole_0 = B_1013
      | v1_funct_2(C_1014,A_1015,B_1013)
      | k1_relset_1(A_1015,B_1013,C_1014) != A_1015
      | ~ m1_subset_1(C_1014,k1_zfmisc_1(k2_zfmisc_1(A_1015,B_1013))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_11581,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_11137,c_11578])).

tff(c_11599,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k7_relat_1('#skF_5','#skF_2'),'#skF_2','#skF_3')
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11131,c_11581])).

tff(c_11600,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_11138,c_11599])).

tff(c_11617,plain,(
    k1_relat_1(k7_relat_1('#skF_5','#skF_2')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_11600])).

tff(c_11624,plain,(
    ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11618,c_11617])).

tff(c_11700,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11624])).

tff(c_11701,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_11600])).

tff(c_11744,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_10])).

tff(c_14,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11743,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11701,c_11701,c_14])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10265,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2'),k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_10057,c_18])).

tff(c_4,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_10361,plain,
    ( k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3')
    | ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10265,c_4])).

tff(c_10586,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_10361])).

tff(c_11132,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_2','#skF_3'),k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11127,c_10586])).

tff(c_11920,plain,(
    ~ r1_tarski('#skF_3',k7_relat_1('#skF_5','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11743,c_11132])).

tff(c_11924,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11744,c_11920])).

tff(c_11925,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_11430])).

tff(c_11964,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11925,c_2])).

tff(c_11966,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_11964])).

tff(c_11967,plain,(
    k2_partfun1('#skF_1','#skF_4','#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_10361])).

tff(c_11974,plain,(
    ~ v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_10056])).

tff(c_20,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_11984,plain,(
    ! [A_1027,B_1028,C_1029] :
      ( k1_relset_1(A_1027,B_1028,C_1029) = k1_relat_1(C_1029)
      | ~ m1_subset_1(C_1029,k1_zfmisc_1(k2_zfmisc_1(A_1027,B_1028))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_12499,plain,(
    ! [A_1084,B_1085,A_1086] :
      ( k1_relset_1(A_1084,B_1085,A_1086) = k1_relat_1(A_1086)
      | ~ r1_tarski(A_1086,k2_zfmisc_1(A_1084,B_1085)) ) ),
    inference(resolution,[status(thm)],[c_20,c_11984])).

tff(c_12529,plain,(
    ! [A_1084,B_1085] : k1_relset_1(A_1084,B_1085,k2_zfmisc_1(A_1084,B_1085)) = k1_relat_1(k2_zfmisc_1(A_1084,B_1085)) ),
    inference(resolution,[status(thm)],[c_8,c_12499])).

tff(c_11973,plain,(
    m1_subset_1(k2_zfmisc_1('#skF_2','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11967,c_10057])).

tff(c_12834,plain,(
    ! [B_1113,C_1114,A_1115] :
      ( k1_xboole_0 = B_1113
      | v1_funct_2(C_1114,A_1115,B_1113)
      | k1_relset_1(A_1115,B_1113,C_1114) != A_1115
      | ~ m1_subset_1(C_1114,k1_zfmisc_1(k2_zfmisc_1(A_1115,B_1113))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12840,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relset_1('#skF_2','#skF_3',k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(resolution,[status(thm)],[c_11973,c_12834])).

tff(c_12856,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2(k2_zfmisc_1('#skF_2','#skF_3'),'#skF_2','#skF_3')
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12529,c_12840])).

tff(c_12857,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_11974,c_12856])).

tff(c_12862,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_12857])).

tff(c_12413,plain,(
    ! [A_1078,B_1079,C_1080,D_1081] :
      ( k2_partfun1(A_1078,B_1079,C_1080,D_1081) = k7_relat_1(C_1080,D_1081)
      | ~ m1_subset_1(C_1080,k1_zfmisc_1(k2_zfmisc_1(A_1078,B_1079)))
      | ~ v1_funct_1(C_1080) ) ),
    inference(cnfTransformation,[status(thm)],[f_131])).

tff(c_12420,plain,(
    ! [D_1081] :
      ( k2_partfun1('#skF_1','#skF_4','#skF_5',D_1081) = k7_relat_1('#skF_5',D_1081)
      | ~ v1_funct_1('#skF_5') ) ),
    inference(resolution,[status(thm)],[c_72,c_12413])).

tff(c_12433,plain,(
    ! [D_1082] : k2_partfun1('#skF_1','#skF_4','#skF_5',D_1082) = k7_relat_1('#skF_5',D_1082) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12420])).

tff(c_12439,plain,(
    k7_relat_1('#skF_5','#skF_2') = k2_zfmisc_1('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_12433,c_11967])).

tff(c_11999,plain,(
    k1_relset_1('#skF_1','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_72,c_11984])).

tff(c_12964,plain,(
    ! [B_1124,A_1125,C_1126] :
      ( k1_xboole_0 = B_1124
      | k1_relset_1(A_1125,B_1124,C_1126) = A_1125
      | ~ v1_funct_2(C_1126,A_1125,B_1124)
      | ~ m1_subset_1(C_1126,k1_zfmisc_1(k2_zfmisc_1(A_1125,B_1124))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12977,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relset_1('#skF_1','#skF_4','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_12964])).

tff(c_12991,plain,
    ( k1_xboole_0 = '#skF_4'
    | k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_11999,c_12977])).

tff(c_12993,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_12991])).

tff(c_13019,plain,(
    ! [A_21] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_21)) = A_21
      | ~ r1_tarski(A_21,'#skF_1')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12993,c_36])).

tff(c_13361,plain,(
    ! [A_1142] :
      ( k1_relat_1(k7_relat_1('#skF_5',A_1142)) = A_1142
      | ~ r1_tarski(A_1142,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_920,c_13019])).

tff(c_13439,plain,
    ( k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2'
    | ~ r1_tarski('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12439,c_13361])).

tff(c_13496,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_13439])).

tff(c_13498,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12862,c_13496])).

tff(c_13499,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_12991])).

tff(c_13605,plain,(
    v1_xboole_0('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13499,c_2])).

tff(c_13607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_78,c_13605])).

tff(c_13608,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_12857])).

tff(c_16,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_10125,plain,(
    ! [C_893,A_894,B_895] :
      ( v4_relat_1(C_893,A_894)
      | ~ m1_subset_1(C_893,k1_zfmisc_1(k2_zfmisc_1(A_894,B_895))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10164,plain,(
    ! [A_904,A_905,B_906] :
      ( v4_relat_1(A_904,A_905)
      | ~ r1_tarski(A_904,k2_zfmisc_1(A_905,B_906)) ) ),
    inference(resolution,[status(thm)],[c_20,c_10125])).

tff(c_10189,plain,(
    ! [A_905,B_906] : v4_relat_1(k2_zfmisc_1(A_905,B_906),A_905) ),
    inference(resolution,[status(thm)],[c_8,c_10164])).

tff(c_10191,plain,(
    ! [B_907,A_908] :
      ( r1_tarski(k1_relat_1(B_907),A_908)
      | ~ v4_relat_1(B_907,A_908)
      | ~ v1_relat_1(B_907) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_866,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_10,c_845])).

tff(c_10228,plain,(
    ! [B_912] :
      ( k1_relat_1(B_912) = k1_xboole_0
      | ~ v4_relat_1(B_912,k1_xboole_0)
      | ~ v1_relat_1(B_912) ) ),
    inference(resolution,[status(thm)],[c_10191,c_866])).

tff(c_10232,plain,(
    ! [B_906] :
      ( k1_relat_1(k2_zfmisc_1(k1_xboole_0,B_906)) = k1_xboole_0
      | ~ v1_relat_1(k2_zfmisc_1(k1_xboole_0,B_906)) ) ),
    inference(resolution,[status(thm)],[c_10189,c_10228])).

tff(c_10243,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_16,c_10232])).

tff(c_48,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_36,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_81,plain,(
    ! [A_36] :
      ( v1_funct_2(k1_xboole_0,A_36,k1_xboole_0)
      | k1_xboole_0 = A_36
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_48])).

tff(c_10368,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_81])).

tff(c_10371,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_10368])).

tff(c_10375,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_10371])).

tff(c_10377,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_81])).

tff(c_12120,plain,(
    ! [B_1044,C_1045] :
      ( k1_relset_1(k1_xboole_0,B_1044,C_1045) = k1_relat_1(C_1045)
      | ~ m1_subset_1(C_1045,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_11984])).

tff(c_12122,plain,(
    ! [B_1044] : k1_relset_1(k1_xboole_0,B_1044,k1_xboole_0) = k1_relat_1(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10377,c_12120])).

tff(c_12127,plain,(
    ! [B_1044] : k1_relset_1(k1_xboole_0,B_1044,k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10243,c_12122])).

tff(c_52,plain,(
    ! [C_38,B_37] :
      ( v1_funct_2(C_38,k1_xboole_0,B_37)
      | k1_relset_1(k1_xboole_0,B_37,C_38) != k1_xboole_0
      | ~ m1_subset_1(C_38,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_37))) ) ),
    inference(cnfTransformation,[status(thm)],[f_117])).

tff(c_12274,plain,(
    ! [C_1065,B_1066] :
      ( v1_funct_2(C_1065,k1_xboole_0,B_1066)
      | k1_relset_1(k1_xboole_0,B_1066,C_1065) != k1_xboole_0
      | ~ m1_subset_1(C_1065,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_52])).

tff(c_12276,plain,(
    ! [B_1066] :
      ( v1_funct_2(k1_xboole_0,k1_xboole_0,B_1066)
      | k1_relset_1(k1_xboole_0,B_1066,k1_xboole_0) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10377,c_12274])).

tff(c_12282,plain,(
    ! [B_1066] : v1_funct_2(k1_xboole_0,k1_xboole_0,B_1066) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12127,c_12276])).

tff(c_13616,plain,(
    ! [B_1066] : v1_funct_2('#skF_3','#skF_3',B_1066) ),
    inference(demodulation,[status(thm),theory(equality)],[c_13608,c_13608,c_12282])).

tff(c_13632,plain,(
    k1_relat_1('#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13608,c_13608,c_10243])).

tff(c_13645,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13608,c_13608,c_14])).

tff(c_13609,plain,(
    k1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_12857])).

tff(c_13830,plain,(
    k1_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13645,c_13609])).

tff(c_13840,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13632,c_13830])).

tff(c_13837,plain,(
    ~ v1_funct_2('#skF_3','#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13645,c_11974])).

tff(c_14023,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13616,c_13840,c_13837])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.77/3.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.13/3.30  
% 9.13/3.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.13/3.30  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v1_xboole_0 > v1_relat_1 > v1_funct_1 > k7_relset_1 > k2_partfun1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 9.13/3.30  
% 9.13/3.30  %Foreground sorts:
% 9.13/3.30  
% 9.13/3.30  
% 9.13/3.30  %Background operators:
% 9.13/3.30  
% 9.13/3.30  
% 9.13/3.30  %Foreground operators:
% 9.13/3.30  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 9.13/3.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.13/3.30  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 9.13/3.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.13/3.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.13/3.30  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 9.13/3.30  tff(k7_relset_1, type, k7_relset_1: ($i * $i * $i * $i) > $i).
% 9.13/3.30  tff('#skF_5', type, '#skF_5': $i).
% 9.13/3.30  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 9.13/3.30  tff('#skF_2', type, '#skF_2': $i).
% 9.13/3.30  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 9.13/3.30  tff('#skF_3', type, '#skF_3': $i).
% 9.13/3.30  tff('#skF_1', type, '#skF_1': $i).
% 9.13/3.30  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 9.13/3.30  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 9.13/3.30  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 9.13/3.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.13/3.30  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 9.13/3.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 9.13/3.30  tff('#skF_4', type, '#skF_4': $i).
% 9.13/3.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.13/3.30  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 9.13/3.30  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 9.13/3.30  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 9.13/3.30  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 9.13/3.30  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 9.13/3.30  
% 9.14/3.33  tff(f_152, negated_conjecture, ~(![A, B, C, D]: (~v1_xboole_0(D) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, A, D)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, D)))) => ((r1_tarski(B, A) & r1_tarski(k7_relset_1(A, D, E, B), C)) => ((v1_funct_1(k2_partfun1(A, D, E, B)) & v1_funct_2(k2_partfun1(A, D, E, B), B, C)) & m1_subset_1(k2_partfun1(A, D, E, B), k1_zfmisc_1(k2_zfmisc_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t178_funct_2)).
% 9.14/3.33  tff(f_63, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 9.14/3.33  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 9.14/3.33  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 9.14/3.33  tff(f_117, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 9.14/3.33  tff(f_77, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_relat_1)).
% 9.14/3.33  tff(f_131, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 9.14/3.33  tff(f_32, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 9.14/3.33  tff(f_91, axiom, (![A, B, C, D]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k7_relset_1(A, B, C, D) = k9_relat_1(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k7_relset_1)).
% 9.14/3.33  tff(f_67, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 9.14/3.33  tff(f_61, axiom, (![A, B]: (v1_relat_1(A) => v1_relat_1(k7_relat_1(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k7_relat_1)).
% 9.14/3.33  tff(f_99, axiom, (![A, B, C]: (v1_relat_1(C) => ((r1_tarski(k1_relat_1(C), A) & r1_tarski(k2_relat_1(C), B)) => m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_relset_1)).
% 9.14/3.33  tff(f_125, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 9.14/3.33  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 9.14/3.33  tff(f_34, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 9.14/3.33  tff(f_40, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 9.14/3.33  tff(f_44, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_subset)).
% 9.14/3.33  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 9.14/3.33  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v4_relat_1(B, A) <=> r1_tarski(k1_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d18_relat_1)).
% 9.14/3.33  tff(c_78, plain, (~v1_xboole_0('#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.14/3.33  tff(c_70, plain, (r1_tarski('#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.14/3.33  tff(c_30, plain, (![A_15, B_16]: (v1_relat_1(k2_zfmisc_1(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 9.14/3.33  tff(c_72, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.14/3.33  tff(c_910, plain, (![B_144, A_145]: (v1_relat_1(B_144) | ~m1_subset_1(B_144, k1_zfmisc_1(A_145)) | ~v1_relat_1(A_145))), inference(cnfTransformation, [status(thm)], [f_51])).
% 9.14/3.33  tff(c_916, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_910])).
% 9.14/3.33  tff(c_920, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_916])).
% 9.14/3.33  tff(c_74, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.14/3.33  tff(c_10603, plain, (![A_926, B_927, C_928]: (k1_relset_1(A_926, B_927, C_928)=k1_relat_1(C_928) | ~m1_subset_1(C_928, k1_zfmisc_1(k2_zfmisc_1(A_926, B_927))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.14/3.33  tff(c_10622, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_10603])).
% 9.14/3.33  tff(c_11404, plain, (![B_1007, A_1008, C_1009]: (k1_xboole_0=B_1007 | k1_relset_1(A_1008, B_1007, C_1009)=A_1008 | ~v1_funct_2(C_1009, A_1008, B_1007) | ~m1_subset_1(C_1009, k1_zfmisc_1(k2_zfmisc_1(A_1008, B_1007))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_11417, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_11404])).
% 9.14/3.33  tff(c_11430, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10622, c_11417])).
% 9.14/3.33  tff(c_11432, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_11430])).
% 9.14/3.33  tff(c_36, plain, (![B_22, A_21]: (k1_relat_1(k7_relat_1(B_22, A_21))=A_21 | ~r1_tarski(A_21, k1_relat_1(B_22)) | ~v1_relat_1(B_22))), inference(cnfTransformation, [status(thm)], [f_77])).
% 9.14/3.33  tff(c_11449, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_5', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_11432, c_36])).
% 9.14/3.33  tff(c_11618, plain, (![A_1016]: (k1_relat_1(k7_relat_1('#skF_5', A_1016))=A_1016 | ~r1_tarski(A_1016, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_11449])).
% 9.14/3.33  tff(c_76, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.14/3.33  tff(c_11109, plain, (![A_987, B_988, C_989, D_990]: (k2_partfun1(A_987, B_988, C_989, D_990)=k7_relat_1(C_989, D_990) | ~m1_subset_1(C_989, k1_zfmisc_1(k2_zfmisc_1(A_987, B_988))) | ~v1_funct_1(C_989))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.33  tff(c_11116, plain, (![D_990]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_990)=k7_relat_1('#skF_5', D_990) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_11109])).
% 9.14/3.33  tff(c_11127, plain, (![D_990]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_990)=k7_relat_1('#skF_5', D_990))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_11116])).
% 9.14/3.33  tff(c_8, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.14/3.33  tff(c_8657, plain, (![A_767, B_768, C_769]: (k1_relset_1(A_767, B_768, C_769)=k1_relat_1(C_769) | ~m1_subset_1(C_769, k1_zfmisc_1(k2_zfmisc_1(A_767, B_768))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.14/3.33  tff(c_8672, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_8657])).
% 9.14/3.33  tff(c_9151, plain, (![B_829, A_830, C_831]: (k1_xboole_0=B_829 | k1_relset_1(A_830, B_829, C_831)=A_830 | ~v1_funct_2(C_831, A_830, B_829) | ~m1_subset_1(C_831, k1_zfmisc_1(k2_zfmisc_1(A_830, B_829))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_9161, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_9151])).
% 9.14/3.33  tff(c_9172, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_8672, c_9161])).
% 9.14/3.33  tff(c_9174, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_9172])).
% 9.14/3.33  tff(c_9185, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_5', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_9174, c_36])).
% 9.14/3.33  tff(c_9203, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_5', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_9185])).
% 9.14/3.33  tff(c_8854, plain, (![A_796, B_797, C_798, D_799]: (k7_relset_1(A_796, B_797, C_798, D_799)=k9_relat_1(C_798, D_799) | ~m1_subset_1(C_798, k1_zfmisc_1(k2_zfmisc_1(A_796, B_797))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.14/3.33  tff(c_8866, plain, (![D_800]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_800)=k9_relat_1('#skF_5', D_800))), inference(resolution, [status(thm)], [c_72, c_8854])).
% 9.14/3.33  tff(c_6806, plain, (![A_619, B_620, C_621]: (k1_relset_1(A_619, B_620, C_621)=k1_relat_1(C_621) | ~m1_subset_1(C_621, k1_zfmisc_1(k2_zfmisc_1(A_619, B_620))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.14/3.33  tff(c_6825, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_6806])).
% 9.14/3.33  tff(c_7633, plain, (![B_702, A_703, C_704]: (k1_xboole_0=B_702 | k1_relset_1(A_703, B_702, C_704)=A_703 | ~v1_funct_2(C_704, A_703, B_702) | ~m1_subset_1(C_704, k1_zfmisc_1(k2_zfmisc_1(A_703, B_702))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_7646, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_7633])).
% 9.14/3.33  tff(c_7660, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_6825, c_7646])).
% 9.14/3.33  tff(c_7662, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_7660])).
% 9.14/3.33  tff(c_7679, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_5', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7662, c_36])).
% 9.14/3.33  tff(c_7950, plain, (![A_719]: (k1_relat_1(k7_relat_1('#skF_5', A_719))=A_719 | ~r1_tarski(A_719, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_7679])).
% 9.14/3.33  tff(c_7272, plain, (![A_675, B_676, C_677, D_678]: (k2_partfun1(A_675, B_676, C_677, D_678)=k7_relat_1(C_677, D_678) | ~m1_subset_1(C_677, k1_zfmisc_1(k2_zfmisc_1(A_675, B_676))) | ~v1_funct_1(C_677))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.33  tff(c_7279, plain, (![D_678]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_678)=k7_relat_1('#skF_5', D_678) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_7272])).
% 9.14/3.33  tff(c_7290, plain, (![D_678]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_678)=k7_relat_1('#skF_5', D_678))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_7279])).
% 9.14/3.33  tff(c_5133, plain, (![A_479, B_480, C_481]: (k1_relset_1(A_479, B_480, C_481)=k1_relat_1(C_481) | ~m1_subset_1(C_481, k1_zfmisc_1(k2_zfmisc_1(A_479, B_480))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.14/3.33  tff(c_5148, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_5133])).
% 9.14/3.33  tff(c_5708, plain, (![B_552, A_553, C_554]: (k1_xboole_0=B_552 | k1_relset_1(A_553, B_552, C_554)=A_553 | ~v1_funct_2(C_554, A_553, B_552) | ~m1_subset_1(C_554, k1_zfmisc_1(k2_zfmisc_1(A_553, B_552))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_5718, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_5708])).
% 9.14/3.33  tff(c_5729, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_5148, c_5718])).
% 9.14/3.33  tff(c_5731, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_5729])).
% 9.14/3.33  tff(c_5742, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_5', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_5731, c_36])).
% 9.14/3.33  tff(c_5760, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_5', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_5742])).
% 9.14/3.33  tff(c_5159, plain, (![A_482, B_483, C_484, D_485]: (k7_relset_1(A_482, B_483, C_484, D_485)=k9_relat_1(C_484, D_485) | ~m1_subset_1(C_484, k1_zfmisc_1(k2_zfmisc_1(A_482, B_483))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.14/3.33  tff(c_5170, plain, (![D_485]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_485)=k9_relat_1('#skF_5', D_485))), inference(resolution, [status(thm)], [c_72, c_5159])).
% 9.14/3.33  tff(c_68, plain, (r1_tarski(k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.14/3.33  tff(c_5173, plain, (r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5170, c_68])).
% 9.14/3.33  tff(c_32, plain, (![B_18, A_17]: (k2_relat_1(k7_relat_1(B_18, A_17))=k9_relat_1(B_18, A_17) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_67])).
% 9.14/3.33  tff(c_28, plain, (![A_13, B_14]: (v1_relat_1(k7_relat_1(A_13, B_14)) | ~v1_relat_1(A_13))), inference(cnfTransformation, [status(thm)], [f_61])).
% 9.14/3.33  tff(c_5435, plain, (![C_526, A_527, B_528]: (m1_subset_1(C_526, k1_zfmisc_1(k2_zfmisc_1(A_527, B_528))) | ~r1_tarski(k2_relat_1(C_526), B_528) | ~r1_tarski(k1_relat_1(C_526), A_527) | ~v1_relat_1(C_526))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.14/3.33  tff(c_5341, plain, (![A_512, B_513, C_514, D_515]: (k2_partfun1(A_512, B_513, C_514, D_515)=k7_relat_1(C_514, D_515) | ~m1_subset_1(C_514, k1_zfmisc_1(k2_zfmisc_1(A_512, B_513))) | ~v1_funct_1(C_514))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.33  tff(c_5346, plain, (![D_515]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_515)=k7_relat_1('#skF_5', D_515) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_5341])).
% 9.14/3.33  tff(c_5354, plain, (![D_515]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_515)=k7_relat_1('#skF_5', D_515))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_5346])).
% 9.14/3.33  tff(c_826, plain, (![A_134, B_135, C_136, D_137]: (v1_funct_1(k2_partfun1(A_134, B_135, C_136, D_137)) | ~m1_subset_1(C_136, k1_zfmisc_1(k2_zfmisc_1(A_134, B_135))) | ~v1_funct_1(C_136))), inference(cnfTransformation, [status(thm)], [f_125])).
% 9.14/3.33  tff(c_831, plain, (![D_137]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_137)) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_826])).
% 9.14/3.33  tff(c_839, plain, (![D_137]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_137)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_831])).
% 9.14/3.33  tff(c_66, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_152])).
% 9.14/3.33  tff(c_126, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_66])).
% 9.14/3.33  tff(c_842, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_839, c_126])).
% 9.14/3.33  tff(c_843, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_66])).
% 9.14/3.33  tff(c_4672, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_843])).
% 9.14/3.33  tff(c_5357, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_5354, c_4672])).
% 9.14/3.33  tff(c_5466, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_5435, c_5357])).
% 9.14/3.33  tff(c_5629, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_5466])).
% 9.14/3.33  tff(c_5632, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_5629])).
% 9.14/3.33  tff(c_5636, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_920, c_5632])).
% 9.14/3.33  tff(c_5637, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_5466])).
% 9.14/3.33  tff(c_6203, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_5637])).
% 9.14/3.33  tff(c_6206, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32, c_6203])).
% 9.14/3.33  tff(c_6209, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_920, c_5173, c_6206])).
% 9.14/3.33  tff(c_6210, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_5637])).
% 9.14/3.33  tff(c_6233, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_5760, c_6210])).
% 9.14/3.33  tff(c_6242, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_8, c_6233])).
% 9.14/3.33  tff(c_6243, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_5729])).
% 9.14/3.33  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 9.14/3.33  tff(c_6281, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6243, c_2])).
% 9.14/3.33  tff(c_6283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_6281])).
% 9.14/3.33  tff(c_6284, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_843])).
% 9.14/3.33  tff(c_7301, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_7290, c_6284])).
% 9.14/3.33  tff(c_6285, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_843])).
% 9.14/3.33  tff(c_6823, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_6285, c_6806])).
% 9.14/3.33  tff(c_7294, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7290, c_7290, c_6823])).
% 9.14/3.33  tff(c_7300, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_7290, c_6285])).
% 9.14/3.33  tff(c_7424, plain, (![B_685, C_686, A_687]: (k1_xboole_0=B_685 | v1_funct_2(C_686, A_687, B_685) | k1_relset_1(A_687, B_685, C_686)!=A_687 | ~m1_subset_1(C_686, k1_zfmisc_1(k2_zfmisc_1(A_687, B_685))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_7427, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_7300, c_7424])).
% 9.14/3.33  tff(c_7445, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_7294, c_7427])).
% 9.14/3.33  tff(c_7446, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_7301, c_7445])).
% 9.14/3.33  tff(c_7452, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_7446])).
% 9.14/3.33  tff(c_7965, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_7950, c_7452])).
% 9.14/3.33  tff(c_8039, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_7965])).
% 9.14/3.33  tff(c_8040, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_7660])).
% 9.14/3.33  tff(c_8080, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8040, c_2])).
% 9.14/3.33  tff(c_8082, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_8080])).
% 9.14/3.33  tff(c_8083, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_7446])).
% 9.14/3.33  tff(c_10, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_34])).
% 9.14/3.33  tff(c_8128, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_8083, c_10])).
% 9.14/3.33  tff(c_7020, plain, (![A_647, B_648, C_649, D_650]: (k7_relset_1(A_647, B_648, C_649, D_650)=k9_relat_1(C_649, D_650) | ~m1_subset_1(C_649, k1_zfmisc_1(k2_zfmisc_1(A_647, B_648))))), inference(cnfTransformation, [status(thm)], [f_91])).
% 9.14/3.33  tff(c_7034, plain, (![D_650]: (k7_relset_1('#skF_1', '#skF_4', '#skF_5', D_650)=k9_relat_1('#skF_5', D_650))), inference(resolution, [status(thm)], [c_72, c_7020])).
% 9.14/3.33  tff(c_845, plain, (![B_138, A_139]: (B_138=A_139 | ~r1_tarski(B_138, A_139) | ~r1_tarski(A_139, B_138))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.14/3.33  tff(c_859, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3' | ~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_68, c_845])).
% 9.14/3.33  tff(c_921, plain, (~r1_tarski('#skF_3', k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_859])).
% 9.14/3.33  tff(c_7036, plain, (~r1_tarski('#skF_3', k9_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_7034, c_921])).
% 9.14/3.33  tff(c_8144, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8128, c_7036])).
% 9.14/3.33  tff(c_8145, plain, (k7_relset_1('#skF_1', '#skF_4', '#skF_5', '#skF_2')='#skF_3'), inference(splitRight, [status(thm)], [c_859])).
% 9.14/3.33  tff(c_8872, plain, (k9_relat_1('#skF_5', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_8866, c_8145])).
% 9.14/3.33  tff(c_9013, plain, (![C_818, A_819, B_820]: (m1_subset_1(C_818, k1_zfmisc_1(k2_zfmisc_1(A_819, B_820))) | ~r1_tarski(k2_relat_1(C_818), B_820) | ~r1_tarski(k1_relat_1(C_818), A_819) | ~v1_relat_1(C_818))), inference(cnfTransformation, [status(thm)], [f_99])).
% 9.14/3.33  tff(c_8949, plain, (![A_810, B_811, C_812, D_813]: (k2_partfun1(A_810, B_811, C_812, D_813)=k7_relat_1(C_812, D_813) | ~m1_subset_1(C_812, k1_zfmisc_1(k2_zfmisc_1(A_810, B_811))) | ~v1_funct_1(C_812))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.33  tff(c_8954, plain, (![D_813]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_813)=k7_relat_1('#skF_5', D_813) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_8949])).
% 9.14/3.33  tff(c_8962, plain, (![D_813]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_813)=k7_relat_1('#skF_5', D_813))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_8954])).
% 9.14/3.33  tff(c_8169, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitLeft, [status(thm)], [c_843])).
% 9.14/3.33  tff(c_8965, plain, (~m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_8962, c_8169])).
% 9.14/3.33  tff(c_9044, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3') | ~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_9013, c_8965])).
% 9.14/3.33  tff(c_9078, plain, (~v1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_9044])).
% 9.14/3.33  tff(c_9081, plain, (~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_28, c_9078])).
% 9.14/3.33  tff(c_9085, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_920, c_9081])).
% 9.14/3.33  tff(c_9086, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2') | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitRight, [status(thm)], [c_9044])).
% 9.14/3.33  tff(c_9983, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_3')), inference(splitLeft, [status(thm)], [c_9086])).
% 9.14/3.33  tff(c_9986, plain, (~r1_tarski(k9_relat_1('#skF_5', '#skF_2'), '#skF_3') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_32, c_9983])).
% 9.14/3.33  tff(c_9989, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_920, c_8, c_8872, c_9986])).
% 9.14/3.33  tff(c_9990, plain, (~r1_tarski(k1_relat_1(k7_relat_1('#skF_5', '#skF_2')), '#skF_2')), inference(splitRight, [status(thm)], [c_9086])).
% 9.14/3.33  tff(c_10006, plain, (~r1_tarski('#skF_2', '#skF_2') | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_9203, c_9990])).
% 9.14/3.33  tff(c_10015, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_8, c_10006])).
% 9.14/3.33  tff(c_10016, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_9172])).
% 9.14/3.33  tff(c_10053, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10016, c_2])).
% 9.14/3.33  tff(c_10055, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_10053])).
% 9.14/3.33  tff(c_10056, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_843])).
% 9.14/3.33  tff(c_11138, plain, (~v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11127, c_10056])).
% 9.14/3.33  tff(c_10057, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(splitRight, [status(thm)], [c_843])).
% 9.14/3.33  tff(c_10620, plain, (k1_relset_1('#skF_2', '#skF_3', k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_10057, c_10603])).
% 9.14/3.33  tff(c_11131, plain, (k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))=k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11127, c_11127, c_10620])).
% 9.14/3.33  tff(c_11137, plain, (m1_subset_1(k7_relat_1('#skF_5', '#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11127, c_10057])).
% 9.14/3.33  tff(c_11578, plain, (![B_1013, C_1014, A_1015]: (k1_xboole_0=B_1013 | v1_funct_2(C_1014, A_1015, B_1013) | k1_relset_1(A_1015, B_1013, C_1014)!=A_1015 | ~m1_subset_1(C_1014, k1_zfmisc_1(k2_zfmisc_1(A_1015, B_1013))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_11581, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(resolution, [status(thm)], [c_11137, c_11578])).
% 9.14/3.33  tff(c_11599, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k7_relat_1('#skF_5', '#skF_2'), '#skF_2', '#skF_3') | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_11131, c_11581])).
% 9.14/3.33  tff(c_11600, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_11138, c_11599])).
% 9.14/3.33  tff(c_11617, plain, (k1_relat_1(k7_relat_1('#skF_5', '#skF_2'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_11600])).
% 9.14/3.33  tff(c_11624, plain, (~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11618, c_11617])).
% 9.14/3.33  tff(c_11700, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_11624])).
% 9.14/3.33  tff(c_11701, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_11600])).
% 9.14/3.33  tff(c_11744, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_10])).
% 9.14/3.33  tff(c_14, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.14/3.33  tff(c_11743, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11701, c_11701, c_14])).
% 9.14/3.33  tff(c_18, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.14/3.33  tff(c_10265, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'), k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_10057, c_18])).
% 9.14/3.33  tff(c_4, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 9.14/3.33  tff(c_10361, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3') | ~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(resolution, [status(thm)], [c_10265, c_4])).
% 9.14/3.33  tff(c_10586, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2'))), inference(splitLeft, [status(thm)], [c_10361])).
% 9.14/3.33  tff(c_11132, plain, (~r1_tarski(k2_zfmisc_1('#skF_2', '#skF_3'), k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11127, c_10586])).
% 9.14/3.33  tff(c_11920, plain, (~r1_tarski('#skF_3', k7_relat_1('#skF_5', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_11743, c_11132])).
% 9.14/3.33  tff(c_11924, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11744, c_11920])).
% 9.14/3.33  tff(c_11925, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_11430])).
% 9.14/3.33  tff(c_11964, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_11925, c_2])).
% 9.14/3.33  tff(c_11966, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_11964])).
% 9.14/3.33  tff(c_11967, plain, (k2_partfun1('#skF_1', '#skF_4', '#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_10361])).
% 9.14/3.33  tff(c_11974, plain, (~v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_10056])).
% 9.14/3.33  tff(c_20, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 9.14/3.33  tff(c_11984, plain, (![A_1027, B_1028, C_1029]: (k1_relset_1(A_1027, B_1028, C_1029)=k1_relat_1(C_1029) | ~m1_subset_1(C_1029, k1_zfmisc_1(k2_zfmisc_1(A_1027, B_1028))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 9.14/3.33  tff(c_12499, plain, (![A_1084, B_1085, A_1086]: (k1_relset_1(A_1084, B_1085, A_1086)=k1_relat_1(A_1086) | ~r1_tarski(A_1086, k2_zfmisc_1(A_1084, B_1085)))), inference(resolution, [status(thm)], [c_20, c_11984])).
% 9.14/3.33  tff(c_12529, plain, (![A_1084, B_1085]: (k1_relset_1(A_1084, B_1085, k2_zfmisc_1(A_1084, B_1085))=k1_relat_1(k2_zfmisc_1(A_1084, B_1085)))), inference(resolution, [status(thm)], [c_8, c_12499])).
% 9.14/3.33  tff(c_11973, plain, (m1_subset_1(k2_zfmisc_1('#skF_2', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_11967, c_10057])).
% 9.14/3.33  tff(c_12834, plain, (![B_1113, C_1114, A_1115]: (k1_xboole_0=B_1113 | v1_funct_2(C_1114, A_1115, B_1113) | k1_relset_1(A_1115, B_1113, C_1114)!=A_1115 | ~m1_subset_1(C_1114, k1_zfmisc_1(k2_zfmisc_1(A_1115, B_1113))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_12840, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relset_1('#skF_2', '#skF_3', k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(resolution, [status(thm)], [c_11973, c_12834])).
% 9.14/3.33  tff(c_12856, plain, (k1_xboole_0='#skF_3' | v1_funct_2(k2_zfmisc_1('#skF_2', '#skF_3'), '#skF_2', '#skF_3') | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12529, c_12840])).
% 9.14/3.33  tff(c_12857, plain, (k1_xboole_0='#skF_3' | k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_11974, c_12856])).
% 9.14/3.33  tff(c_12862, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))!='#skF_2'), inference(splitLeft, [status(thm)], [c_12857])).
% 9.14/3.33  tff(c_12413, plain, (![A_1078, B_1079, C_1080, D_1081]: (k2_partfun1(A_1078, B_1079, C_1080, D_1081)=k7_relat_1(C_1080, D_1081) | ~m1_subset_1(C_1080, k1_zfmisc_1(k2_zfmisc_1(A_1078, B_1079))) | ~v1_funct_1(C_1080))), inference(cnfTransformation, [status(thm)], [f_131])).
% 9.14/3.33  tff(c_12420, plain, (![D_1081]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1081)=k7_relat_1('#skF_5', D_1081) | ~v1_funct_1('#skF_5'))), inference(resolution, [status(thm)], [c_72, c_12413])).
% 9.14/3.33  tff(c_12433, plain, (![D_1082]: (k2_partfun1('#skF_1', '#skF_4', '#skF_5', D_1082)=k7_relat_1('#skF_5', D_1082))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12420])).
% 9.14/3.33  tff(c_12439, plain, (k7_relat_1('#skF_5', '#skF_2')=k2_zfmisc_1('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_12433, c_11967])).
% 9.14/3.33  tff(c_11999, plain, (k1_relset_1('#skF_1', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_72, c_11984])).
% 9.14/3.33  tff(c_12964, plain, (![B_1124, A_1125, C_1126]: (k1_xboole_0=B_1124 | k1_relset_1(A_1125, B_1124, C_1126)=A_1125 | ~v1_funct_2(C_1126, A_1125, B_1124) | ~m1_subset_1(C_1126, k1_zfmisc_1(k2_zfmisc_1(A_1125, B_1124))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_12977, plain, (k1_xboole_0='#skF_4' | k1_relset_1('#skF_1', '#skF_4', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_72, c_12964])).
% 9.14/3.33  tff(c_12991, plain, (k1_xboole_0='#skF_4' | k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_11999, c_12977])).
% 9.14/3.33  tff(c_12993, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(splitLeft, [status(thm)], [c_12991])).
% 9.14/3.33  tff(c_13019, plain, (![A_21]: (k1_relat_1(k7_relat_1('#skF_5', A_21))=A_21 | ~r1_tarski(A_21, '#skF_1') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_12993, c_36])).
% 9.14/3.33  tff(c_13361, plain, (![A_1142]: (k1_relat_1(k7_relat_1('#skF_5', A_1142))=A_1142 | ~r1_tarski(A_1142, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_920, c_13019])).
% 9.14/3.33  tff(c_13439, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2' | ~r1_tarski('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12439, c_13361])).
% 9.14/3.33  tff(c_13496, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_70, c_13439])).
% 9.14/3.33  tff(c_13498, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12862, c_13496])).
% 9.14/3.33  tff(c_13499, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_12991])).
% 9.14/3.33  tff(c_13605, plain, (v1_xboole_0('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13499, c_2])).
% 9.14/3.33  tff(c_13607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_78, c_13605])).
% 9.14/3.33  tff(c_13608, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_12857])).
% 9.14/3.33  tff(c_16, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_40])).
% 9.14/3.33  tff(c_10125, plain, (![C_893, A_894, B_895]: (v4_relat_1(C_893, A_894) | ~m1_subset_1(C_893, k1_zfmisc_1(k2_zfmisc_1(A_894, B_895))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 9.14/3.33  tff(c_10164, plain, (![A_904, A_905, B_906]: (v4_relat_1(A_904, A_905) | ~r1_tarski(A_904, k2_zfmisc_1(A_905, B_906)))), inference(resolution, [status(thm)], [c_20, c_10125])).
% 9.14/3.33  tff(c_10189, plain, (![A_905, B_906]: (v4_relat_1(k2_zfmisc_1(A_905, B_906), A_905))), inference(resolution, [status(thm)], [c_8, c_10164])).
% 9.14/3.33  tff(c_10191, plain, (![B_907, A_908]: (r1_tarski(k1_relat_1(B_907), A_908) | ~v4_relat_1(B_907, A_908) | ~v1_relat_1(B_907))), inference(cnfTransformation, [status(thm)], [f_57])).
% 9.14/3.33  tff(c_866, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_845])).
% 9.14/3.33  tff(c_10228, plain, (![B_912]: (k1_relat_1(B_912)=k1_xboole_0 | ~v4_relat_1(B_912, k1_xboole_0) | ~v1_relat_1(B_912))), inference(resolution, [status(thm)], [c_10191, c_866])).
% 9.14/3.33  tff(c_10232, plain, (![B_906]: (k1_relat_1(k2_zfmisc_1(k1_xboole_0, B_906))=k1_xboole_0 | ~v1_relat_1(k2_zfmisc_1(k1_xboole_0, B_906)))), inference(resolution, [status(thm)], [c_10189, c_10228])).
% 9.14/3.33  tff(c_10243, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_16, c_10232])).
% 9.14/3.33  tff(c_48, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_36, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_81, plain, (![A_36]: (v1_funct_2(k1_xboole_0, A_36, k1_xboole_0) | k1_xboole_0=A_36 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_48])).
% 9.14/3.33  tff(c_10368, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_81])).
% 9.14/3.33  tff(c_10371, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_10368])).
% 9.14/3.33  tff(c_10375, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_10371])).
% 9.14/3.33  tff(c_10377, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_81])).
% 9.14/3.33  tff(c_12120, plain, (![B_1044, C_1045]: (k1_relset_1(k1_xboole_0, B_1044, C_1045)=k1_relat_1(C_1045) | ~m1_subset_1(C_1045, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_11984])).
% 9.14/3.33  tff(c_12122, plain, (![B_1044]: (k1_relset_1(k1_xboole_0, B_1044, k1_xboole_0)=k1_relat_1(k1_xboole_0))), inference(resolution, [status(thm)], [c_10377, c_12120])).
% 9.14/3.33  tff(c_12127, plain, (![B_1044]: (k1_relset_1(k1_xboole_0, B_1044, k1_xboole_0)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10243, c_12122])).
% 9.14/3.33  tff(c_52, plain, (![C_38, B_37]: (v1_funct_2(C_38, k1_xboole_0, B_37) | k1_relset_1(k1_xboole_0, B_37, C_38)!=k1_xboole_0 | ~m1_subset_1(C_38, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_37))))), inference(cnfTransformation, [status(thm)], [f_117])).
% 9.14/3.33  tff(c_12274, plain, (![C_1065, B_1066]: (v1_funct_2(C_1065, k1_xboole_0, B_1066) | k1_relset_1(k1_xboole_0, B_1066, C_1065)!=k1_xboole_0 | ~m1_subset_1(C_1065, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_52])).
% 9.14/3.33  tff(c_12276, plain, (![B_1066]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1066) | k1_relset_1(k1_xboole_0, B_1066, k1_xboole_0)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_10377, c_12274])).
% 9.14/3.33  tff(c_12282, plain, (![B_1066]: (v1_funct_2(k1_xboole_0, k1_xboole_0, B_1066))), inference(demodulation, [status(thm), theory('equality')], [c_12127, c_12276])).
% 9.14/3.33  tff(c_13616, plain, (![B_1066]: (v1_funct_2('#skF_3', '#skF_3', B_1066))), inference(demodulation, [status(thm), theory('equality')], [c_13608, c_13608, c_12282])).
% 9.14/3.33  tff(c_13632, plain, (k1_relat_1('#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13608, c_13608, c_10243])).
% 9.14/3.33  tff(c_13645, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_3')='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13608, c_13608, c_14])).
% 9.14/3.33  tff(c_13609, plain, (k1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))='#skF_2'), inference(splitRight, [status(thm)], [c_12857])).
% 9.14/3.33  tff(c_13830, plain, (k1_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_13645, c_13609])).
% 9.14/3.33  tff(c_13840, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_13632, c_13830])).
% 9.14/3.33  tff(c_13837, plain, (~v1_funct_2('#skF_3', '#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_13645, c_11974])).
% 9.14/3.33  tff(c_14023, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13616, c_13840, c_13837])).
% 9.14/3.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 9.14/3.33  
% 9.14/3.33  Inference rules
% 9.14/3.33  ----------------------
% 9.14/3.33  #Ref     : 0
% 9.14/3.33  #Sup     : 2948
% 9.14/3.33  #Fact    : 0
% 9.14/3.33  #Define  : 0
% 9.14/3.33  #Split   : 85
% 9.14/3.33  #Chain   : 0
% 9.14/3.33  #Close   : 0
% 9.14/3.33  
% 9.14/3.33  Ordering : KBO
% 9.14/3.33  
% 9.14/3.33  Simplification rules
% 9.14/3.33  ----------------------
% 9.14/3.33  #Subsume      : 448
% 9.14/3.33  #Demod        : 3080
% 9.14/3.33  #Tautology    : 1242
% 9.14/3.33  #SimpNegUnit  : 124
% 9.14/3.33  #BackRed      : 561
% 9.14/3.33  
% 9.14/3.33  #Partial instantiations: 0
% 9.14/3.33  #Strategies tried      : 1
% 9.14/3.33  
% 9.14/3.33  Timing (in seconds)
% 9.14/3.33  ----------------------
% 9.14/3.34  Preprocessing        : 0.38
% 9.14/3.34  Parsing              : 0.20
% 9.14/3.34  CNF conversion       : 0.03
% 9.14/3.34  Main loop            : 2.08
% 9.14/3.34  Inferencing          : 0.67
% 9.14/3.34  Reduction            : 0.75
% 9.14/3.34  Demodulation         : 0.53
% 9.14/3.34  BG Simplification    : 0.08
% 9.14/3.34  Subsumption          : 0.40
% 9.14/3.34  Abstraction          : 0.09
% 9.14/3.34  MUC search           : 0.00
% 9.14/3.34  Cooper               : 0.00
% 9.14/3.34  Total                : 2.55
% 9.14/3.34  Index Insertion      : 0.00
% 9.14/3.34  Index Deletion       : 0.00
% 9.14/3.34  Index Matching       : 0.00
% 9.14/3.34  BG Taut test         : 0.00
%------------------------------------------------------------------------------
