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
% DateTime   : Thu Dec  3 10:13:35 EST 2020

% Result     : Theorem 8.80s
% Output     : CNFRefutation 8.80s
% Verified   : 
% Statistics : Number of formulae       :  177 (1305 expanded)
%              Number of leaves         :   39 ( 414 expanded)
%              Depth                    :   13
%              Number of atoms          :  282 (3911 expanded)
%              Number of equality atoms :   87 (1408 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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

tff(f_73,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_101,axiom,(
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

tff(f_69,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( r1_tarski(A,k1_relat_1(B))
       => k1_relat_1(k7_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_relat_1)).

tff(f_115,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => k2_partfun1(A,B,C,D) = k7_relat_1(C,D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

tff(f_109,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(C)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( v1_funct_1(k2_partfun1(A,B,C,D))
        & m1_subset_1(k2_partfun1(A,B,C,D),k1_zfmisc_1(k2_zfmisc_1(A,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_partfun1)).

tff(f_79,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_127,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( r1_tarski(k2_relat_1(B),A)
       => ( v1_funct_1(B)
          & v1_funct_2(B,k1_relat_1(B),A)
          & m1_subset_1(B,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B),A))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_funct_2)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_45,axiom,(
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

tff(f_63,axiom,(
    ! [A] : k7_relat_1(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t111_relat_1)).

tff(f_41,axiom,(
    ! [A] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

tff(c_70,plain,(
    r1_tarski('#skF_3','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_72,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_136,plain,(
    ! [C_54,A_55,B_56] :
      ( v1_relat_1(C_54)
      | ~ m1_subset_1(C_54,k1_zfmisc_1(k2_zfmisc_1(A_55,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_154,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_136])).

tff(c_68,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_85,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_74,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10001,plain,(
    ! [A_936,B_937,C_938] :
      ( k1_relset_1(A_936,B_937,C_938) = k1_relat_1(C_938)
      | ~ m1_subset_1(C_938,k1_zfmisc_1(k2_zfmisc_1(A_936,B_937))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_10026,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_10001])).

tff(c_11017,plain,(
    ! [B_1044,A_1045,C_1046] :
      ( k1_xboole_0 = B_1044
      | k1_relset_1(A_1045,B_1044,C_1046) = A_1045
      | ~ v1_funct_2(C_1046,A_1045,B_1044)
      | ~ m1_subset_1(C_1046,k1_zfmisc_1(k2_zfmisc_1(A_1045,B_1044))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_11037,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_11017])).

tff(c_11049,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_10026,c_11037])).

tff(c_11050,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_11049])).

tff(c_32,plain,(
    ! [B_18,A_17] :
      ( k1_relat_1(k7_relat_1(B_18,A_17)) = A_17
      | ~ r1_tarski(A_17,k1_relat_1(B_18))
      | ~ v1_relat_1(B_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_11065,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11050,c_32])).

tff(c_11075,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_11065])).

tff(c_76,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_10857,plain,(
    ! [A_1031,B_1032,C_1033,D_1034] :
      ( k2_partfun1(A_1031,B_1032,C_1033,D_1034) = k7_relat_1(C_1033,D_1034)
      | ~ m1_subset_1(C_1033,k1_zfmisc_1(k2_zfmisc_1(A_1031,B_1032)))
      | ~ v1_funct_1(C_1033) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_10871,plain,(
    ! [D_1034] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_1034) = k7_relat_1('#skF_4',D_1034)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_10857])).

tff(c_10883,plain,(
    ! [D_1034] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_1034) = k7_relat_1('#skF_4',D_1034) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_10871])).

tff(c_4818,plain,(
    ! [A_532,B_533,C_534,D_535] :
      ( k2_partfun1(A_532,B_533,C_534,D_535) = k7_relat_1(C_534,D_535)
      | ~ m1_subset_1(C_534,k1_zfmisc_1(k2_zfmisc_1(A_532,B_533)))
      | ~ v1_funct_1(C_534) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_4830,plain,(
    ! [D_535] :
      ( k2_partfun1('#skF_1','#skF_2','#skF_4',D_535) = k7_relat_1('#skF_4',D_535)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_4818])).

tff(c_4840,plain,(
    ! [D_535] : k2_partfun1('#skF_1','#skF_2','#skF_4',D_535) = k7_relat_1('#skF_4',D_535) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4830])).

tff(c_5038,plain,(
    ! [A_555,B_556,C_557,D_558] :
      ( m1_subset_1(k2_partfun1(A_555,B_556,C_557,D_558),k1_zfmisc_1(k2_zfmisc_1(A_555,B_556)))
      | ~ m1_subset_1(C_557,k1_zfmisc_1(k2_zfmisc_1(A_555,B_556)))
      | ~ v1_funct_1(C_557) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_5068,plain,(
    ! [D_535] :
      ( m1_subset_1(k7_relat_1('#skF_4',D_535),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4840,c_5038])).

tff(c_5099,plain,(
    ! [D_560] : m1_subset_1(k7_relat_1('#skF_4',D_560),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_72,c_5068])).

tff(c_34,plain,(
    ! [C_21,A_19,B_20] :
      ( v1_relat_1(C_21)
      | ~ m1_subset_1(C_21,k1_zfmisc_1(k2_zfmisc_1(A_19,B_20))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_5143,plain,(
    ! [D_560] : v1_relat_1(k7_relat_1('#skF_4',D_560)) ),
    inference(resolution,[status(thm)],[c_5099,c_34])).

tff(c_36,plain,(
    ! [C_24,B_23,A_22] :
      ( v5_relat_1(C_24,B_23)
      | ~ m1_subset_1(C_24,k1_zfmisc_1(k2_zfmisc_1(A_22,B_23))) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5142,plain,(
    ! [D_560] : v5_relat_1(k7_relat_1('#skF_4',D_560),'#skF_2') ),
    inference(resolution,[status(thm)],[c_5099,c_36])).

tff(c_26,plain,(
    ! [B_13,A_12] :
      ( r1_tarski(k2_relat_1(B_13),A_12)
      | ~ v5_relat_1(B_13,A_12)
      | ~ v1_relat_1(B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4471,plain,(
    ! [A_484,B_485,C_486,D_487] :
      ( v1_funct_1(k2_partfun1(A_484,B_485,C_486,D_487))
      | ~ m1_subset_1(C_486,k1_zfmisc_1(k2_zfmisc_1(A_484,B_485)))
      | ~ v1_funct_1(C_486) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_4481,plain,(
    ! [D_487] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_487))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_4471])).

tff(c_4490,plain,(
    ! [D_487] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_487)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_4481])).

tff(c_4850,plain,(
    ! [D_487] : v1_funct_1(k7_relat_1('#skF_4',D_487)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_4490])).

tff(c_1138,plain,(
    ! [A_199,B_200,C_201] :
      ( k1_relset_1(A_199,B_200,C_201) = k1_relat_1(C_201)
      | ~ m1_subset_1(C_201,k1_zfmisc_1(k2_zfmisc_1(A_199,B_200))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1159,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_72,c_1138])).

tff(c_4923,plain,(
    ! [B_549,A_550,C_551] :
      ( k1_xboole_0 = B_549
      | k1_relset_1(A_550,B_549,C_551) = A_550
      | ~ v1_funct_2(C_551,A_550,B_549)
      | ~ m1_subset_1(C_551,k1_zfmisc_1(k2_zfmisc_1(A_550,B_549))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_4940,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_72,c_4923])).

tff(c_4950,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1159,c_4940])).

tff(c_4951,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_4950])).

tff(c_4966,plain,(
    ! [A_17] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_17)) = A_17
      | ~ r1_tarski(A_17,'#skF_1')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4951,c_32])).

tff(c_5172,plain,(
    ! [A_566] :
      ( k1_relat_1(k7_relat_1('#skF_4',A_566)) = A_566
      | ~ r1_tarski(A_566,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_4966])).

tff(c_60,plain,(
    ! [B_40,A_39] :
      ( m1_subset_1(B_40,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_40),A_39)))
      | ~ r1_tarski(k2_relat_1(B_40),A_39)
      | ~ v1_funct_1(B_40)
      | ~ v1_relat_1(B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_127])).

tff(c_5181,plain,(
    ! [A_566,A_39] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_566),k1_zfmisc_1(k2_zfmisc_1(A_566,A_39)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_566)),A_39)
      | ~ v1_funct_1(k7_relat_1('#skF_4',A_566))
      | ~ v1_relat_1(k7_relat_1('#skF_4',A_566))
      | ~ r1_tarski(A_566,'#skF_1') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5172,c_60])).

tff(c_9491,plain,(
    ! [A_877,A_878] :
      ( m1_subset_1(k7_relat_1('#skF_4',A_877),k1_zfmisc_1(k2_zfmisc_1(A_877,A_878)))
      | ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4',A_877)),A_878)
      | ~ r1_tarski(A_877,'#skF_1') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5143,c_4850,c_5181])).

tff(c_711,plain,(
    ! [A_138,B_139,C_140,D_141] :
      ( v1_funct_1(k2_partfun1(A_138,B_139,C_140,D_141))
      | ~ m1_subset_1(C_140,k1_zfmisc_1(k2_zfmisc_1(A_138,B_139)))
      | ~ v1_funct_1(C_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_721,plain,(
    ! [D_141] :
      ( v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_141))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_72,c_711])).

tff(c_728,plain,(
    ! [D_141] : v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4',D_141)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_721])).

tff(c_66,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2')))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_155,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_66])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_728,c_155])).

tff(c_732,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_66])).

tff(c_789,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_732])).

tff(c_4852,plain,(
    ~ m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4840,c_789])).

tff(c_9506,plain,
    ( ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2')
    | ~ r1_tarski('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_9491,c_4852])).

tff(c_9550,plain,(
    ~ r1_tarski(k2_relat_1(k7_relat_1('#skF_4','#skF_3')),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_9506])).

tff(c_9570,plain,
    ( ~ v5_relat_1(k7_relat_1('#skF_4','#skF_3'),'#skF_2')
    | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_26,c_9550])).

tff(c_9574,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5143,c_5142,c_9570])).

tff(c_9576,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_10022,plain,(
    k1_relset_1('#skF_3','#skF_2',k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) = k1_relat_1(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_9576,c_10001])).

tff(c_10887,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) = k1_relat_1(k7_relat_1('#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10883,c_10883,c_10022])).

tff(c_9575,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_2','#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(splitRight,[status(thm)],[c_732])).

tff(c_10894,plain,(
    ~ v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10883,c_9575])).

tff(c_10893,plain,(
    m1_subset_1(k7_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10883,c_9576])).

tff(c_48,plain,(
    ! [B_29,C_30,A_28] :
      ( k1_xboole_0 = B_29
      | v1_funct_2(C_30,A_28,B_29)
      | k1_relset_1(A_28,B_29,C_30) != A_28
      | ~ m1_subset_1(C_30,k1_zfmisc_1(k2_zfmisc_1(A_28,B_29))) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_10958,plain,
    ( k1_xboole_0 = '#skF_2'
    | v1_funct_2(k7_relat_1('#skF_4','#skF_3'),'#skF_3','#skF_2')
    | k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(resolution,[status(thm)],[c_10893,c_48])).

tff(c_10982,plain,(
    k1_relset_1('#skF_3','#skF_2',k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_10894,c_85,c_10958])).

tff(c_11213,plain,(
    k1_relat_1(k7_relat_1('#skF_4','#skF_3')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10887,c_10982])).

tff(c_11271,plain,(
    ~ r1_tarski('#skF_3','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_11075,c_11213])).

tff(c_11275,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_11271])).

tff(c_11276,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_11278,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11276,c_8])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_11301,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11276,c_11276,c_12])).

tff(c_11277,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_11283,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11276,c_11277])).

tff(c_11289,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11283,c_72])).

tff(c_11302,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11301,c_11289])).

tff(c_11962,plain,(
    ! [A_1157,B_1158] :
      ( r1_tarski(A_1157,B_1158)
      | ~ m1_subset_1(A_1157,k1_zfmisc_1(B_1158)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11973,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_11302,c_11962])).

tff(c_13109,plain,(
    ! [B_1306,A_1307] :
      ( B_1306 = A_1307
      | ~ r1_tarski(B_1306,A_1307)
      | ~ r1_tarski(A_1307,B_1306) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_13113,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_11973,c_13109])).

tff(c_13125,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_13113])).

tff(c_11284,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_11283,c_74])).

tff(c_13158,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13125,c_13125,c_11284])).

tff(c_13119,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_13109])).

tff(c_13133,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_13119])).

tff(c_13147,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13125,c_13133])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12058,plain,(
    ! [B_1169,A_1170] :
      ( B_1169 = A_1170
      | ~ r1_tarski(B_1169,A_1170)
      | ~ r1_tarski(A_1170,B_1169) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_12060,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_11973,c_12058])).

tff(c_12069,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_12060])).

tff(c_30,plain,(
    ! [A_16] : k7_relat_1(k1_xboole_0,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_11291,plain,(
    ! [A_16] : k7_relat_1('#skF_1',A_16) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11276,c_11276,c_30])).

tff(c_12099,plain,(
    ! [A_16] : k7_relat_1('#skF_4',A_16) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12069,c_12069,c_11291])).

tff(c_16,plain,(
    ! [A_6] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(A_6)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_11299,plain,(
    ! [A_6] : m1_subset_1('#skF_1',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11276,c_16])).

tff(c_12097,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12069,c_11299])).

tff(c_13024,plain,(
    ! [A_1296,B_1297,C_1298,D_1299] :
      ( k2_partfun1(A_1296,B_1297,C_1298,D_1299) = k7_relat_1(C_1298,D_1299)
      | ~ m1_subset_1(C_1298,k1_zfmisc_1(k2_zfmisc_1(A_1296,B_1297)))
      | ~ v1_funct_1(C_1298) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_13033,plain,(
    ! [A_1296,B_1297,D_1299] :
      ( k2_partfun1(A_1296,B_1297,'#skF_4',D_1299) = k7_relat_1('#skF_4',D_1299)
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_12097,c_13024])).

tff(c_13040,plain,(
    ! [A_1296,B_1297,D_1299] : k2_partfun1(A_1296,B_1297,'#skF_4',D_1299) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_12099,c_13033])).

tff(c_20,plain,(
    ! [A_7,B_8] :
      ( m1_subset_1(A_7,k1_zfmisc_1(B_8))
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_12066,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_12058])).

tff(c_12077,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_12066])).

tff(c_12087,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12069,c_12077])).

tff(c_11334,plain,(
    ! [A_1064,B_1065] :
      ( r1_tarski(A_1064,B_1065)
      | ~ m1_subset_1(A_1064,k1_zfmisc_1(B_1065)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_11341,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_11302,c_11334])).

tff(c_11392,plain,(
    ! [B_1074,A_1075] :
      ( B_1074 = A_1075
      | ~ r1_tarski(B_1074,A_1075)
      | ~ r1_tarski(A_1075,B_1074) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11394,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_11341,c_11392])).

tff(c_11403,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_11394])).

tff(c_11428,plain,(
    ! [A_6] : m1_subset_1('#skF_4',k1_zfmisc_1(A_6)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11403,c_11299])).

tff(c_11941,plain,(
    ! [A_1151,B_1152,C_1153,D_1154] :
      ( v1_funct_1(k2_partfun1(A_1151,B_1152,C_1153,D_1154))
      | ~ m1_subset_1(C_1153,k1_zfmisc_1(k2_zfmisc_1(A_1151,B_1152)))
      | ~ v1_funct_1(C_1153) ) ),
    inference(cnfTransformation,[status(thm)],[f_109])).

tff(c_11948,plain,(
    ! [A_1151,B_1152,D_1154] :
      ( v1_funct_1(k2_partfun1(A_1151,B_1152,'#skF_4',D_1154))
      | ~ v1_funct_1('#skF_4') ) ),
    inference(resolution,[status(thm)],[c_11428,c_11941])).

tff(c_11954,plain,(
    ! [A_1151,B_1152,D_1154] : v1_funct_1(k2_partfun1(A_1151,B_1152,'#skF_4',D_1154)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_76,c_11948])).

tff(c_11400,plain,
    ( '#skF_3' = '#skF_1'
    | ~ r1_tarski('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_11392])).

tff(c_11411,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_11400])).

tff(c_11332,plain,
    ( ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1'))
    | ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11283,c_11283,c_11283,c_11301,c_11283,c_11283,c_66])).

tff(c_11333,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_11332])).

tff(c_11412,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11411,c_11333])).

tff(c_11572,plain,(
    ~ v1_funct_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_11403,c_11403,c_11403,c_11412])).

tff(c_11958,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_11954,c_11572])).

tff(c_11959,plain,
    ( ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1')
    | ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_11332])).

tff(c_12019,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitLeft,[status(thm)],[c_11959])).

tff(c_12166,plain,(
    ~ m1_subset_1(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12087,c_12069,c_12069,c_12069,c_12019])).

tff(c_12170,plain,(
    ~ r1_tarski(k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_20,c_12166])).

tff(c_13043,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13040,c_12170])).

tff(c_13048,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_13043])).

tff(c_13050,plain,(
    m1_subset_1(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),k1_zfmisc_1('#skF_1')) ),
    inference(splitRight,[status(thm)],[c_11959])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_tarski(A_7,B_8)
      | ~ m1_subset_1(A_7,k1_zfmisc_1(B_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_13103,plain,(
    r1_tarski(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_13050,c_18])).

tff(c_13111,plain,
    ( k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3') = '#skF_1'
    | ~ r1_tarski('#skF_1',k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3')) ),
    inference(resolution,[status(thm)],[c_13103,c_13109])).

tff(c_13122,plain,(
    k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_11278,c_13111])).

tff(c_13316,plain,(
    k2_partfun1('#skF_4','#skF_4','#skF_4','#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_13147,c_13125,c_13125,c_13125,c_13122])).

tff(c_13049,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_3'),'#skF_3','#skF_1') ),
    inference(splitRight,[status(thm)],[c_11959])).

tff(c_13137,plain,(
    ~ v1_funct_2(k2_partfun1('#skF_1','#skF_1','#skF_4','#skF_1'),'#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_13133,c_13133,c_13049])).

tff(c_13344,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_13158,c_13316,c_13125,c_13125,c_13125,c_13125,c_13125,c_13137])).
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
% 0.13/0.34  % DateTime   : Tue Dec  1 17:24:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 8.80/3.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.14  
% 8.80/3.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.14  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r2_hidden > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k2_partfun1 > k1_relset_1 > k7_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.80/3.14  
% 8.80/3.14  %Foreground sorts:
% 8.80/3.14  
% 8.80/3.14  
% 8.80/3.14  %Background operators:
% 8.80/3.14  
% 8.80/3.14  
% 8.80/3.14  %Foreground operators:
% 8.80/3.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.80/3.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.80/3.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 8.80/3.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 8.80/3.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.80/3.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 8.80/3.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.80/3.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.80/3.14  tff('#skF_2', type, '#skF_2': $i).
% 8.80/3.14  tff('#skF_3', type, '#skF_3': $i).
% 8.80/3.14  tff('#skF_1', type, '#skF_1': $i).
% 8.80/3.14  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 8.80/3.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 8.80/3.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.80/3.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.80/3.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.80/3.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.80/3.14  tff('#skF_4', type, '#skF_4': $i).
% 8.80/3.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.80/3.14  tff(k2_partfun1, type, k2_partfun1: ($i * $i * $i * $i) > $i).
% 8.80/3.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 8.80/3.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.80/3.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.80/3.14  
% 8.80/3.16  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(C, A) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(k2_partfun1(A, B, D, C)) & v1_funct_2(k2_partfun1(A, B, D, C), C, B)) & m1_subset_1(k2_partfun1(A, B, D, C), k1_zfmisc_1(k2_zfmisc_1(C, B)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_funct_2)).
% 8.80/3.16  tff(f_73, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.80/3.16  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 8.80/3.16  tff(f_101, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 8.80/3.16  tff(f_69, axiom, (![A, B]: (v1_relat_1(B) => (r1_tarski(A, k1_relat_1(B)) => (k1_relat_1(k7_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_relat_1)).
% 8.80/3.16  tff(f_115, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (k2_partfun1(A, B, C, D) = k7_relat_1(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_partfun1)).
% 8.80/3.16  tff(f_109, axiom, (![A, B, C, D]: ((v1_funct_1(C) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (v1_funct_1(k2_partfun1(A, B, C, D)) & m1_subset_1(k2_partfun1(A, B, C, D), k1_zfmisc_1(k2_zfmisc_1(A, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_partfun1)).
% 8.80/3.16  tff(f_79, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 8.80/3.16  tff(f_57, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 8.80/3.16  tff(f_127, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => (r1_tarski(k2_relat_1(B), A) => ((v1_funct_1(B) & v1_funct_2(B, k1_relat_1(B), A)) & m1_subset_1(B, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B), A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_funct_2)).
% 8.80/3.16  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 8.80/3.16  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 8.80/3.16  tff(f_45, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 8.80/3.16  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 8.80/3.16  tff(f_63, axiom, (![A]: (k7_relat_1(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t111_relat_1)).
% 8.80/3.16  tff(f_41, axiom, (![A]: m1_subset_1(k1_xboole_0, k1_zfmisc_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_subset_1)).
% 8.80/3.16  tff(c_70, plain, (r1_tarski('#skF_3', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.80/3.16  tff(c_72, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.80/3.16  tff(c_136, plain, (![C_54, A_55, B_56]: (v1_relat_1(C_54) | ~m1_subset_1(C_54, k1_zfmisc_1(k2_zfmisc_1(A_55, B_56))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.80/3.16  tff(c_154, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_136])).
% 8.80/3.16  tff(c_68, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.80/3.16  tff(c_85, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_68])).
% 8.80/3.16  tff(c_74, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.80/3.16  tff(c_10001, plain, (![A_936, B_937, C_938]: (k1_relset_1(A_936, B_937, C_938)=k1_relat_1(C_938) | ~m1_subset_1(C_938, k1_zfmisc_1(k2_zfmisc_1(A_936, B_937))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.80/3.16  tff(c_10026, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_10001])).
% 8.80/3.16  tff(c_11017, plain, (![B_1044, A_1045, C_1046]: (k1_xboole_0=B_1044 | k1_relset_1(A_1045, B_1044, C_1046)=A_1045 | ~v1_funct_2(C_1046, A_1045, B_1044) | ~m1_subset_1(C_1046, k1_zfmisc_1(k2_zfmisc_1(A_1045, B_1044))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.16  tff(c_11037, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_11017])).
% 8.80/3.16  tff(c_11049, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_10026, c_11037])).
% 8.80/3.16  tff(c_11050, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_85, c_11049])).
% 8.80/3.16  tff(c_32, plain, (![B_18, A_17]: (k1_relat_1(k7_relat_1(B_18, A_17))=A_17 | ~r1_tarski(A_17, k1_relat_1(B_18)) | ~v1_relat_1(B_18))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.80/3.16  tff(c_11065, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_11050, c_32])).
% 8.80/3.16  tff(c_11075, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_11065])).
% 8.80/3.16  tff(c_76, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.80/3.16  tff(c_10857, plain, (![A_1031, B_1032, C_1033, D_1034]: (k2_partfun1(A_1031, B_1032, C_1033, D_1034)=k7_relat_1(C_1033, D_1034) | ~m1_subset_1(C_1033, k1_zfmisc_1(k2_zfmisc_1(A_1031, B_1032))) | ~v1_funct_1(C_1033))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.80/3.16  tff(c_10871, plain, (![D_1034]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1034)=k7_relat_1('#skF_4', D_1034) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_10857])).
% 8.80/3.16  tff(c_10883, plain, (![D_1034]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_1034)=k7_relat_1('#skF_4', D_1034))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_10871])).
% 8.80/3.16  tff(c_4818, plain, (![A_532, B_533, C_534, D_535]: (k2_partfun1(A_532, B_533, C_534, D_535)=k7_relat_1(C_534, D_535) | ~m1_subset_1(C_534, k1_zfmisc_1(k2_zfmisc_1(A_532, B_533))) | ~v1_funct_1(C_534))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.80/3.16  tff(c_4830, plain, (![D_535]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_535)=k7_relat_1('#skF_4', D_535) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_4818])).
% 8.80/3.16  tff(c_4840, plain, (![D_535]: (k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_535)=k7_relat_1('#skF_4', D_535))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4830])).
% 8.80/3.16  tff(c_5038, plain, (![A_555, B_556, C_557, D_558]: (m1_subset_1(k2_partfun1(A_555, B_556, C_557, D_558), k1_zfmisc_1(k2_zfmisc_1(A_555, B_556))) | ~m1_subset_1(C_557, k1_zfmisc_1(k2_zfmisc_1(A_555, B_556))) | ~v1_funct_1(C_557))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.80/3.16  tff(c_5068, plain, (![D_535]: (m1_subset_1(k7_relat_1('#skF_4', D_535), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4840, c_5038])).
% 8.80/3.16  tff(c_5099, plain, (![D_560]: (m1_subset_1(k7_relat_1('#skF_4', D_560), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_72, c_5068])).
% 8.80/3.16  tff(c_34, plain, (![C_21, A_19, B_20]: (v1_relat_1(C_21) | ~m1_subset_1(C_21, k1_zfmisc_1(k2_zfmisc_1(A_19, B_20))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 8.80/3.16  tff(c_5143, plain, (![D_560]: (v1_relat_1(k7_relat_1('#skF_4', D_560)))), inference(resolution, [status(thm)], [c_5099, c_34])).
% 8.80/3.16  tff(c_36, plain, (![C_24, B_23, A_22]: (v5_relat_1(C_24, B_23) | ~m1_subset_1(C_24, k1_zfmisc_1(k2_zfmisc_1(A_22, B_23))))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.80/3.16  tff(c_5142, plain, (![D_560]: (v5_relat_1(k7_relat_1('#skF_4', D_560), '#skF_2'))), inference(resolution, [status(thm)], [c_5099, c_36])).
% 8.80/3.16  tff(c_26, plain, (![B_13, A_12]: (r1_tarski(k2_relat_1(B_13), A_12) | ~v5_relat_1(B_13, A_12) | ~v1_relat_1(B_13))), inference(cnfTransformation, [status(thm)], [f_57])).
% 8.80/3.16  tff(c_4471, plain, (![A_484, B_485, C_486, D_487]: (v1_funct_1(k2_partfun1(A_484, B_485, C_486, D_487)) | ~m1_subset_1(C_486, k1_zfmisc_1(k2_zfmisc_1(A_484, B_485))) | ~v1_funct_1(C_486))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.80/3.16  tff(c_4481, plain, (![D_487]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_487)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_4471])).
% 8.80/3.16  tff(c_4490, plain, (![D_487]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_487)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_4481])).
% 8.80/3.16  tff(c_4850, plain, (![D_487]: (v1_funct_1(k7_relat_1('#skF_4', D_487)))), inference(demodulation, [status(thm), theory('equality')], [c_4840, c_4490])).
% 8.80/3.16  tff(c_1138, plain, (![A_199, B_200, C_201]: (k1_relset_1(A_199, B_200, C_201)=k1_relat_1(C_201) | ~m1_subset_1(C_201, k1_zfmisc_1(k2_zfmisc_1(A_199, B_200))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.80/3.16  tff(c_1159, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_72, c_1138])).
% 8.80/3.16  tff(c_4923, plain, (![B_549, A_550, C_551]: (k1_xboole_0=B_549 | k1_relset_1(A_550, B_549, C_551)=A_550 | ~v1_funct_2(C_551, A_550, B_549) | ~m1_subset_1(C_551, k1_zfmisc_1(k2_zfmisc_1(A_550, B_549))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.16  tff(c_4940, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_72, c_4923])).
% 8.80/3.16  tff(c_4950, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1159, c_4940])).
% 8.80/3.16  tff(c_4951, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_85, c_4950])).
% 8.80/3.16  tff(c_4966, plain, (![A_17]: (k1_relat_1(k7_relat_1('#skF_4', A_17))=A_17 | ~r1_tarski(A_17, '#skF_1') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_4951, c_32])).
% 8.80/3.16  tff(c_5172, plain, (![A_566]: (k1_relat_1(k7_relat_1('#skF_4', A_566))=A_566 | ~r1_tarski(A_566, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_154, c_4966])).
% 8.80/3.16  tff(c_60, plain, (![B_40, A_39]: (m1_subset_1(B_40, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(B_40), A_39))) | ~r1_tarski(k2_relat_1(B_40), A_39) | ~v1_funct_1(B_40) | ~v1_relat_1(B_40))), inference(cnfTransformation, [status(thm)], [f_127])).
% 8.80/3.16  tff(c_5181, plain, (![A_566, A_39]: (m1_subset_1(k7_relat_1('#skF_4', A_566), k1_zfmisc_1(k2_zfmisc_1(A_566, A_39))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_566)), A_39) | ~v1_funct_1(k7_relat_1('#skF_4', A_566)) | ~v1_relat_1(k7_relat_1('#skF_4', A_566)) | ~r1_tarski(A_566, '#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_5172, c_60])).
% 8.80/3.16  tff(c_9491, plain, (![A_877, A_878]: (m1_subset_1(k7_relat_1('#skF_4', A_877), k1_zfmisc_1(k2_zfmisc_1(A_877, A_878))) | ~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', A_877)), A_878) | ~r1_tarski(A_877, '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5143, c_4850, c_5181])).
% 8.80/3.16  tff(c_711, plain, (![A_138, B_139, C_140, D_141]: (v1_funct_1(k2_partfun1(A_138, B_139, C_140, D_141)) | ~m1_subset_1(C_140, k1_zfmisc_1(k2_zfmisc_1(A_138, B_139))) | ~v1_funct_1(C_140))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.80/3.16  tff(c_721, plain, (![D_141]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_141)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_72, c_711])).
% 8.80/3.16  tff(c_728, plain, (![D_141]: (v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', D_141)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_721])).
% 8.80/3.16  tff(c_66, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2'))) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_147])).
% 8.80/3.16  tff(c_155, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_66])).
% 8.80/3.16  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_728, c_155])).
% 8.80/3.16  tff(c_732, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_66])).
% 8.80/3.16  tff(c_789, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitLeft, [status(thm)], [c_732])).
% 8.80/3.16  tff(c_4852, plain, (~m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_4840, c_789])).
% 8.80/3.16  tff(c_9506, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2') | ~r1_tarski('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_9491, c_4852])).
% 8.80/3.16  tff(c_9550, plain, (~r1_tarski(k2_relat_1(k7_relat_1('#skF_4', '#skF_3')), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_9506])).
% 8.80/3.16  tff(c_9570, plain, (~v5_relat_1(k7_relat_1('#skF_4', '#skF_3'), '#skF_2') | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_9550])).
% 8.80/3.16  tff(c_9574, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5143, c_5142, c_9570])).
% 8.80/3.16  tff(c_9576, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(splitRight, [status(thm)], [c_732])).
% 8.80/3.16  tff(c_10022, plain, (k1_relset_1('#skF_3', '#skF_2', k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))=k1_relat_1(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_9576, c_10001])).
% 8.80/3.16  tff(c_10887, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))=k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_10883, c_10883, c_10022])).
% 8.80/3.16  tff(c_9575, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_2', '#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(splitRight, [status(thm)], [c_732])).
% 8.80/3.16  tff(c_10894, plain, (~v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_10883, c_9575])).
% 8.80/3.16  tff(c_10893, plain, (m1_subset_1(k7_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_10883, c_9576])).
% 8.80/3.16  tff(c_48, plain, (![B_29, C_30, A_28]: (k1_xboole_0=B_29 | v1_funct_2(C_30, A_28, B_29) | k1_relset_1(A_28, B_29, C_30)!=A_28 | ~m1_subset_1(C_30, k1_zfmisc_1(k2_zfmisc_1(A_28, B_29))))), inference(cnfTransformation, [status(thm)], [f_101])).
% 8.80/3.16  tff(c_10958, plain, (k1_xboole_0='#skF_2' | v1_funct_2(k7_relat_1('#skF_4', '#skF_3'), '#skF_3', '#skF_2') | k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(resolution, [status(thm)], [c_10893, c_48])).
% 8.80/3.16  tff(c_10982, plain, (k1_relset_1('#skF_3', '#skF_2', k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_10894, c_85, c_10958])).
% 8.80/3.16  tff(c_11213, plain, (k1_relat_1(k7_relat_1('#skF_4', '#skF_3'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10887, c_10982])).
% 8.80/3.16  tff(c_11271, plain, (~r1_tarski('#skF_3', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_11075, c_11213])).
% 8.80/3.16  tff(c_11275, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_70, c_11271])).
% 8.80/3.16  tff(c_11276, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_68])).
% 8.80/3.16  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 8.80/3.16  tff(c_11278, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_11276, c_8])).
% 8.80/3.16  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.80/3.16  tff(c_11301, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11276, c_11276, c_12])).
% 8.80/3.16  tff(c_11277, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_68])).
% 8.80/3.16  tff(c_11283, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11276, c_11277])).
% 8.80/3.16  tff(c_11289, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_11283, c_72])).
% 8.80/3.16  tff(c_11302, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11301, c_11289])).
% 8.80/3.16  tff(c_11962, plain, (![A_1157, B_1158]: (r1_tarski(A_1157, B_1158) | ~m1_subset_1(A_1157, k1_zfmisc_1(B_1158)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.80/3.16  tff(c_11973, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_11302, c_11962])).
% 8.80/3.16  tff(c_13109, plain, (![B_1306, A_1307]: (B_1306=A_1307 | ~r1_tarski(B_1306, A_1307) | ~r1_tarski(A_1307, B_1306))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.80/3.16  tff(c_13113, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_11973, c_13109])).
% 8.80/3.16  tff(c_13125, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_13113])).
% 8.80/3.16  tff(c_11284, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11283, c_74])).
% 8.80/3.16  tff(c_13158, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13125, c_13125, c_11284])).
% 8.80/3.16  tff(c_13119, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_13109])).
% 8.80/3.16  tff(c_13133, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_13119])).
% 8.80/3.16  tff(c_13147, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13125, c_13133])).
% 8.80/3.16  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.80/3.16  tff(c_12058, plain, (![B_1169, A_1170]: (B_1169=A_1170 | ~r1_tarski(B_1169, A_1170) | ~r1_tarski(A_1170, B_1169))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.80/3.16  tff(c_12060, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_11973, c_12058])).
% 8.80/3.16  tff(c_12069, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_12060])).
% 8.80/3.16  tff(c_30, plain, (![A_16]: (k7_relat_1(k1_xboole_0, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 8.80/3.16  tff(c_11291, plain, (![A_16]: (k7_relat_1('#skF_1', A_16)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_11276, c_11276, c_30])).
% 8.80/3.16  tff(c_12099, plain, (![A_16]: (k7_relat_1('#skF_4', A_16)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12069, c_12069, c_11291])).
% 8.80/3.16  tff(c_16, plain, (![A_6]: (m1_subset_1(k1_xboole_0, k1_zfmisc_1(A_6)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 8.80/3.16  tff(c_11299, plain, (![A_6]: (m1_subset_1('#skF_1', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_11276, c_16])).
% 8.80/3.16  tff(c_12097, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_12069, c_11299])).
% 8.80/3.16  tff(c_13024, plain, (![A_1296, B_1297, C_1298, D_1299]: (k2_partfun1(A_1296, B_1297, C_1298, D_1299)=k7_relat_1(C_1298, D_1299) | ~m1_subset_1(C_1298, k1_zfmisc_1(k2_zfmisc_1(A_1296, B_1297))) | ~v1_funct_1(C_1298))), inference(cnfTransformation, [status(thm)], [f_115])).
% 8.80/3.16  tff(c_13033, plain, (![A_1296, B_1297, D_1299]: (k2_partfun1(A_1296, B_1297, '#skF_4', D_1299)=k7_relat_1('#skF_4', D_1299) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_12097, c_13024])).
% 8.80/3.16  tff(c_13040, plain, (![A_1296, B_1297, D_1299]: (k2_partfun1(A_1296, B_1297, '#skF_4', D_1299)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_76, c_12099, c_13033])).
% 8.80/3.16  tff(c_20, plain, (![A_7, B_8]: (m1_subset_1(A_7, k1_zfmisc_1(B_8)) | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.80/3.16  tff(c_12066, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_12058])).
% 8.80/3.16  tff(c_12077, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_12066])).
% 8.80/3.16  tff(c_12087, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_12069, c_12077])).
% 8.80/3.16  tff(c_11334, plain, (![A_1064, B_1065]: (r1_tarski(A_1064, B_1065) | ~m1_subset_1(A_1064, k1_zfmisc_1(B_1065)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.80/3.16  tff(c_11341, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_11302, c_11334])).
% 8.80/3.16  tff(c_11392, plain, (![B_1074, A_1075]: (B_1074=A_1075 | ~r1_tarski(B_1074, A_1075) | ~r1_tarski(A_1075, B_1074))), inference(cnfTransformation, [status(thm)], [f_31])).
% 8.80/3.16  tff(c_11394, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_11341, c_11392])).
% 8.80/3.16  tff(c_11403, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_11394])).
% 8.80/3.16  tff(c_11428, plain, (![A_6]: (m1_subset_1('#skF_4', k1_zfmisc_1(A_6)))), inference(demodulation, [status(thm), theory('equality')], [c_11403, c_11299])).
% 8.80/3.16  tff(c_11941, plain, (![A_1151, B_1152, C_1153, D_1154]: (v1_funct_1(k2_partfun1(A_1151, B_1152, C_1153, D_1154)) | ~m1_subset_1(C_1153, k1_zfmisc_1(k2_zfmisc_1(A_1151, B_1152))) | ~v1_funct_1(C_1153))), inference(cnfTransformation, [status(thm)], [f_109])).
% 8.80/3.16  tff(c_11948, plain, (![A_1151, B_1152, D_1154]: (v1_funct_1(k2_partfun1(A_1151, B_1152, '#skF_4', D_1154)) | ~v1_funct_1('#skF_4'))), inference(resolution, [status(thm)], [c_11428, c_11941])).
% 8.80/3.16  tff(c_11954, plain, (![A_1151, B_1152, D_1154]: (v1_funct_1(k2_partfun1(A_1151, B_1152, '#skF_4', D_1154)))), inference(demodulation, [status(thm), theory('equality')], [c_76, c_11948])).
% 8.80/3.16  tff(c_11400, plain, ('#skF_3'='#skF_1' | ~r1_tarski('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_70, c_11392])).
% 8.80/3.16  tff(c_11411, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_11400])).
% 8.80/3.16  tff(c_11332, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1')) | ~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_11283, c_11283, c_11283, c_11301, c_11283, c_11283, c_66])).
% 8.80/3.16  tff(c_11333, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(splitLeft, [status(thm)], [c_11332])).
% 8.80/3.16  tff(c_11412, plain, (~v1_funct_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_11411, c_11333])).
% 8.80/3.16  tff(c_11572, plain, (~v1_funct_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_11403, c_11403, c_11403, c_11412])).
% 8.80/3.16  tff(c_11958, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_11954, c_11572])).
% 8.80/3.16  tff(c_11959, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1') | ~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_11332])).
% 8.80/3.16  tff(c_12019, plain, (~m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitLeft, [status(thm)], [c_11959])).
% 8.80/3.16  tff(c_12166, plain, (~m1_subset_1(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_12087, c_12069, c_12069, c_12069, c_12019])).
% 8.80/3.16  tff(c_12170, plain, (~r1_tarski(k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4'), '#skF_4')), inference(resolution, [status(thm)], [c_20, c_12166])).
% 8.80/3.16  tff(c_13043, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_13040, c_12170])).
% 8.80/3.16  tff(c_13048, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_13043])).
% 8.80/3.16  tff(c_13050, plain, (m1_subset_1(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), k1_zfmisc_1('#skF_1'))), inference(splitRight, [status(thm)], [c_11959])).
% 8.80/3.16  tff(c_18, plain, (![A_7, B_8]: (r1_tarski(A_7, B_8) | ~m1_subset_1(A_7, k1_zfmisc_1(B_8)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 8.80/3.16  tff(c_13103, plain, (r1_tarski(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_13050, c_18])).
% 8.80/3.16  tff(c_13111, plain, (k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3')='#skF_1' | ~r1_tarski('#skF_1', k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'))), inference(resolution, [status(thm)], [c_13103, c_13109])).
% 8.80/3.16  tff(c_13122, plain, (k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_11278, c_13111])).
% 8.80/3.16  tff(c_13316, plain, (k2_partfun1('#skF_4', '#skF_4', '#skF_4', '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_13147, c_13125, c_13125, c_13125, c_13122])).
% 8.80/3.16  tff(c_13049, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_3'), '#skF_3', '#skF_1')), inference(splitRight, [status(thm)], [c_11959])).
% 8.80/3.16  tff(c_13137, plain, (~v1_funct_2(k2_partfun1('#skF_1', '#skF_1', '#skF_4', '#skF_1'), '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_13133, c_13133, c_13049])).
% 8.80/3.16  tff(c_13344, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_13158, c_13316, c_13125, c_13125, c_13125, c_13125, c_13125, c_13137])).
% 8.80/3.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.80/3.16  
% 8.80/3.16  Inference rules
% 8.80/3.16  ----------------------
% 8.80/3.16  #Ref     : 0
% 8.80/3.16  #Sup     : 2814
% 8.80/3.16  #Fact    : 0
% 8.80/3.16  #Define  : 0
% 8.80/3.16  #Split   : 24
% 8.80/3.16  #Chain   : 0
% 8.80/3.16  #Close   : 0
% 8.80/3.16  
% 8.80/3.16  Ordering : KBO
% 8.80/3.16  
% 8.80/3.16  Simplification rules
% 8.80/3.16  ----------------------
% 8.80/3.16  #Subsume      : 354
% 8.80/3.16  #Demod        : 3308
% 8.80/3.16  #Tautology    : 1293
% 8.80/3.16  #SimpNegUnit  : 30
% 8.80/3.16  #BackRed      : 115
% 8.80/3.16  
% 8.80/3.16  #Partial instantiations: 0
% 8.80/3.16  #Strategies tried      : 1
% 8.80/3.16  
% 8.80/3.16  Timing (in seconds)
% 8.80/3.16  ----------------------
% 8.80/3.17  Preprocessing        : 0.35
% 8.80/3.17  Parsing              : 0.19
% 8.80/3.17  CNF conversion       : 0.02
% 8.80/3.17  Main loop            : 2.02
% 8.80/3.17  Inferencing          : 0.69
% 8.80/3.17  Reduction            : 0.74
% 8.80/3.17  Demodulation         : 0.54
% 8.80/3.17  BG Simplification    : 0.06
% 8.80/3.17  Subsumption          : 0.38
% 8.80/3.17  Abstraction          : 0.07
% 8.80/3.17  MUC search           : 0.00
% 8.80/3.17  Cooper               : 0.00
% 8.80/3.17  Total                : 2.43
% 8.80/3.17  Index Insertion      : 0.00
% 8.80/3.17  Index Deletion       : 0.00
% 8.80/3.17  Index Matching       : 0.00
% 8.80/3.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
