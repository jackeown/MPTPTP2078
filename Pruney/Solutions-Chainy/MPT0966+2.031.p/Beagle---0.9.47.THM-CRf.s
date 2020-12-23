%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:12 EST 2020

% Result     : Theorem 5.54s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :  308 (3041 expanded)
%              Number of leaves         :   27 ( 954 expanded)
%              Depth                    :   16
%              Number of atoms          :  533 (8339 expanded)
%              Number of equality atoms :  207 (2822 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ( r1_tarski(k2_relset_1(A,B,D),C)
         => ( ( B = k1_xboole_0
              & A != k1_xboole_0 )
            | ( v1_funct_1(D)
              & v1_funct_2(D,A,C)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,C))) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_funct_2)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,A)))
     => ( r1_tarski(k2_relat_1(D),B)
       => m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(C,B))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_relset_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_75,axiom,(
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

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2137,plain,(
    ! [A_244,B_245,C_246] :
      ( k2_relset_1(A_244,B_245,C_246) = k2_relat_1(C_246)
      | ~ m1_subset_1(C_246,k1_zfmisc_1(k2_zfmisc_1(A_244,B_245))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2152,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2137])).

tff(c_42,plain,(
    r1_tarski(k2_relset_1('#skF_1','#skF_2','#skF_4'),'#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_2153,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2152,c_42])).

tff(c_2250,plain,(
    ! [D_262,C_263,B_264,A_265] :
      ( m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(C_263,B_264)))
      | ~ r1_tarski(k2_relat_1(D_262),B_264)
      | ~ m1_subset_1(D_262,k1_zfmisc_1(k2_zfmisc_1(C_263,A_265))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2322,plain,(
    ! [B_276] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_276)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_276) ) ),
    inference(resolution,[status(thm)],[c_44,c_2250])).

tff(c_40,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_80,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_150,plain,(
    ! [A_35,B_36,C_37] :
      ( k1_relset_1(A_35,B_36,C_37) = k1_relat_1(C_37)
      | ~ m1_subset_1(C_37,k1_zfmisc_1(k2_zfmisc_1(A_35,B_36))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_165,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_150])).

tff(c_1491,plain,(
    ! [B_187,A_188,C_189] :
      ( k1_xboole_0 = B_187
      | k1_relset_1(A_188,B_187,C_189) = A_188
      | ~ v1_funct_2(C_189,A_188,B_187)
      | ~ m1_subset_1(C_189,k1_zfmisc_1(k2_zfmisc_1(A_188,B_187))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1501,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_1491])).

tff(c_1512,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_165,c_1501])).

tff(c_1513,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_1512])).

tff(c_231,plain,(
    ! [A_48,B_49,C_50] :
      ( k2_relset_1(A_48,B_49,C_50) = k2_relat_1(C_50)
      | ~ m1_subset_1(C_50,k1_zfmisc_1(k2_zfmisc_1(A_48,B_49))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_246,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_231])).

tff(c_248,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_42])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_38,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_50,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_38])).

tff(c_149,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_354,plain,(
    ! [D_68,C_69,B_70,A_71] :
      ( m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(C_69,B_70)))
      | ~ r1_tarski(k2_relat_1(D_68),B_70)
      | ~ m1_subset_1(D_68,k1_zfmisc_1(k2_zfmisc_1(C_69,A_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_367,plain,(
    ! [B_72] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_72)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_72) ) ),
    inference(resolution,[status(thm)],[c_44,c_354])).

tff(c_20,plain,(
    ! [A_8,B_9,C_10] :
      ( k1_relset_1(A_8,B_9,C_10) = k1_relat_1(C_10)
      | ~ m1_subset_1(C_10,k1_zfmisc_1(k2_zfmisc_1(A_8,B_9))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_426,plain,(
    ! [B_76] :
      ( k1_relset_1('#skF_1',B_76,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_76) ) ),
    inference(resolution,[status(thm)],[c_367,c_20])).

tff(c_434,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_248,c_426])).

tff(c_365,plain,(
    ! [B_70] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_70)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_70) ) ),
    inference(resolution,[status(thm)],[c_44,c_354])).

tff(c_554,plain,(
    ! [B_91,C_92,A_93] :
      ( k1_xboole_0 = B_91
      | v1_funct_2(C_92,A_93,B_91)
      | k1_relset_1(A_93,B_91,C_92) != A_93
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_91))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_612,plain,(
    ! [B_100] :
      ( k1_xboole_0 = B_100
      | v1_funct_2('#skF_4','#skF_1',B_100)
      | k1_relset_1('#skF_1',B_100,'#skF_4') != '#skF_1'
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_100) ) ),
    inference(resolution,[status(thm)],[c_365,c_554])).

tff(c_615,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_248,c_612])).

tff(c_621,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_434,c_615])).

tff(c_622,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_149,c_621])).

tff(c_629,plain,(
    k1_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_622])).

tff(c_669,plain,(
    ! [B_103,A_104,C_105] :
      ( k1_xboole_0 = B_103
      | k1_relset_1(A_104,B_103,C_105) = A_104
      | ~ v1_funct_2(C_105,A_104,B_103)
      | ~ m1_subset_1(C_105,k1_zfmisc_1(k2_zfmisc_1(A_104,B_103))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_682,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_669])).

tff(c_694,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_165,c_682])).

tff(c_696,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_629,c_80,c_694])).

tff(c_697,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_622])).

tff(c_12,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_382,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_367])).

tff(c_387,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_382])).

tff(c_710,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_697,c_387])).

tff(c_731,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_710])).

tff(c_732,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_16,plain,(
    ! [A_6,B_7] :
      ( r1_tarski(A_6,B_7)
      | ~ m1_subset_1(A_6,k1_zfmisc_1(B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_749,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_732,c_16])).

tff(c_8,plain,(
    ! [A_3] : r1_tarski(k1_xboole_0,A_3) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_91,plain,(
    ! [B_29,A_30] :
      ( B_29 = A_30
      | ~ r1_tarski(B_29,A_30)
      | ~ r1_tarski(A_30,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_106,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ r1_tarski(A_3,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_8,c_91])).

tff(c_767,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_749,c_106])).

tff(c_799,plain,(
    '#skF_2' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_80])).

tff(c_36,plain,(
    ! [B_19,A_18,C_20] :
      ( k1_xboole_0 = B_19
      | k1_relset_1(A_18,B_19,C_20) = A_18
      | ~ v1_funct_2(C_20,A_18,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_989,plain,(
    ! [B_120,A_121,C_122] :
      ( B_120 = '#skF_4'
      | k1_relset_1(A_121,B_120,C_122) = A_121
      | ~ v1_funct_2(C_122,A_121,B_120)
      | ~ m1_subset_1(C_122,k1_zfmisc_1(k2_zfmisc_1(A_121,B_120))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_36])).

tff(c_1002,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_44,c_989])).

tff(c_1007,plain,
    ( '#skF_2' = '#skF_4'
    | k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_165,c_1002])).

tff(c_1008,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_799,c_1007])).

tff(c_802,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_8])).

tff(c_18,plain,(
    ! [A_6,B_7] :
      ( m1_subset_1(A_6,k1_zfmisc_1(B_7))
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1183,plain,(
    ! [A_141,B_142,A_143] :
      ( k1_relset_1(A_141,B_142,A_143) = k1_relat_1(A_143)
      | ~ r1_tarski(A_143,k2_zfmisc_1(A_141,B_142)) ) ),
    inference(resolution,[status(thm)],[c_18,c_150])).

tff(c_1193,plain,(
    ! [A_141,B_142] : k1_relset_1(A_141,B_142,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_802,c_1183])).

tff(c_1199,plain,(
    ! [A_141,B_142] : k1_relset_1(A_141,B_142,'#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1008,c_1193])).

tff(c_733,plain,(
    r1_tarski(k2_relat_1('#skF_4'),k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_382])).

tff(c_820,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_733])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_822,plain,
    ( k2_relat_1('#skF_4') = '#skF_4'
    | ~ r1_tarski('#skF_4',k2_relat_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_820,c_2])).

tff(c_825,plain,(
    k2_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_802,c_822])).

tff(c_833,plain,(
    ! [B_70] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_70)))
      | ~ r1_tarski('#skF_4',B_70) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_365])).

tff(c_1087,plain,(
    ! [B_131] : m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_131))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_802,c_833])).

tff(c_32,plain,(
    ! [B_19,C_20,A_18] :
      ( k1_xboole_0 = B_19
      | v1_funct_2(C_20,A_18,B_19)
      | k1_relset_1(A_18,B_19,C_20) != A_18
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1057,plain,(
    ! [B_19,C_20,A_18] :
      ( B_19 = '#skF_4'
      | v1_funct_2(C_20,A_18,B_19)
      | k1_relset_1(A_18,B_19,C_20) != A_18
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(A_18,B_19))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_767,c_32])).

tff(c_1108,plain,(
    ! [B_131] :
      ( B_131 = '#skF_4'
      | v1_funct_2('#skF_4','#skF_1',B_131)
      | k1_relset_1('#skF_1',B_131,'#skF_4') != '#skF_1' ) ),
    inference(resolution,[status(thm)],[c_1087,c_1057])).

tff(c_1224,plain,(
    ! [B_148] :
      ( B_148 = '#skF_4'
      | v1_funct_2('#skF_4','#skF_1',B_148) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1199,c_1108])).

tff(c_1228,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1224,c_149])).

tff(c_101,plain,
    ( k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3'
    | ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_42,c_91])).

tff(c_185,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_247,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_185])).

tff(c_834,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_825,c_247])).

tff(c_1229,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1228,c_834])).

tff(c_1233,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1229])).

tff(c_1234,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_1262,plain,(
    ! [A_153,B_154,C_155] :
      ( k2_relset_1(A_153,B_154,C_155) = k2_relat_1(C_155)
      | ~ m1_subset_1(C_155,k1_zfmisc_1(k2_zfmisc_1(A_153,B_154))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1269,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1262])).

tff(c_1278,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1234,c_1269])).

tff(c_1309,plain,(
    ! [D_159,C_160,B_161,A_162] :
      ( m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(C_160,B_161)))
      | ~ r1_tarski(k2_relat_1(D_159),B_161)
      | ~ m1_subset_1(D_159,k1_zfmisc_1(k2_zfmisc_1(C_160,A_162))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_1314,plain,(
    ! [B_161] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_161)))
      | ~ r1_tarski(k2_relat_1('#skF_4'),B_161) ) ),
    inference(resolution,[status(thm)],[c_44,c_1309])).

tff(c_1323,plain,(
    ! [B_163] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_163)))
      | ~ r1_tarski('#skF_3',B_163) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1314])).

tff(c_1371,plain,(
    ! [B_168] :
      ( k1_relset_1('#skF_1',B_168,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_168) ) ),
    inference(resolution,[status(thm)],[c_1323,c_20])).

tff(c_1376,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_6,c_1371])).

tff(c_1515,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1513,c_1376])).

tff(c_1321,plain,(
    ! [B_161] :
      ( m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_161)))
      | ~ r1_tarski('#skF_3',B_161) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1278,c_1314])).

tff(c_1658,plain,(
    ! [B_210,C_211,A_212] :
      ( k1_xboole_0 = B_210
      | v1_funct_2(C_211,A_212,B_210)
      | k1_relset_1(A_212,B_210,C_211) != A_212
      | ~ m1_subset_1(C_211,k1_zfmisc_1(k2_zfmisc_1(A_212,B_210))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1862,plain,(
    ! [B_229] :
      ( k1_xboole_0 = B_229
      | v1_funct_2('#skF_4','#skF_1',B_229)
      | k1_relset_1('#skF_1',B_229,'#skF_4') != '#skF_1'
      | ~ r1_tarski('#skF_3',B_229) ) ),
    inference(resolution,[status(thm)],[c_1321,c_1658])).

tff(c_1868,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1'
    | ~ r1_tarski('#skF_3','#skF_3') ),
    inference(resolution,[status(thm)],[c_1862,c_149])).

tff(c_1872,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1515,c_1868])).

tff(c_1338,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_1323])).

tff(c_1345,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitLeft,[status(thm)],[c_1338])).

tff(c_1898,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1872,c_1345])).

tff(c_1913,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_1898])).

tff(c_1915,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(splitRight,[status(thm)],[c_1338])).

tff(c_1927,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_1915,c_106])).

tff(c_1945,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_8])).

tff(c_1914,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_1338])).

tff(c_1960,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1914])).

tff(c_1964,plain,(
    r1_tarski('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_1960,c_16])).

tff(c_1966,plain,
    ( '#skF_3' = '#skF_4'
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_1964,c_2])).

tff(c_1969,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1945,c_1966])).

tff(c_14,plain,(
    ! [B_5] : k2_zfmisc_1(k1_xboole_0,B_5) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1944,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_3',B_5) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1927,c_14])).

tff(c_2052,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_4',B_5) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_1969,c_1944])).

tff(c_26,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k2_zfmisc_1(A_18,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_54,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18
      | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_26])).

tff(c_132,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_136,plain,(
    ~ r1_tarski(k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_18,c_132])).

tff(c_140,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_136])).

tff(c_141,plain,(
    ! [A_18] :
      ( v1_funct_2(k1_xboole_0,A_18,k1_xboole_0)
      | k1_xboole_0 = A_18 ) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_1938,plain,(
    ! [A_18] :
      ( v1_funct_2('#skF_3',A_18,'#skF_3')
      | A_18 = '#skF_3' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1927,c_1927,c_1927,c_141])).

tff(c_2106,plain,(
    ! [A_243] :
      ( v1_funct_2('#skF_4',A_243,'#skF_4')
      | A_243 = '#skF_4' ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_1969,c_1969,c_1938])).

tff(c_1998,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1969,c_149])).

tff(c_2117,plain,(
    '#skF_1' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2106,c_1998])).

tff(c_81,plain,(
    ! [A_25,B_26] :
      ( r1_tarski(A_25,B_26)
      | ~ m1_subset_1(A_25,k1_zfmisc_1(B_26)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_81])).

tff(c_100,plain,
    ( k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4'
    | ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_85,c_91])).

tff(c_131,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_1','#skF_2'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_100])).

tff(c_2124,plain,(
    ~ r1_tarski(k2_zfmisc_1('#skF_4','#skF_2'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2117,c_131])).

tff(c_2129,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2052,c_2124])).

tff(c_2130,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_2333,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_2322,c_2130])).

tff(c_2347,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2153,c_2333])).

tff(c_2348,plain,(
    k2_zfmisc_1('#skF_1','#skF_2') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_100])).

tff(c_2351,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2348,c_44])).

tff(c_5046,plain,(
    ! [A_581,B_582,C_583] :
      ( k2_relset_1(A_581,B_582,C_583) = k2_relat_1(C_583)
      | ~ m1_subset_1(C_583,k1_zfmisc_1(k2_zfmisc_1(A_581,B_582))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5151,plain,(
    ! [C_600] :
      ( k2_relset_1('#skF_1','#skF_2',C_600) = k2_relat_1(C_600)
      | ~ m1_subset_1(C_600,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_5046])).

tff(c_5159,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2351,c_5151])).

tff(c_5162,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5159,c_42])).

tff(c_5327,plain,(
    ! [D_622,C_623,B_624,A_625] :
      ( m1_subset_1(D_622,k1_zfmisc_1(k2_zfmisc_1(C_623,B_624)))
      | ~ r1_tarski(k2_relat_1(D_622),B_624)
      | ~ m1_subset_1(D_622,k1_zfmisc_1(k2_zfmisc_1(C_623,A_625))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_5621,plain,(
    ! [A_664,C_665,B_666,A_667] :
      ( m1_subset_1(A_664,k1_zfmisc_1(k2_zfmisc_1(C_665,B_666)))
      | ~ r1_tarski(k2_relat_1(A_664),B_666)
      | ~ r1_tarski(A_664,k2_zfmisc_1(C_665,A_667)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5327])).

tff(c_5681,plain,(
    ! [A_670,B_671] :
      ( m1_subset_1(A_670,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_671)))
      | ~ r1_tarski(k2_relat_1(A_670),B_671)
      | ~ r1_tarski(A_670,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_5621])).

tff(c_10,plain,(
    ! [B_5,A_4] :
      ( k1_xboole_0 = B_5
      | k1_xboole_0 = A_4
      | k2_zfmisc_1(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2356,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_10])).

tff(c_2359,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_xboole_0 != '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2356])).

tff(c_2367,plain,(
    k1_xboole_0 != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2359])).

tff(c_2366,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_3502,plain,(
    ! [A_411,B_412,C_413] :
      ( k1_relset_1(A_411,B_412,C_413) = k1_relat_1(C_413)
      | ~ m1_subset_1(C_413,k1_zfmisc_1(k2_zfmisc_1(A_411,B_412))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_3543,plain,(
    ! [C_419] :
      ( k1_relset_1('#skF_1','#skF_2',C_419) = k1_relat_1(C_419)
      | ~ m1_subset_1(C_419,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_3502])).

tff(c_3551,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2351,c_3543])).

tff(c_3839,plain,(
    ! [B_464,A_465,C_466] :
      ( k1_xboole_0 = B_464
      | k1_relset_1(A_465,B_464,C_466) = A_465
      | ~ v1_funct_2(C_466,A_465,B_464)
      | ~ m1_subset_1(C_466,k1_zfmisc_1(k2_zfmisc_1(A_465,B_464))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3845,plain,(
    ! [C_466] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_466) = '#skF_1'
      | ~ v1_funct_2(C_466,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_466,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_3839])).

tff(c_3865,plain,(
    ! [C_467] :
      ( k1_relset_1('#skF_1','#skF_2',C_467) = '#skF_1'
      | ~ v1_funct_2(C_467,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_467,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_3845])).

tff(c_3868,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2351,c_3865])).

tff(c_3875,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_3551,c_3868])).

tff(c_2386,plain,(
    ! [A_278,B_279,C_280] :
      ( k1_relset_1(A_278,B_279,C_280) = k1_relat_1(C_280)
      | ~ m1_subset_1(C_280,k1_zfmisc_1(k2_zfmisc_1(A_278,B_279))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2468,plain,(
    ! [C_293] :
      ( k1_relset_1('#skF_1','#skF_2',C_293) = k1_relat_1(C_293)
      | ~ m1_subset_1(C_293,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_2386])).

tff(c_2476,plain,(
    k1_relset_1('#skF_1','#skF_2','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2351,c_2468])).

tff(c_2739,plain,(
    ! [B_332,A_333,C_334] :
      ( k1_xboole_0 = B_332
      | k1_relset_1(A_333,B_332,C_334) = A_333
      | ~ v1_funct_2(C_334,A_333,B_332)
      | ~ m1_subset_1(C_334,k1_zfmisc_1(k2_zfmisc_1(A_333,B_332))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2742,plain,(
    ! [C_334] :
      ( k1_xboole_0 = '#skF_2'
      | k1_relset_1('#skF_1','#skF_2',C_334) = '#skF_1'
      | ~ v1_funct_2(C_334,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_334,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_2739])).

tff(c_2765,plain,(
    ! [C_337] :
      ( k1_relset_1('#skF_1','#skF_2',C_337) = '#skF_1'
      | ~ v1_funct_2(C_337,'#skF_1','#skF_2')
      | ~ m1_subset_1(C_337,k1_zfmisc_1('#skF_4')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_80,c_2742])).

tff(c_2768,plain,
    ( k1_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_2351,c_2765])).

tff(c_2775,plain,(
    k1_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_2476,c_2768])).

tff(c_2549,plain,(
    ! [A_302,B_303,C_304] :
      ( k2_relset_1(A_302,B_303,C_304) = k2_relat_1(C_304)
      | ~ m1_subset_1(C_304,k1_zfmisc_1(k2_zfmisc_1(A_302,B_303))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2590,plain,(
    ! [C_310] :
      ( k2_relset_1('#skF_1','#skF_2',C_310) = k2_relat_1(C_310)
      | ~ m1_subset_1(C_310,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_2549])).

tff(c_2598,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2351,c_2590])).

tff(c_2601,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2598,c_42])).

tff(c_2656,plain,(
    ! [D_317,C_318,B_319,A_320] :
      ( m1_subset_1(D_317,k1_zfmisc_1(k2_zfmisc_1(C_318,B_319)))
      | ~ r1_tarski(k2_relat_1(D_317),B_319)
      | ~ m1_subset_1(D_317,k1_zfmisc_1(k2_zfmisc_1(C_318,A_320))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_2929,plain,(
    ! [A_358,C_359,B_360,A_361] :
      ( m1_subset_1(A_358,k1_zfmisc_1(k2_zfmisc_1(C_359,B_360)))
      | ~ r1_tarski(k2_relat_1(A_358),B_360)
      | ~ r1_tarski(A_358,k2_zfmisc_1(C_359,A_361)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2656])).

tff(c_3199,plain,(
    ! [A_386,B_387] :
      ( m1_subset_1(A_386,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_387)))
      | ~ r1_tarski(k2_relat_1(A_386),B_387)
      | ~ r1_tarski(A_386,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_2929])).

tff(c_3231,plain,(
    ! [A_389,B_390] :
      ( r1_tarski(A_389,k2_zfmisc_1('#skF_1',B_390))
      | ~ r1_tarski(k2_relat_1(A_389),B_390)
      | ~ r1_tarski(A_389,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_3199,c_16])).

tff(c_3242,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_2601,c_3231])).

tff(c_3251,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_3242])).

tff(c_2400,plain,(
    ! [A_278,B_279,A_6] :
      ( k1_relset_1(A_278,B_279,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_278,B_279)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2386])).

tff(c_3263,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_3251,c_2400])).

tff(c_3272,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2775,c_3263])).

tff(c_2823,plain,(
    ! [B_343,C_344,A_345] :
      ( k1_xboole_0 = B_343
      | v1_funct_2(C_344,A_345,B_343)
      | k1_relset_1(A_345,B_343,C_344) != A_345
      | ~ m1_subset_1(C_344,k1_zfmisc_1(k2_zfmisc_1(A_345,B_343))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_2842,plain,(
    ! [B_343,A_6,A_345] :
      ( k1_xboole_0 = B_343
      | v1_funct_2(A_6,A_345,B_343)
      | k1_relset_1(A_345,B_343,A_6) != A_345
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_345,B_343)) ) ),
    inference(resolution,[status(thm)],[c_18,c_2823])).

tff(c_3255,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_3251,c_2842])).

tff(c_3268,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_2366,c_3255])).

tff(c_3320,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3272,c_3268])).

tff(c_3368,plain,(
    ! [A_3] : r1_tarski('#skF_3',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3320,c_8])).

tff(c_2385,plain,(
    ~ r1_tarski('#skF_3',k2_relset_1('#skF_1','#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_101])).

tff(c_2600,plain,(
    ~ r1_tarski('#skF_3',k2_relat_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2598,c_2385])).

tff(c_3379,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_3368,c_2600])).

tff(c_3380,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_101])).

tff(c_3389,plain,(
    ! [A_394,B_395,C_396] :
      ( k2_relset_1(A_394,B_395,C_396) = k2_relat_1(C_396)
      | ~ m1_subset_1(C_396,k1_zfmisc_1(k2_zfmisc_1(A_394,B_395))) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_3445,plain,(
    ! [C_406] :
      ( k2_relset_1('#skF_1','#skF_2',C_406) = k2_relat_1(C_406)
      | ~ m1_subset_1(C_406,k1_zfmisc_1('#skF_4')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_3389])).

tff(c_3448,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_2351,c_3445])).

tff(c_3454,plain,(
    k2_relat_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_3380,c_3448])).

tff(c_3645,plain,(
    ! [D_433,C_434,B_435,A_436] :
      ( m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(C_434,B_435)))
      | ~ r1_tarski(k2_relat_1(D_433),B_435)
      | ~ m1_subset_1(D_433,k1_zfmisc_1(k2_zfmisc_1(C_434,A_436))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_3931,plain,(
    ! [A_474,C_475,B_476,A_477] :
      ( m1_subset_1(A_474,k1_zfmisc_1(k2_zfmisc_1(C_475,B_476)))
      | ~ r1_tarski(k2_relat_1(A_474),B_476)
      | ~ r1_tarski(A_474,k2_zfmisc_1(C_475,A_477)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3645])).

tff(c_4193,plain,(
    ! [A_499,B_500] :
      ( m1_subset_1(A_499,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_500)))
      | ~ r1_tarski(k2_relat_1(A_499),B_500)
      | ~ r1_tarski(A_499,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2348,c_3931])).

tff(c_4245,plain,(
    ! [A_503,B_504] :
      ( r1_tarski(A_503,k2_zfmisc_1('#skF_1',B_504))
      | ~ r1_tarski(k2_relat_1(A_503),B_504)
      | ~ r1_tarski(A_503,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_4193,c_16])).

tff(c_4256,plain,(
    ! [B_504] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_504))
      | ~ r1_tarski('#skF_3',B_504)
      | ~ r1_tarski('#skF_4','#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3454,c_4245])).

tff(c_4266,plain,(
    ! [B_505] :
      ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1',B_505))
      | ~ r1_tarski('#skF_3',B_505) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4256])).

tff(c_3516,plain,(
    ! [A_411,B_412,A_6] :
      ( k1_relset_1(A_411,B_412,A_6) = k1_relat_1(A_6)
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_411,B_412)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3502])).

tff(c_4277,plain,(
    ! [B_505] :
      ( k1_relset_1('#skF_1',B_505,'#skF_4') = k1_relat_1('#skF_4')
      | ~ r1_tarski('#skF_3',B_505) ) ),
    inference(resolution,[status(thm)],[c_4266,c_3516])).

tff(c_4353,plain,(
    ! [B_510] :
      ( k1_relset_1('#skF_1',B_510,'#skF_4') = '#skF_1'
      | ~ r1_tarski('#skF_3',B_510) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3875,c_4277])).

tff(c_4368,plain,(
    k1_relset_1('#skF_1','#skF_3','#skF_4') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_6,c_4353])).

tff(c_4437,plain,(
    ! [A_515] :
      ( r1_tarski(A_515,k2_zfmisc_1('#skF_1',k2_relat_1(A_515)))
      | ~ r1_tarski(A_515,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_6,c_4245])).

tff(c_4474,plain,
    ( r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3'))
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3454,c_4437])).

tff(c_4487,plain,(
    r1_tarski('#skF_4',k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4474])).

tff(c_3738,plain,(
    ! [B_448,C_449,A_450] :
      ( k1_xboole_0 = B_448
      | v1_funct_2(C_449,A_450,B_448)
      | k1_relset_1(A_450,B_448,C_449) != A_450
      | ~ m1_subset_1(C_449,k1_zfmisc_1(k2_zfmisc_1(A_450,B_448))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_3753,plain,(
    ! [B_448,A_6,A_450] :
      ( k1_xboole_0 = B_448
      | v1_funct_2(A_6,A_450,B_448)
      | k1_relset_1(A_450,B_448,A_6) != A_450
      | ~ r1_tarski(A_6,k2_zfmisc_1(A_450,B_448)) ) ),
    inference(resolution,[status(thm)],[c_18,c_3738])).

tff(c_4490,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3')
    | k1_relset_1('#skF_1','#skF_3','#skF_4') != '#skF_1' ),
    inference(resolution,[status(thm)],[c_4487,c_3753])).

tff(c_4506,plain,
    ( k1_xboole_0 = '#skF_3'
    | v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4368,c_4490])).

tff(c_4507,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_2366,c_4506])).

tff(c_3776,plain,(
    ! [D_455,A_456,B_457] :
      ( m1_subset_1(D_455,k1_zfmisc_1(k2_zfmisc_1(A_456,B_457)))
      | ~ r1_tarski(k2_relat_1(D_455),B_457)
      | ~ m1_subset_1(D_455,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_3645])).

tff(c_3810,plain,(
    ! [D_459,A_460,B_461] :
      ( r1_tarski(D_459,k2_zfmisc_1(A_460,B_461))
      | ~ r1_tarski(k2_relat_1(D_459),B_461)
      | ~ m1_subset_1(D_459,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_3776,c_16])).

tff(c_3817,plain,(
    ! [D_462,A_463] :
      ( r1_tarski(D_462,k2_zfmisc_1(A_463,k2_relat_1(D_462)))
      | ~ m1_subset_1(D_462,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(resolution,[status(thm)],[c_6,c_3810])).

tff(c_3831,plain,(
    ! [A_463] :
      ( r1_tarski('#skF_4',k2_zfmisc_1(A_463,'#skF_3'))
      | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_3454,c_3817])).

tff(c_3860,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_3831])).

tff(c_4238,plain,(
    ! [A_502] :
      ( m1_subset_1(A_502,k1_zfmisc_1(k1_xboole_0))
      | ~ r1_tarski(k2_relat_1(A_502),k1_xboole_0)
      | ~ r1_tarski(A_502,'#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_4193])).

tff(c_4241,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0)
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3454,c_4238])).

tff(c_4243,plain,
    ( m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0))
    | ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4241])).

tff(c_4244,plain,(
    ~ r1_tarski('#skF_3',k1_xboole_0) ),
    inference(negUnitSimplification,[status(thm)],[c_3860,c_4243])).

tff(c_4519,plain,(
    ~ r1_tarski('#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4507,c_4244])).

tff(c_4569,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4519])).

tff(c_4571,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_3831])).

tff(c_4611,plain,(
    r1_tarski('#skF_4',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_4571,c_16])).

tff(c_4622,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_4611,c_106])).

tff(c_4634,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2367,c_4622])).

tff(c_4636,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_2359])).

tff(c_4635,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_2359])).

tff(c_4648,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_4635])).

tff(c_4642,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4635,c_8])).

tff(c_4662,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4648,c_4642])).

tff(c_4715,plain,(
    ! [A_525,B_526,C_527] :
      ( k1_relset_1(A_525,B_526,C_527) = k1_relat_1(C_527)
      | ~ m1_subset_1(C_527,k1_zfmisc_1(k2_zfmisc_1(A_525,B_526))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_4802,plain,(
    ! [A_540,B_541,A_542] :
      ( k1_relset_1(A_540,B_541,A_542) = k1_relat_1(A_542)
      | ~ r1_tarski(A_542,k2_zfmisc_1(A_540,B_541)) ) ),
    inference(resolution,[status(thm)],[c_18,c_4715])).

tff(c_4817,plain,(
    ! [A_540,B_541] : k1_relset_1(A_540,B_541,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_4662,c_4802])).

tff(c_4657,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4648,c_46])).

tff(c_34,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_52,plain,(
    ! [B_19,C_20] :
      ( k1_relset_1(k1_xboole_0,B_19,C_20) = k1_xboole_0
      | ~ v1_funct_2(C_20,k1_xboole_0,B_19)
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_34])).

tff(c_4896,plain,(
    ! [B_559,C_560] :
      ( k1_relset_1('#skF_4',B_559,C_560) = '#skF_4'
      | ~ v1_funct_2(C_560,'#skF_4',B_559)
      | ~ m1_subset_1(C_560,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_4636,c_4636,c_4636,c_52])).

tff(c_4898,plain,
    ( k1_relset_1('#skF_4','#skF_2','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_4657,c_4896])).

tff(c_4904,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2351,c_4817,c_4898])).

tff(c_4909,plain,(
    ! [A_540,B_541] : k1_relset_1(A_540,B_541,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_4904,c_4817])).

tff(c_30,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_19))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_51,plain,(
    ! [C_20,B_19] :
      ( v1_funct_2(C_20,k1_xboole_0,B_19)
      | k1_relset_1(k1_xboole_0,B_19,C_20) != k1_xboole_0
      | ~ m1_subset_1(C_20,k1_zfmisc_1(k1_xboole_0)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_30])).

tff(c_5007,plain,(
    ! [C_578,B_579] :
      ( v1_funct_2(C_578,'#skF_4',B_579)
      | k1_relset_1('#skF_4',B_579,C_578) != '#skF_4'
      | ~ m1_subset_1(C_578,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4636,c_4636,c_4636,c_4636,c_51])).

tff(c_5009,plain,(
    ! [B_579] :
      ( v1_funct_2('#skF_4','#skF_4',B_579)
      | k1_relset_1('#skF_4',B_579,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_2351,c_5007])).

tff(c_5015,plain,(
    ! [B_579] : v1_funct_2('#skF_4','#skF_4',B_579) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4909,c_5009])).

tff(c_4654,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4648,c_2366])).

tff(c_5020,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_5015,c_4654])).

tff(c_5021,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_5698,plain,
    ( ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_3')
    | ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_5681,c_5021])).

tff(c_5717,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5162,c_5698])).

tff(c_5718,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5722,plain,(
    ! [A_3] : r1_tarski('#skF_1',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5718,c_8])).

tff(c_5720,plain,(
    ! [A_4] : k2_zfmisc_1(A_4,'#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5718,c_5718,c_12])).

tff(c_5719,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_5727,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5718,c_5719])).

tff(c_5756,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5720,c_5727,c_44])).

tff(c_5758,plain,(
    ! [A_675,B_676] :
      ( r1_tarski(A_675,B_676)
      | ~ m1_subset_1(A_675,k1_zfmisc_1(B_676)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_5762,plain,(
    r1_tarski('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_5756,c_5758])).

tff(c_5782,plain,(
    ! [B_681,A_682] :
      ( B_681 = A_682
      | ~ r1_tarski(B_681,A_682)
      | ~ r1_tarski(A_682,B_681) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_5784,plain,
    ( '#skF_1' = '#skF_4'
    | ~ r1_tarski('#skF_1','#skF_4') ),
    inference(resolution,[status(thm)],[c_5762,c_5782])).

tff(c_5793,plain,(
    '#skF_1' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5722,c_5784])).

tff(c_5810,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5793,c_5718])).

tff(c_5816,plain,(
    ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_5829,plain,(
    ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5810,c_5810,c_5816])).

tff(c_5832,plain,(
    ~ r1_tarski('#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_18,c_5829])).

tff(c_5836,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_5832])).

tff(c_5838,plain,(
    m1_subset_1(k1_xboole_0,k1_zfmisc_1(k1_xboole_0)) ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_5851,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5810,c_5810,c_5838])).

tff(c_5808,plain,(
    ! [A_3] : r1_tarski('#skF_4',A_3) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5793,c_5722])).

tff(c_5910,plain,(
    ! [A_691,B_692,C_693] :
      ( k1_relset_1(A_691,B_692,C_693) = k1_relat_1(C_693)
      | ~ m1_subset_1(C_693,k1_zfmisc_1(k2_zfmisc_1(A_691,B_692))) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_5984,plain,(
    ! [A_704,B_705,A_706] :
      ( k1_relset_1(A_704,B_705,A_706) = k1_relat_1(A_706)
      | ~ r1_tarski(A_706,k2_zfmisc_1(A_704,B_705)) ) ),
    inference(resolution,[status(thm)],[c_18,c_5910])).

tff(c_5999,plain,(
    ! [A_704,B_705] : k1_relset_1(A_704,B_705,'#skF_4') = k1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_5808,c_5984])).

tff(c_5740,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5727,c_46])).

tff(c_5806,plain,(
    v1_funct_2('#skF_4','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5793,c_5793,c_5740])).

tff(c_6074,plain,(
    ! [B_719,C_720] :
      ( k1_relset_1('#skF_4',B_719,C_720) = '#skF_4'
      | ~ v1_funct_2(C_720,'#skF_4',B_719)
      | ~ m1_subset_1(C_720,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5810,c_5810,c_5810,c_5810,c_52])).

tff(c_6076,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_4') = '#skF_4'
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1('#skF_4')) ),
    inference(resolution,[status(thm)],[c_5806,c_6074])).

tff(c_6082,plain,(
    k1_relat_1('#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5851,c_5999,c_6076])).

tff(c_6087,plain,(
    ! [A_704,B_705] : k1_relset_1(A_704,B_705,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6082,c_5999])).

tff(c_6181,plain,(
    ! [C_739,B_740] :
      ( v1_funct_2(C_739,'#skF_4',B_740)
      | k1_relset_1('#skF_4',B_740,C_739) != '#skF_4'
      | ~ m1_subset_1(C_739,k1_zfmisc_1('#skF_4')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5810,c_5810,c_5810,c_5810,c_51])).

tff(c_6183,plain,(
    ! [B_740] :
      ( v1_funct_2('#skF_4','#skF_4',B_740)
      | k1_relset_1('#skF_4',B_740,'#skF_4') != '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_5851,c_6181])).

tff(c_6189,plain,(
    ! [B_740] : v1_funct_2('#skF_4','#skF_4',B_740) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6087,c_6183])).

tff(c_5721,plain,(
    ! [B_5] : k2_zfmisc_1('#skF_1',B_5) = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5718,c_5718,c_14])).

tff(c_5764,plain,(
    ~ v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5756,c_5721,c_50])).

tff(c_5802,plain,(
    ~ v1_funct_2('#skF_4','#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_5793,c_5764])).

tff(c_6194,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6189,c_5802])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.54/2.11  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.18  
% 6.00/2.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.18  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v1_funct_1 > k2_relset_1 > k1_relset_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.00/2.18  
% 6.00/2.18  %Foreground sorts:
% 6.00/2.18  
% 6.00/2.18  
% 6.00/2.18  %Background operators:
% 6.00/2.18  
% 6.00/2.18  
% 6.00/2.18  %Foreground operators:
% 6.00/2.18  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 6.00/2.18  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 6.00/2.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.00/2.18  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 6.00/2.18  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 6.00/2.18  tff('#skF_2', type, '#skF_2': $i).
% 6.00/2.18  tff('#skF_3', type, '#skF_3': $i).
% 6.00/2.18  tff('#skF_1', type, '#skF_1': $i).
% 6.00/2.18  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 6.00/2.18  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 6.00/2.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 6.00/2.18  tff('#skF_4', type, '#skF_4': $i).
% 6.00/2.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.18  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 6.00/2.18  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 6.00/2.18  
% 6.00/2.23  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 6.00/2.23  tff(f_95, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r1_tarski(k2_relset_1(A, B, D), C) => (((B = k1_xboole_0) & ~(A = k1_xboole_0)) | ((v1_funct_1(D) & v1_funct_2(D, A, C)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_funct_2)).
% 6.00/2.23  tff(f_51, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 6.00/2.23  tff(f_57, axiom, (![A, B, C, D]: (m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, A))) => (r1_tarski(k2_relat_1(D), B) => m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(C, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_relset_1)).
% 6.00/2.23  tff(f_47, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 6.00/2.23  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 6.00/2.23  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 6.00/2.23  tff(f_43, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 6.00/2.23  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 6.00/2.23  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.00/2.23  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.00/2.23  tff(c_2137, plain, (![A_244, B_245, C_246]: (k2_relset_1(A_244, B_245, C_246)=k2_relat_1(C_246) | ~m1_subset_1(C_246, k1_zfmisc_1(k2_zfmisc_1(A_244, B_245))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.00/2.23  tff(c_2152, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2137])).
% 6.00/2.23  tff(c_42, plain, (r1_tarski(k2_relset_1('#skF_1', '#skF_2', '#skF_4'), '#skF_3')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.00/2.23  tff(c_2153, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2152, c_42])).
% 6.00/2.23  tff(c_2250, plain, (![D_262, C_263, B_264, A_265]: (m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(C_263, B_264))) | ~r1_tarski(k2_relat_1(D_262), B_264) | ~m1_subset_1(D_262, k1_zfmisc_1(k2_zfmisc_1(C_263, A_265))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.00/2.23  tff(c_2322, plain, (![B_276]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_276))) | ~r1_tarski(k2_relat_1('#skF_4'), B_276))), inference(resolution, [status(thm)], [c_44, c_2250])).
% 6.00/2.23  tff(c_40, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.00/2.23  tff(c_80, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 6.00/2.23  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.00/2.23  tff(c_150, plain, (![A_35, B_36, C_37]: (k1_relset_1(A_35, B_36, C_37)=k1_relat_1(C_37) | ~m1_subset_1(C_37, k1_zfmisc_1(k2_zfmisc_1(A_35, B_36))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.00/2.23  tff(c_165, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_150])).
% 6.00/2.23  tff(c_1491, plain, (![B_187, A_188, C_189]: (k1_xboole_0=B_187 | k1_relset_1(A_188, B_187, C_189)=A_188 | ~v1_funct_2(C_189, A_188, B_187) | ~m1_subset_1(C_189, k1_zfmisc_1(k2_zfmisc_1(A_188, B_187))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_1501, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_1491])).
% 6.00/2.24  tff(c_1512, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_165, c_1501])).
% 6.00/2.24  tff(c_1513, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_80, c_1512])).
% 6.00/2.24  tff(c_231, plain, (![A_48, B_49, C_50]: (k2_relset_1(A_48, B_49, C_50)=k2_relat_1(C_50) | ~m1_subset_1(C_50, k1_zfmisc_1(k2_zfmisc_1(A_48, B_49))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.00/2.24  tff(c_246, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_231])).
% 6.00/2.24  tff(c_248, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_42])).
% 6.00/2.24  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.00/2.24  tff(c_38, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | ~v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_95])).
% 6.00/2.24  tff(c_50, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_38])).
% 6.00/2.24  tff(c_149, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 6.00/2.24  tff(c_354, plain, (![D_68, C_69, B_70, A_71]: (m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(C_69, B_70))) | ~r1_tarski(k2_relat_1(D_68), B_70) | ~m1_subset_1(D_68, k1_zfmisc_1(k2_zfmisc_1(C_69, A_71))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.00/2.24  tff(c_367, plain, (![B_72]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_72))) | ~r1_tarski(k2_relat_1('#skF_4'), B_72))), inference(resolution, [status(thm)], [c_44, c_354])).
% 6.00/2.24  tff(c_20, plain, (![A_8, B_9, C_10]: (k1_relset_1(A_8, B_9, C_10)=k1_relat_1(C_10) | ~m1_subset_1(C_10, k1_zfmisc_1(k2_zfmisc_1(A_8, B_9))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.00/2.24  tff(c_426, plain, (![B_76]: (k1_relset_1('#skF_1', B_76, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), B_76))), inference(resolution, [status(thm)], [c_367, c_20])).
% 6.00/2.24  tff(c_434, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_248, c_426])).
% 6.00/2.24  tff(c_365, plain, (![B_70]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_70))) | ~r1_tarski(k2_relat_1('#skF_4'), B_70))), inference(resolution, [status(thm)], [c_44, c_354])).
% 6.00/2.24  tff(c_554, plain, (![B_91, C_92, A_93]: (k1_xboole_0=B_91 | v1_funct_2(C_92, A_93, B_91) | k1_relset_1(A_93, B_91, C_92)!=A_93 | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_91))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_612, plain, (![B_100]: (k1_xboole_0=B_100 | v1_funct_2('#skF_4', '#skF_1', B_100) | k1_relset_1('#skF_1', B_100, '#skF_4')!='#skF_1' | ~r1_tarski(k2_relat_1('#skF_4'), B_100))), inference(resolution, [status(thm)], [c_365, c_554])).
% 6.00/2.24  tff(c_615, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_248, c_612])).
% 6.00/2.24  tff(c_621, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_434, c_615])).
% 6.00/2.24  tff(c_622, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_149, c_621])).
% 6.00/2.24  tff(c_629, plain, (k1_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_622])).
% 6.00/2.24  tff(c_669, plain, (![B_103, A_104, C_105]: (k1_xboole_0=B_103 | k1_relset_1(A_104, B_103, C_105)=A_104 | ~v1_funct_2(C_105, A_104, B_103) | ~m1_subset_1(C_105, k1_zfmisc_1(k2_zfmisc_1(A_104, B_103))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_682, plain, (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_669])).
% 6.00/2.24  tff(c_694, plain, (k1_xboole_0='#skF_2' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_165, c_682])).
% 6.00/2.24  tff(c_696, plain, $false, inference(negUnitSimplification, [status(thm)], [c_629, c_80, c_694])).
% 6.00/2.24  tff(c_697, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_622])).
% 6.00/2.24  tff(c_12, plain, (![A_4]: (k2_zfmisc_1(A_4, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.00/2.24  tff(c_382, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_367])).
% 6.00/2.24  tff(c_387, plain, (~r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(splitLeft, [status(thm)], [c_382])).
% 6.00/2.24  tff(c_710, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_697, c_387])).
% 6.00/2.24  tff(c_731, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_248, c_710])).
% 6.00/2.24  tff(c_732, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_382])).
% 6.00/2.24  tff(c_16, plain, (![A_6, B_7]: (r1_tarski(A_6, B_7) | ~m1_subset_1(A_6, k1_zfmisc_1(B_7)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.00/2.24  tff(c_749, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_732, c_16])).
% 6.00/2.24  tff(c_8, plain, (![A_3]: (r1_tarski(k1_xboole_0, A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.00/2.24  tff(c_91, plain, (![B_29, A_30]: (B_29=A_30 | ~r1_tarski(B_29, A_30) | ~r1_tarski(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.00/2.24  tff(c_106, plain, (![A_3]: (k1_xboole_0=A_3 | ~r1_tarski(A_3, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_91])).
% 6.00/2.24  tff(c_767, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_749, c_106])).
% 6.00/2.24  tff(c_799, plain, ('#skF_2'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_767, c_80])).
% 6.00/2.24  tff(c_36, plain, (![B_19, A_18, C_20]: (k1_xboole_0=B_19 | k1_relset_1(A_18, B_19, C_20)=A_18 | ~v1_funct_2(C_20, A_18, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_989, plain, (![B_120, A_121, C_122]: (B_120='#skF_4' | k1_relset_1(A_121, B_120, C_122)=A_121 | ~v1_funct_2(C_122, A_121, B_120) | ~m1_subset_1(C_122, k1_zfmisc_1(k2_zfmisc_1(A_121, B_120))))), inference(demodulation, [status(thm), theory('equality')], [c_767, c_36])).
% 6.00/2.24  tff(c_1002, plain, ('#skF_2'='#skF_4' | k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_44, c_989])).
% 6.00/2.24  tff(c_1007, plain, ('#skF_2'='#skF_4' | k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_165, c_1002])).
% 6.00/2.24  tff(c_1008, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_799, c_1007])).
% 6.00/2.24  tff(c_802, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_767, c_8])).
% 6.00/2.24  tff(c_18, plain, (![A_6, B_7]: (m1_subset_1(A_6, k1_zfmisc_1(B_7)) | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.00/2.24  tff(c_1183, plain, (![A_141, B_142, A_143]: (k1_relset_1(A_141, B_142, A_143)=k1_relat_1(A_143) | ~r1_tarski(A_143, k2_zfmisc_1(A_141, B_142)))), inference(resolution, [status(thm)], [c_18, c_150])).
% 6.00/2.24  tff(c_1193, plain, (![A_141, B_142]: (k1_relset_1(A_141, B_142, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_802, c_1183])).
% 6.00/2.24  tff(c_1199, plain, (![A_141, B_142]: (k1_relset_1(A_141, B_142, '#skF_4')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1008, c_1193])).
% 6.00/2.24  tff(c_733, plain, (r1_tarski(k2_relat_1('#skF_4'), k1_xboole_0)), inference(splitRight, [status(thm)], [c_382])).
% 6.00/2.24  tff(c_820, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_767, c_733])).
% 6.00/2.24  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.00/2.24  tff(c_822, plain, (k2_relat_1('#skF_4')='#skF_4' | ~r1_tarski('#skF_4', k2_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_820, c_2])).
% 6.00/2.24  tff(c_825, plain, (k2_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_802, c_822])).
% 6.00/2.24  tff(c_833, plain, (![B_70]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_70))) | ~r1_tarski('#skF_4', B_70))), inference(demodulation, [status(thm), theory('equality')], [c_825, c_365])).
% 6.00/2.24  tff(c_1087, plain, (![B_131]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_131))))), inference(demodulation, [status(thm), theory('equality')], [c_802, c_833])).
% 6.00/2.24  tff(c_32, plain, (![B_19, C_20, A_18]: (k1_xboole_0=B_19 | v1_funct_2(C_20, A_18, B_19) | k1_relset_1(A_18, B_19, C_20)!=A_18 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_1057, plain, (![B_19, C_20, A_18]: (B_19='#skF_4' | v1_funct_2(C_20, A_18, B_19) | k1_relset_1(A_18, B_19, C_20)!=A_18 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(A_18, B_19))))), inference(demodulation, [status(thm), theory('equality')], [c_767, c_32])).
% 6.00/2.24  tff(c_1108, plain, (![B_131]: (B_131='#skF_4' | v1_funct_2('#skF_4', '#skF_1', B_131) | k1_relset_1('#skF_1', B_131, '#skF_4')!='#skF_1')), inference(resolution, [status(thm)], [c_1087, c_1057])).
% 6.00/2.24  tff(c_1224, plain, (![B_148]: (B_148='#skF_4' | v1_funct_2('#skF_4', '#skF_1', B_148))), inference(demodulation, [status(thm), theory('equality')], [c_1199, c_1108])).
% 6.00/2.24  tff(c_1228, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1224, c_149])).
% 6.00/2.24  tff(c_101, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3' | ~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_42, c_91])).
% 6.00/2.24  tff(c_185, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_101])).
% 6.00/2.24  tff(c_247, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_246, c_185])).
% 6.00/2.24  tff(c_834, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_825, c_247])).
% 6.00/2.24  tff(c_1229, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1228, c_834])).
% 6.00/2.24  tff(c_1233, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1229])).
% 6.00/2.24  tff(c_1234, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_101])).
% 6.00/2.24  tff(c_1262, plain, (![A_153, B_154, C_155]: (k2_relset_1(A_153, B_154, C_155)=k2_relat_1(C_155) | ~m1_subset_1(C_155, k1_zfmisc_1(k2_zfmisc_1(A_153, B_154))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.00/2.24  tff(c_1269, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1262])).
% 6.00/2.24  tff(c_1278, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1234, c_1269])).
% 6.00/2.24  tff(c_1309, plain, (![D_159, C_160, B_161, A_162]: (m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(C_160, B_161))) | ~r1_tarski(k2_relat_1(D_159), B_161) | ~m1_subset_1(D_159, k1_zfmisc_1(k2_zfmisc_1(C_160, A_162))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.00/2.24  tff(c_1314, plain, (![B_161]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_161))) | ~r1_tarski(k2_relat_1('#skF_4'), B_161))), inference(resolution, [status(thm)], [c_44, c_1309])).
% 6.00/2.24  tff(c_1323, plain, (![B_163]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_163))) | ~r1_tarski('#skF_3', B_163))), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1314])).
% 6.00/2.24  tff(c_1371, plain, (![B_168]: (k1_relset_1('#skF_1', B_168, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_168))), inference(resolution, [status(thm)], [c_1323, c_20])).
% 6.00/2.24  tff(c_1376, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_6, c_1371])).
% 6.00/2.24  tff(c_1515, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1513, c_1376])).
% 6.00/2.24  tff(c_1321, plain, (![B_161]: (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_161))) | ~r1_tarski('#skF_3', B_161))), inference(demodulation, [status(thm), theory('equality')], [c_1278, c_1314])).
% 6.00/2.24  tff(c_1658, plain, (![B_210, C_211, A_212]: (k1_xboole_0=B_210 | v1_funct_2(C_211, A_212, B_210) | k1_relset_1(A_212, B_210, C_211)!=A_212 | ~m1_subset_1(C_211, k1_zfmisc_1(k2_zfmisc_1(A_212, B_210))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_1862, plain, (![B_229]: (k1_xboole_0=B_229 | v1_funct_2('#skF_4', '#skF_1', B_229) | k1_relset_1('#skF_1', B_229, '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', B_229))), inference(resolution, [status(thm)], [c_1321, c_1658])).
% 6.00/2.24  tff(c_1868, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1' | ~r1_tarski('#skF_3', '#skF_3')), inference(resolution, [status(thm)], [c_1862, c_149])).
% 6.00/2.24  tff(c_1872, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_6, c_1515, c_1868])).
% 6.00/2.24  tff(c_1338, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_12, c_1323])).
% 6.00/2.24  tff(c_1345, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(splitLeft, [status(thm)], [c_1338])).
% 6.00/2.24  tff(c_1898, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1872, c_1345])).
% 6.00/2.24  tff(c_1913, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_1898])).
% 6.00/2.24  tff(c_1915, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(splitRight, [status(thm)], [c_1338])).
% 6.00/2.24  tff(c_1927, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_1915, c_106])).
% 6.00/2.24  tff(c_1945, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_8])).
% 6.00/2.24  tff(c_1914, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_1338])).
% 6.00/2.24  tff(c_1960, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1914])).
% 6.00/2.24  tff(c_1964, plain, (r1_tarski('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_1960, c_16])).
% 6.00/2.24  tff(c_1966, plain, ('#skF_3'='#skF_4' | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_1964, c_2])).
% 6.00/2.24  tff(c_1969, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1945, c_1966])).
% 6.00/2.24  tff(c_14, plain, (![B_5]: (k2_zfmisc_1(k1_xboole_0, B_5)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.00/2.24  tff(c_1944, plain, (![B_5]: (k2_zfmisc_1('#skF_3', B_5)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1927, c_14])).
% 6.00/2.24  tff(c_2052, plain, (![B_5]: (k2_zfmisc_1('#skF_4', B_5)='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1969, c_1969, c_1944])).
% 6.00/2.24  tff(c_26, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k2_zfmisc_1(A_18, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_54, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18 | ~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_26])).
% 6.00/2.24  tff(c_132, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_54])).
% 6.00/2.24  tff(c_136, plain, (~r1_tarski(k1_xboole_0, k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_132])).
% 6.00/2.24  tff(c_140, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_136])).
% 6.00/2.24  tff(c_141, plain, (![A_18]: (v1_funct_2(k1_xboole_0, A_18, k1_xboole_0) | k1_xboole_0=A_18)), inference(splitRight, [status(thm)], [c_54])).
% 6.00/2.24  tff(c_1938, plain, (![A_18]: (v1_funct_2('#skF_3', A_18, '#skF_3') | A_18='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_1927, c_1927, c_1927, c_141])).
% 6.00/2.24  tff(c_2106, plain, (![A_243]: (v1_funct_2('#skF_4', A_243, '#skF_4') | A_243='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1969, c_1969, c_1969, c_1938])).
% 6.00/2.24  tff(c_1998, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1969, c_149])).
% 6.00/2.24  tff(c_2117, plain, ('#skF_1'='#skF_4'), inference(resolution, [status(thm)], [c_2106, c_1998])).
% 6.00/2.24  tff(c_81, plain, (![A_25, B_26]: (r1_tarski(A_25, B_26) | ~m1_subset_1(A_25, k1_zfmisc_1(B_26)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.00/2.24  tff(c_85, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_81])).
% 6.00/2.24  tff(c_100, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4' | ~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(resolution, [status(thm)], [c_85, c_91])).
% 6.00/2.24  tff(c_131, plain, (~r1_tarski(k2_zfmisc_1('#skF_1', '#skF_2'), '#skF_4')), inference(splitLeft, [status(thm)], [c_100])).
% 6.00/2.24  tff(c_2124, plain, (~r1_tarski(k2_zfmisc_1('#skF_4', '#skF_2'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_2117, c_131])).
% 6.00/2.24  tff(c_2129, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_2052, c_2124])).
% 6.00/2.24  tff(c_2130, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 6.00/2.24  tff(c_2333, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_2322, c_2130])).
% 6.00/2.24  tff(c_2347, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2153, c_2333])).
% 6.00/2.24  tff(c_2348, plain, (k2_zfmisc_1('#skF_1', '#skF_2')='#skF_4'), inference(splitRight, [status(thm)], [c_100])).
% 6.00/2.24  tff(c_2351, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2348, c_44])).
% 6.00/2.24  tff(c_5046, plain, (![A_581, B_582, C_583]: (k2_relset_1(A_581, B_582, C_583)=k2_relat_1(C_583) | ~m1_subset_1(C_583, k1_zfmisc_1(k2_zfmisc_1(A_581, B_582))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.00/2.24  tff(c_5151, plain, (![C_600]: (k2_relset_1('#skF_1', '#skF_2', C_600)=k2_relat_1(C_600) | ~m1_subset_1(C_600, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_5046])).
% 6.00/2.24  tff(c_5159, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2351, c_5151])).
% 6.00/2.24  tff(c_5162, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5159, c_42])).
% 6.00/2.24  tff(c_5327, plain, (![D_622, C_623, B_624, A_625]: (m1_subset_1(D_622, k1_zfmisc_1(k2_zfmisc_1(C_623, B_624))) | ~r1_tarski(k2_relat_1(D_622), B_624) | ~m1_subset_1(D_622, k1_zfmisc_1(k2_zfmisc_1(C_623, A_625))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.00/2.24  tff(c_5621, plain, (![A_664, C_665, B_666, A_667]: (m1_subset_1(A_664, k1_zfmisc_1(k2_zfmisc_1(C_665, B_666))) | ~r1_tarski(k2_relat_1(A_664), B_666) | ~r1_tarski(A_664, k2_zfmisc_1(C_665, A_667)))), inference(resolution, [status(thm)], [c_18, c_5327])).
% 6.00/2.24  tff(c_5681, plain, (![A_670, B_671]: (m1_subset_1(A_670, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_671))) | ~r1_tarski(k2_relat_1(A_670), B_671) | ~r1_tarski(A_670, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_5621])).
% 6.00/2.24  tff(c_10, plain, (![B_5, A_4]: (k1_xboole_0=B_5 | k1_xboole_0=A_4 | k2_zfmisc_1(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 6.00/2.24  tff(c_2356, plain, (k1_xboole_0='#skF_2' | k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_2348, c_10])).
% 6.00/2.24  tff(c_2359, plain, (k1_xboole_0='#skF_1' | k1_xboole_0!='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_80, c_2356])).
% 6.00/2.24  tff(c_2367, plain, (k1_xboole_0!='#skF_4'), inference(splitLeft, [status(thm)], [c_2359])).
% 6.00/2.24  tff(c_2366, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_50])).
% 6.00/2.24  tff(c_3502, plain, (![A_411, B_412, C_413]: (k1_relset_1(A_411, B_412, C_413)=k1_relat_1(C_413) | ~m1_subset_1(C_413, k1_zfmisc_1(k2_zfmisc_1(A_411, B_412))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.00/2.24  tff(c_3543, plain, (![C_419]: (k1_relset_1('#skF_1', '#skF_2', C_419)=k1_relat_1(C_419) | ~m1_subset_1(C_419, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_3502])).
% 6.00/2.24  tff(c_3551, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2351, c_3543])).
% 6.00/2.24  tff(c_3839, plain, (![B_464, A_465, C_466]: (k1_xboole_0=B_464 | k1_relset_1(A_465, B_464, C_466)=A_465 | ~v1_funct_2(C_466, A_465, B_464) | ~m1_subset_1(C_466, k1_zfmisc_1(k2_zfmisc_1(A_465, B_464))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_3845, plain, (![C_466]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_466)='#skF_1' | ~v1_funct_2(C_466, '#skF_1', '#skF_2') | ~m1_subset_1(C_466, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_3839])).
% 6.00/2.24  tff(c_3865, plain, (![C_467]: (k1_relset_1('#skF_1', '#skF_2', C_467)='#skF_1' | ~v1_funct_2(C_467, '#skF_1', '#skF_2') | ~m1_subset_1(C_467, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_3845])).
% 6.00/2.24  tff(c_3868, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2351, c_3865])).
% 6.00/2.24  tff(c_3875, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_3551, c_3868])).
% 6.00/2.24  tff(c_2386, plain, (![A_278, B_279, C_280]: (k1_relset_1(A_278, B_279, C_280)=k1_relat_1(C_280) | ~m1_subset_1(C_280, k1_zfmisc_1(k2_zfmisc_1(A_278, B_279))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.00/2.24  tff(c_2468, plain, (![C_293]: (k1_relset_1('#skF_1', '#skF_2', C_293)=k1_relat_1(C_293) | ~m1_subset_1(C_293, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_2386])).
% 6.00/2.24  tff(c_2476, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2351, c_2468])).
% 6.00/2.24  tff(c_2739, plain, (![B_332, A_333, C_334]: (k1_xboole_0=B_332 | k1_relset_1(A_333, B_332, C_334)=A_333 | ~v1_funct_2(C_334, A_333, B_332) | ~m1_subset_1(C_334, k1_zfmisc_1(k2_zfmisc_1(A_333, B_332))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_2742, plain, (![C_334]: (k1_xboole_0='#skF_2' | k1_relset_1('#skF_1', '#skF_2', C_334)='#skF_1' | ~v1_funct_2(C_334, '#skF_1', '#skF_2') | ~m1_subset_1(C_334, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_2739])).
% 6.00/2.24  tff(c_2765, plain, (![C_337]: (k1_relset_1('#skF_1', '#skF_2', C_337)='#skF_1' | ~v1_funct_2(C_337, '#skF_1', '#skF_2') | ~m1_subset_1(C_337, k1_zfmisc_1('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_80, c_2742])).
% 6.00/2.24  tff(c_2768, plain, (k1_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_1' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_2351, c_2765])).
% 6.00/2.24  tff(c_2775, plain, (k1_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_46, c_2476, c_2768])).
% 6.00/2.24  tff(c_2549, plain, (![A_302, B_303, C_304]: (k2_relset_1(A_302, B_303, C_304)=k2_relat_1(C_304) | ~m1_subset_1(C_304, k1_zfmisc_1(k2_zfmisc_1(A_302, B_303))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.00/2.24  tff(c_2590, plain, (![C_310]: (k2_relset_1('#skF_1', '#skF_2', C_310)=k2_relat_1(C_310) | ~m1_subset_1(C_310, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_2549])).
% 6.00/2.24  tff(c_2598, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2351, c_2590])).
% 6.00/2.24  tff(c_2601, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2598, c_42])).
% 6.00/2.24  tff(c_2656, plain, (![D_317, C_318, B_319, A_320]: (m1_subset_1(D_317, k1_zfmisc_1(k2_zfmisc_1(C_318, B_319))) | ~r1_tarski(k2_relat_1(D_317), B_319) | ~m1_subset_1(D_317, k1_zfmisc_1(k2_zfmisc_1(C_318, A_320))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.00/2.24  tff(c_2929, plain, (![A_358, C_359, B_360, A_361]: (m1_subset_1(A_358, k1_zfmisc_1(k2_zfmisc_1(C_359, B_360))) | ~r1_tarski(k2_relat_1(A_358), B_360) | ~r1_tarski(A_358, k2_zfmisc_1(C_359, A_361)))), inference(resolution, [status(thm)], [c_18, c_2656])).
% 6.00/2.24  tff(c_3199, plain, (![A_386, B_387]: (m1_subset_1(A_386, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_387))) | ~r1_tarski(k2_relat_1(A_386), B_387) | ~r1_tarski(A_386, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_2929])).
% 6.00/2.24  tff(c_3231, plain, (![A_389, B_390]: (r1_tarski(A_389, k2_zfmisc_1('#skF_1', B_390)) | ~r1_tarski(k2_relat_1(A_389), B_390) | ~r1_tarski(A_389, '#skF_4'))), inference(resolution, [status(thm)], [c_3199, c_16])).
% 6.00/2.24  tff(c_3242, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_2601, c_3231])).
% 6.00/2.24  tff(c_3251, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_3242])).
% 6.00/2.24  tff(c_2400, plain, (![A_278, B_279, A_6]: (k1_relset_1(A_278, B_279, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_278, B_279)))), inference(resolution, [status(thm)], [c_18, c_2386])).
% 6.00/2.24  tff(c_3263, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')=k1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_3251, c_2400])).
% 6.00/2.24  tff(c_3272, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_2775, c_3263])).
% 6.00/2.24  tff(c_2823, plain, (![B_343, C_344, A_345]: (k1_xboole_0=B_343 | v1_funct_2(C_344, A_345, B_343) | k1_relset_1(A_345, B_343, C_344)!=A_345 | ~m1_subset_1(C_344, k1_zfmisc_1(k2_zfmisc_1(A_345, B_343))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_2842, plain, (![B_343, A_6, A_345]: (k1_xboole_0=B_343 | v1_funct_2(A_6, A_345, B_343) | k1_relset_1(A_345, B_343, A_6)!=A_345 | ~r1_tarski(A_6, k2_zfmisc_1(A_345, B_343)))), inference(resolution, [status(thm)], [c_18, c_2823])).
% 6.00/2.24  tff(c_3255, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_3251, c_2842])).
% 6.00/2.24  tff(c_3268, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_2366, c_3255])).
% 6.00/2.24  tff(c_3320, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3272, c_3268])).
% 6.00/2.24  tff(c_3368, plain, (![A_3]: (r1_tarski('#skF_3', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_3320, c_8])).
% 6.00/2.24  tff(c_2385, plain, (~r1_tarski('#skF_3', k2_relset_1('#skF_1', '#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_101])).
% 6.00/2.24  tff(c_2600, plain, (~r1_tarski('#skF_3', k2_relat_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_2598, c_2385])).
% 6.00/2.24  tff(c_3379, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_3368, c_2600])).
% 6.00/2.24  tff(c_3380, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')='#skF_3'), inference(splitRight, [status(thm)], [c_101])).
% 6.00/2.24  tff(c_3389, plain, (![A_394, B_395, C_396]: (k2_relset_1(A_394, B_395, C_396)=k2_relat_1(C_396) | ~m1_subset_1(C_396, k1_zfmisc_1(k2_zfmisc_1(A_394, B_395))))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.00/2.24  tff(c_3445, plain, (![C_406]: (k2_relset_1('#skF_1', '#skF_2', C_406)=k2_relat_1(C_406) | ~m1_subset_1(C_406, k1_zfmisc_1('#skF_4')))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_3389])).
% 6.00/2.24  tff(c_3448, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_2351, c_3445])).
% 6.00/2.24  tff(c_3454, plain, (k2_relat_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_3380, c_3448])).
% 6.00/2.24  tff(c_3645, plain, (![D_433, C_434, B_435, A_436]: (m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(C_434, B_435))) | ~r1_tarski(k2_relat_1(D_433), B_435) | ~m1_subset_1(D_433, k1_zfmisc_1(k2_zfmisc_1(C_434, A_436))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.00/2.24  tff(c_3931, plain, (![A_474, C_475, B_476, A_477]: (m1_subset_1(A_474, k1_zfmisc_1(k2_zfmisc_1(C_475, B_476))) | ~r1_tarski(k2_relat_1(A_474), B_476) | ~r1_tarski(A_474, k2_zfmisc_1(C_475, A_477)))), inference(resolution, [status(thm)], [c_18, c_3645])).
% 6.00/2.24  tff(c_4193, plain, (![A_499, B_500]: (m1_subset_1(A_499, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_500))) | ~r1_tarski(k2_relat_1(A_499), B_500) | ~r1_tarski(A_499, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_2348, c_3931])).
% 6.00/2.24  tff(c_4245, plain, (![A_503, B_504]: (r1_tarski(A_503, k2_zfmisc_1('#skF_1', B_504)) | ~r1_tarski(k2_relat_1(A_503), B_504) | ~r1_tarski(A_503, '#skF_4'))), inference(resolution, [status(thm)], [c_4193, c_16])).
% 6.00/2.24  tff(c_4256, plain, (![B_504]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_504)) | ~r1_tarski('#skF_3', B_504) | ~r1_tarski('#skF_4', '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_3454, c_4245])).
% 6.00/2.24  tff(c_4266, plain, (![B_505]: (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', B_505)) | ~r1_tarski('#skF_3', B_505))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4256])).
% 6.00/2.24  tff(c_3516, plain, (![A_411, B_412, A_6]: (k1_relset_1(A_411, B_412, A_6)=k1_relat_1(A_6) | ~r1_tarski(A_6, k2_zfmisc_1(A_411, B_412)))), inference(resolution, [status(thm)], [c_18, c_3502])).
% 6.00/2.24  tff(c_4277, plain, (![B_505]: (k1_relset_1('#skF_1', B_505, '#skF_4')=k1_relat_1('#skF_4') | ~r1_tarski('#skF_3', B_505))), inference(resolution, [status(thm)], [c_4266, c_3516])).
% 6.00/2.24  tff(c_4353, plain, (![B_510]: (k1_relset_1('#skF_1', B_510, '#skF_4')='#skF_1' | ~r1_tarski('#skF_3', B_510))), inference(demodulation, [status(thm), theory('equality')], [c_3875, c_4277])).
% 6.00/2.24  tff(c_4368, plain, (k1_relset_1('#skF_1', '#skF_3', '#skF_4')='#skF_1'), inference(resolution, [status(thm)], [c_6, c_4353])).
% 6.00/2.24  tff(c_4437, plain, (![A_515]: (r1_tarski(A_515, k2_zfmisc_1('#skF_1', k2_relat_1(A_515))) | ~r1_tarski(A_515, '#skF_4'))), inference(resolution, [status(thm)], [c_6, c_4245])).
% 6.00/2.24  tff(c_4474, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3')) | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3454, c_4437])).
% 6.00/2.24  tff(c_4487, plain, (r1_tarski('#skF_4', k2_zfmisc_1('#skF_1', '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4474])).
% 6.00/2.24  tff(c_3738, plain, (![B_448, C_449, A_450]: (k1_xboole_0=B_448 | v1_funct_2(C_449, A_450, B_448) | k1_relset_1(A_450, B_448, C_449)!=A_450 | ~m1_subset_1(C_449, k1_zfmisc_1(k2_zfmisc_1(A_450, B_448))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_3753, plain, (![B_448, A_6, A_450]: (k1_xboole_0=B_448 | v1_funct_2(A_6, A_450, B_448) | k1_relset_1(A_450, B_448, A_6)!=A_450 | ~r1_tarski(A_6, k2_zfmisc_1(A_450, B_448)))), inference(resolution, [status(thm)], [c_18, c_3738])).
% 6.00/2.24  tff(c_4490, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3') | k1_relset_1('#skF_1', '#skF_3', '#skF_4')!='#skF_1'), inference(resolution, [status(thm)], [c_4487, c_3753])).
% 6.00/2.24  tff(c_4506, plain, (k1_xboole_0='#skF_3' | v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4368, c_4490])).
% 6.00/2.24  tff(c_4507, plain, (k1_xboole_0='#skF_3'), inference(negUnitSimplification, [status(thm)], [c_2366, c_4506])).
% 6.00/2.24  tff(c_3776, plain, (![D_455, A_456, B_457]: (m1_subset_1(D_455, k1_zfmisc_1(k2_zfmisc_1(A_456, B_457))) | ~r1_tarski(k2_relat_1(D_455), B_457) | ~m1_subset_1(D_455, k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_12, c_3645])).
% 6.00/2.24  tff(c_3810, plain, (![D_459, A_460, B_461]: (r1_tarski(D_459, k2_zfmisc_1(A_460, B_461)) | ~r1_tarski(k2_relat_1(D_459), B_461) | ~m1_subset_1(D_459, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_3776, c_16])).
% 6.00/2.24  tff(c_3817, plain, (![D_462, A_463]: (r1_tarski(D_462, k2_zfmisc_1(A_463, k2_relat_1(D_462))) | ~m1_subset_1(D_462, k1_zfmisc_1(k1_xboole_0)))), inference(resolution, [status(thm)], [c_6, c_3810])).
% 6.00/2.24  tff(c_3831, plain, (![A_463]: (r1_tarski('#skF_4', k2_zfmisc_1(A_463, '#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_3454, c_3817])).
% 6.00/2.24  tff(c_3860, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_3831])).
% 6.00/2.24  tff(c_4238, plain, (![A_502]: (m1_subset_1(A_502, k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski(k2_relat_1(A_502), k1_xboole_0) | ~r1_tarski(A_502, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_12, c_4193])).
% 6.00/2.24  tff(c_4241, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0) | ~r1_tarski('#skF_4', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3454, c_4238])).
% 6.00/2.24  tff(c_4243, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0)) | ~r1_tarski('#skF_3', k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4241])).
% 6.00/2.24  tff(c_4244, plain, (~r1_tarski('#skF_3', k1_xboole_0)), inference(negUnitSimplification, [status(thm)], [c_3860, c_4243])).
% 6.00/2.24  tff(c_4519, plain, (~r1_tarski('#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4507, c_4244])).
% 6.00/2.24  tff(c_4569, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_4519])).
% 6.00/2.24  tff(c_4571, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_3831])).
% 6.00/2.24  tff(c_4611, plain, (r1_tarski('#skF_4', k1_xboole_0)), inference(resolution, [status(thm)], [c_4571, c_16])).
% 6.00/2.24  tff(c_4622, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_4611, c_106])).
% 6.00/2.24  tff(c_4634, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2367, c_4622])).
% 6.00/2.24  tff(c_4636, plain, (k1_xboole_0='#skF_4'), inference(splitRight, [status(thm)], [c_2359])).
% 6.00/2.24  tff(c_4635, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_2359])).
% 6.00/2.24  tff(c_4648, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_4635])).
% 6.00/2.24  tff(c_4642, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4635, c_8])).
% 6.00/2.24  tff(c_4662, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_4648, c_4642])).
% 6.00/2.24  tff(c_4715, plain, (![A_525, B_526, C_527]: (k1_relset_1(A_525, B_526, C_527)=k1_relat_1(C_527) | ~m1_subset_1(C_527, k1_zfmisc_1(k2_zfmisc_1(A_525, B_526))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.00/2.24  tff(c_4802, plain, (![A_540, B_541, A_542]: (k1_relset_1(A_540, B_541, A_542)=k1_relat_1(A_542) | ~r1_tarski(A_542, k2_zfmisc_1(A_540, B_541)))), inference(resolution, [status(thm)], [c_18, c_4715])).
% 6.00/2.24  tff(c_4817, plain, (![A_540, B_541]: (k1_relset_1(A_540, B_541, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_4662, c_4802])).
% 6.00/2.24  tff(c_4657, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4648, c_46])).
% 6.00/2.24  tff(c_34, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_52, plain, (![B_19, C_20]: (k1_relset_1(k1_xboole_0, B_19, C_20)=k1_xboole_0 | ~v1_funct_2(C_20, k1_xboole_0, B_19) | ~m1_subset_1(C_20, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_34])).
% 6.00/2.24  tff(c_4896, plain, (![B_559, C_560]: (k1_relset_1('#skF_4', B_559, C_560)='#skF_4' | ~v1_funct_2(C_560, '#skF_4', B_559) | ~m1_subset_1(C_560, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_4636, c_4636, c_4636, c_52])).
% 6.00/2.24  tff(c_4898, plain, (k1_relset_1('#skF_4', '#skF_2', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_4657, c_4896])).
% 6.00/2.24  tff(c_4904, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_2351, c_4817, c_4898])).
% 6.00/2.24  tff(c_4909, plain, (![A_540, B_541]: (k1_relset_1(A_540, B_541, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_4904, c_4817])).
% 6.00/2.24  tff(c_30, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_19))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.00/2.24  tff(c_51, plain, (![C_20, B_19]: (v1_funct_2(C_20, k1_xboole_0, B_19) | k1_relset_1(k1_xboole_0, B_19, C_20)!=k1_xboole_0 | ~m1_subset_1(C_20, k1_zfmisc_1(k1_xboole_0)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_30])).
% 6.00/2.24  tff(c_5007, plain, (![C_578, B_579]: (v1_funct_2(C_578, '#skF_4', B_579) | k1_relset_1('#skF_4', B_579, C_578)!='#skF_4' | ~m1_subset_1(C_578, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_4636, c_4636, c_4636, c_4636, c_51])).
% 6.00/2.24  tff(c_5009, plain, (![B_579]: (v1_funct_2('#skF_4', '#skF_4', B_579) | k1_relset_1('#skF_4', B_579, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_2351, c_5007])).
% 6.00/2.24  tff(c_5015, plain, (![B_579]: (v1_funct_2('#skF_4', '#skF_4', B_579))), inference(demodulation, [status(thm), theory('equality')], [c_4909, c_5009])).
% 6.00/2.24  tff(c_4654, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_4648, c_2366])).
% 6.00/2.24  tff(c_5020, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_5015, c_4654])).
% 6.00/2.24  tff(c_5021, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(splitRight, [status(thm)], [c_50])).
% 6.00/2.24  tff(c_5698, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_3') | ~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_5681, c_5021])).
% 6.00/2.24  tff(c_5717, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5162, c_5698])).
% 6.00/2.24  tff(c_5718, plain, (k1_xboole_0='#skF_1'), inference(splitRight, [status(thm)], [c_40])).
% 6.00/2.24  tff(c_5722, plain, (![A_3]: (r1_tarski('#skF_1', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5718, c_8])).
% 6.00/2.24  tff(c_5720, plain, (![A_4]: (k2_zfmisc_1(A_4, '#skF_1')='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5718, c_5718, c_12])).
% 6.00/2.24  tff(c_5719, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 6.00/2.24  tff(c_5727, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_5718, c_5719])).
% 6.00/2.24  tff(c_5756, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_5720, c_5727, c_44])).
% 6.00/2.24  tff(c_5758, plain, (![A_675, B_676]: (r1_tarski(A_675, B_676) | ~m1_subset_1(A_675, k1_zfmisc_1(B_676)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.00/2.24  tff(c_5762, plain, (r1_tarski('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_5756, c_5758])).
% 6.00/2.24  tff(c_5782, plain, (![B_681, A_682]: (B_681=A_682 | ~r1_tarski(B_681, A_682) | ~r1_tarski(A_682, B_681))), inference(cnfTransformation, [status(thm)], [f_31])).
% 6.00/2.24  tff(c_5784, plain, ('#skF_1'='#skF_4' | ~r1_tarski('#skF_1', '#skF_4')), inference(resolution, [status(thm)], [c_5762, c_5782])).
% 6.00/2.24  tff(c_5793, plain, ('#skF_1'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5722, c_5784])).
% 6.00/2.24  tff(c_5810, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5793, c_5718])).
% 6.00/2.24  tff(c_5816, plain, (~m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitLeft, [status(thm)], [c_54])).
% 6.00/2.24  tff(c_5829, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5810, c_5810, c_5816])).
% 6.00/2.24  tff(c_5832, plain, (~r1_tarski('#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_18, c_5829])).
% 6.00/2.24  tff(c_5836, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_5832])).
% 6.00/2.24  tff(c_5838, plain, (m1_subset_1(k1_xboole_0, k1_zfmisc_1(k1_xboole_0))), inference(splitRight, [status(thm)], [c_54])).
% 6.00/2.24  tff(c_5851, plain, (m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_5810, c_5810, c_5838])).
% 6.00/2.24  tff(c_5808, plain, (![A_3]: (r1_tarski('#skF_4', A_3))), inference(demodulation, [status(thm), theory('equality')], [c_5793, c_5722])).
% 6.00/2.24  tff(c_5910, plain, (![A_691, B_692, C_693]: (k1_relset_1(A_691, B_692, C_693)=k1_relat_1(C_693) | ~m1_subset_1(C_693, k1_zfmisc_1(k2_zfmisc_1(A_691, B_692))))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.00/2.24  tff(c_5984, plain, (![A_704, B_705, A_706]: (k1_relset_1(A_704, B_705, A_706)=k1_relat_1(A_706) | ~r1_tarski(A_706, k2_zfmisc_1(A_704, B_705)))), inference(resolution, [status(thm)], [c_18, c_5910])).
% 6.00/2.24  tff(c_5999, plain, (![A_704, B_705]: (k1_relset_1(A_704, B_705, '#skF_4')=k1_relat_1('#skF_4'))), inference(resolution, [status(thm)], [c_5808, c_5984])).
% 6.00/2.24  tff(c_5740, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5727, c_46])).
% 6.00/2.24  tff(c_5806, plain, (v1_funct_2('#skF_4', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_5793, c_5793, c_5740])).
% 6.00/2.24  tff(c_6074, plain, (![B_719, C_720]: (k1_relset_1('#skF_4', B_719, C_720)='#skF_4' | ~v1_funct_2(C_720, '#skF_4', B_719) | ~m1_subset_1(C_720, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5810, c_5810, c_5810, c_5810, c_52])).
% 6.00/2.24  tff(c_6076, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_4')='#skF_4' | ~m1_subset_1('#skF_4', k1_zfmisc_1('#skF_4'))), inference(resolution, [status(thm)], [c_5806, c_6074])).
% 6.00/2.24  tff(c_6082, plain, (k1_relat_1('#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5851, c_5999, c_6076])).
% 6.00/2.24  tff(c_6087, plain, (![A_704, B_705]: (k1_relset_1(A_704, B_705, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_6082, c_5999])).
% 6.00/2.24  tff(c_6181, plain, (![C_739, B_740]: (v1_funct_2(C_739, '#skF_4', B_740) | k1_relset_1('#skF_4', B_740, C_739)!='#skF_4' | ~m1_subset_1(C_739, k1_zfmisc_1('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_5810, c_5810, c_5810, c_5810, c_51])).
% 6.00/2.24  tff(c_6183, plain, (![B_740]: (v1_funct_2('#skF_4', '#skF_4', B_740) | k1_relset_1('#skF_4', B_740, '#skF_4')!='#skF_4')), inference(resolution, [status(thm)], [c_5851, c_6181])).
% 6.00/2.24  tff(c_6189, plain, (![B_740]: (v1_funct_2('#skF_4', '#skF_4', B_740))), inference(demodulation, [status(thm), theory('equality')], [c_6087, c_6183])).
% 6.00/2.24  tff(c_5721, plain, (![B_5]: (k2_zfmisc_1('#skF_1', B_5)='#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_5718, c_5718, c_14])).
% 6.00/2.24  tff(c_5764, plain, (~v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5756, c_5721, c_50])).
% 6.00/2.24  tff(c_5802, plain, (~v1_funct_2('#skF_4', '#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_5793, c_5764])).
% 6.00/2.24  tff(c_6194, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6189, c_5802])).
% 6.00/2.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.24  
% 6.00/2.24  Inference rules
% 6.00/2.24  ----------------------
% 6.00/2.24  #Ref     : 0
% 6.00/2.24  #Sup     : 1357
% 6.00/2.24  #Fact    : 0
% 6.00/2.24  #Define  : 0
% 6.00/2.24  #Split   : 35
% 6.00/2.24  #Chain   : 0
% 6.00/2.24  #Close   : 0
% 6.00/2.24  
% 6.00/2.24  Ordering : KBO
% 6.00/2.24  
% 6.00/2.24  Simplification rules
% 6.00/2.24  ----------------------
% 6.00/2.24  #Subsume      : 155
% 6.00/2.24  #Demod        : 1137
% 6.00/2.24  #Tautology    : 731
% 6.00/2.24  #SimpNegUnit  : 37
% 6.00/2.24  #BackRed      : 281
% 6.00/2.24  
% 6.00/2.24  #Partial instantiations: 0
% 6.00/2.24  #Strategies tried      : 1
% 6.00/2.24  
% 6.00/2.24  Timing (in seconds)
% 6.00/2.24  ----------------------
% 6.00/2.24  Preprocessing        : 0.32
% 6.00/2.24  Parsing              : 0.17
% 6.00/2.24  CNF conversion       : 0.02
% 6.00/2.24  Main loop            : 1.06
% 6.00/2.24  Inferencing          : 0.37
% 6.00/2.24  Reduction            : 0.34
% 6.00/2.24  Demodulation         : 0.23
% 6.00/2.24  BG Simplification    : 0.04
% 6.00/2.24  Subsumption          : 0.22
% 6.00/2.24  Abstraction          : 0.05
% 6.00/2.24  MUC search           : 0.00
% 6.00/2.24  Cooper               : 0.00
% 6.00/2.24  Total                : 1.51
% 6.00/2.24  Index Insertion      : 0.00
% 6.00/2.24  Index Deletion       : 0.00
% 6.00/2.24  Index Matching       : 0.00
% 6.00/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------
