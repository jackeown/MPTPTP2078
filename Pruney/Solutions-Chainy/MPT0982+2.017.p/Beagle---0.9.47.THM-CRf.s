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
% DateTime   : Thu Dec  3 10:11:57 EST 2020

% Result     : Theorem 4.63s
% Output     : CNFRefutation 4.97s
% Verified   : 
% Statistics : Number of formulae       :  125 ( 416 expanded)
%              Number of leaves         :   43 ( 165 expanded)
%              Depth                    :   18
%              Number of atoms          :  237 (1374 expanded)
%              Number of equality atoms :   70 ( 378 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k10_relat_1,type,(
    k10_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_161,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( ( k2_relset_1(A,C,k1_partfun1(A,B,B,C,D,E)) = C
                & v2_funct_1(E) )
             => ( C = k1_xboole_0
                | k2_relset_1(A,B,D) = B ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_75,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_89,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_129,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_119,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => r1_tarski(k2_relat_1(k5_relat_1(A,B)),k2_relat_1(B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_107,axiom,(
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

tff(f_71,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v1_funct_1(B) )
     => ( ( r1_tarski(A,k1_relat_1(B))
          & v2_funct_1(B) )
       => k10_relat_1(B,k9_relat_1(B,A)) = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t164_funct_1)).

tff(f_48,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => k2_relat_1(k5_relat_1(A,B)) = k9_relat_1(B,k2_relat_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t160_relat_1)).

tff(c_70,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_102,plain,(
    ! [C_55,B_56,A_57] :
      ( v5_relat_1(C_55,B_56)
      | ~ m1_subset_1(C_55,k1_zfmisc_1(k2_zfmisc_1(A_57,B_56))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_109,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_70,c_102])).

tff(c_84,plain,(
    ! [C_49,A_50,B_51] :
      ( v1_relat_1(C_49)
      | ~ m1_subset_1(C_49,k1_zfmisc_1(k2_zfmisc_1(A_50,B_51))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_84])).

tff(c_93,plain,(
    ! [C_52,A_53,B_54] :
      ( v4_relat_1(C_52,A_53)
      | ~ m1_subset_1(C_52,k1_zfmisc_1(k2_zfmisc_1(A_53,B_54))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_100,plain,(
    v4_relat_1('#skF_4','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_93])).

tff(c_115,plain,(
    ! [B_58,A_59] :
      ( k7_relat_1(B_58,A_59) = B_58
      | ~ v4_relat_1(B_58,A_59)
      | ~ v1_relat_1(B_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_121,plain,
    ( k7_relat_1('#skF_4','#skF_1') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_100,c_115])).

tff(c_127,plain,(
    k7_relat_1('#skF_4','#skF_1') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_121])).

tff(c_136,plain,(
    ! [B_60,A_61] :
      ( k2_relat_1(k7_relat_1(B_60,A_61)) = k9_relat_1(B_60,A_61)
      | ~ v1_relat_1(B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_145,plain,
    ( k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_136])).

tff(c_152,plain,(
    k9_relat_1('#skF_4','#skF_1') = k2_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_145])).

tff(c_12,plain,(
    ! [B_6,A_5] :
      ( k2_relat_1(k7_relat_1(B_6,A_5)) = k9_relat_1(B_6,A_5)
      | ~ v1_relat_1(B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_176,plain,(
    ! [B_65,A_66] :
      ( r1_tarski(k2_relat_1(B_65),A_66)
      | ~ v5_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_880,plain,(
    ! [B_134,A_135,A_136] :
      ( r1_tarski(k9_relat_1(B_134,A_135),A_136)
      | ~ v5_relat_1(k7_relat_1(B_134,A_135),A_136)
      | ~ v1_relat_1(k7_relat_1(B_134,A_135))
      | ~ v1_relat_1(B_134) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_176])).

tff(c_893,plain,(
    ! [A_136] :
      ( r1_tarski(k9_relat_1('#skF_4','#skF_1'),A_136)
      | ~ v5_relat_1('#skF_4',A_136)
      | ~ v1_relat_1(k7_relat_1('#skF_4','#skF_1'))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_880])).

tff(c_901,plain,(
    ! [A_136] :
      ( r1_tarski(k2_relat_1('#skF_4'),A_136)
      | ~ v5_relat_1('#skF_4',A_136) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_91,c_127,c_152,c_893])).

tff(c_202,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_209,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_202])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_211,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_209,c_56])).

tff(c_64,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_92,plain,(
    v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_84])).

tff(c_110,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_102])).

tff(c_74,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_68,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_732,plain,(
    ! [A_116,D_121,C_120,F_119,E_118,B_117] :
      ( k1_partfun1(A_116,B_117,C_120,D_121,E_118,F_119) = k5_relat_1(E_118,F_119)
      | ~ m1_subset_1(F_119,k1_zfmisc_1(k2_zfmisc_1(C_120,D_121)))
      | ~ v1_funct_1(F_119)
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(cnfTransformation,[status(thm)],[f_129])).

tff(c_742,plain,(
    ! [A_116,B_117,E_118] :
      ( k1_partfun1(A_116,B_117,'#skF_2','#skF_3',E_118,'#skF_5') = k5_relat_1(E_118,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_118,k1_zfmisc_1(k2_zfmisc_1(A_116,B_117)))
      | ~ v1_funct_1(E_118) ) ),
    inference(resolution,[status(thm)],[c_64,c_732])).

tff(c_1244,plain,(
    ! [A_149,B_150,E_151] :
      ( k1_partfun1(A_149,B_150,'#skF_2','#skF_3',E_151,'#skF_5') = k5_relat_1(E_151,'#skF_5')
      | ~ m1_subset_1(E_151,k1_zfmisc_1(k2_zfmisc_1(A_149,B_150)))
      | ~ v1_funct_1(E_151) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_742])).

tff(c_1265,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_70,c_1244])).

tff(c_1285,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1265])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_1662,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1285,c_62])).

tff(c_44,plain,(
    ! [B_33,C_34,E_36,F_37,A_32,D_35] :
      ( m1_subset_1(k1_partfun1(A_32,B_33,C_34,D_35,E_36,F_37),k1_zfmisc_1(k2_zfmisc_1(A_32,D_35)))
      | ~ m1_subset_1(F_37,k1_zfmisc_1(k2_zfmisc_1(C_34,D_35)))
      | ~ v1_funct_1(F_37)
      | ~ m1_subset_1(E_36,k1_zfmisc_1(k2_zfmisc_1(A_32,B_33)))
      | ~ v1_funct_1(E_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_119])).

tff(c_1666,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ v1_funct_1('#skF_5')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1285,c_44])).

tff(c_1670,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_1666])).

tff(c_30,plain,(
    ! [A_26,B_27,C_28] :
      ( k2_relset_1(A_26,B_27,C_28) = k2_relat_1(C_28)
      | ~ m1_subset_1(C_28,k1_zfmisc_1(k2_zfmisc_1(A_26,B_27))) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_1704,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_1670,c_30])).

tff(c_1740,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1662,c_1704])).

tff(c_101,plain,(
    v4_relat_1('#skF_5','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_93])).

tff(c_118,plain,
    ( k7_relat_1('#skF_5','#skF_2') = '#skF_5'
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_101,c_115])).

tff(c_124,plain,(
    k7_relat_1('#skF_5','#skF_2') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_118])).

tff(c_148,plain,
    ( k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_136])).

tff(c_154,plain,(
    k9_relat_1('#skF_5','#skF_2') = k2_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_148])).

tff(c_191,plain,(
    ! [A_68,B_69] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_68,B_69)),k2_relat_1(B_69))
      | ~ v1_relat_1(B_69)
      | ~ v1_relat_1(A_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1309,plain,(
    ! [A_152,B_153,A_154] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_152,k7_relat_1(B_153,A_154))),k9_relat_1(B_153,A_154))
      | ~ v1_relat_1(k7_relat_1(B_153,A_154))
      | ~ v1_relat_1(A_152)
      | ~ v1_relat_1(B_153) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_191])).

tff(c_1347,plain,(
    ! [A_152] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_152,'#skF_5')),k9_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1(k7_relat_1('#skF_5','#skF_2'))
      | ~ v1_relat_1(A_152)
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_1309])).

tff(c_1365,plain,(
    ! [A_152] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_152,'#skF_5')),k2_relat_1('#skF_5'))
      | ~ v1_relat_1(A_152) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_92,c_124,c_154,c_1347])).

tff(c_1750,plain,
    ( r1_tarski('#skF_3',k2_relat_1('#skF_5'))
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1740,c_1365])).

tff(c_1807,plain,(
    r1_tarski('#skF_3',k2_relat_1('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1750])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_186,plain,(
    ! [B_65,A_66] :
      ( k2_relat_1(B_65) = A_66
      | ~ r1_tarski(A_66,k2_relat_1(B_65))
      | ~ v5_relat_1(B_65,A_66)
      | ~ v1_relat_1(B_65) ) ),
    inference(resolution,[status(thm)],[c_176,c_2])).

tff(c_1845,plain,
    ( k2_relat_1('#skF_5') = '#skF_3'
    | ~ v5_relat_1('#skF_5','#skF_3')
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_1807,c_186])).

tff(c_1850,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_110,c_1845])).

tff(c_60,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_58,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_66,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_161])).

tff(c_258,plain,(
    ! [A_77,B_78,C_79] :
      ( k1_relset_1(A_77,B_78,C_79) = k1_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_270,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_258])).

tff(c_403,plain,(
    ! [B_100,A_101,C_102] :
      ( k1_xboole_0 = B_100
      | k1_relset_1(A_101,B_100,C_102) = A_101
      | ~ v1_funct_2(C_102,A_101,B_100)
      | ~ m1_subset_1(C_102,k1_zfmisc_1(k2_zfmisc_1(A_101,B_100))) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_412,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_403])).

tff(c_419,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_270,c_412])).

tff(c_420,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_419])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_382,plain,(
    ! [B_97,A_98] :
      ( k10_relat_1(B_97,k9_relat_1(B_97,A_98)) = A_98
      | ~ v2_funct_1(B_97)
      | ~ r1_tarski(A_98,k1_relat_1(B_97))
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_390,plain,(
    ! [B_97] :
      ( k10_relat_1(B_97,k9_relat_1(B_97,k1_relat_1(B_97))) = k1_relat_1(B_97)
      | ~ v2_funct_1(B_97)
      | ~ v1_funct_1(B_97)
      | ~ v1_relat_1(B_97) ) ),
    inference(resolution,[status(thm)],[c_6,c_382])).

tff(c_425,plain,
    ( k10_relat_1('#skF_5',k9_relat_1('#skF_5','#skF_2')) = k1_relat_1('#skF_5')
    | ~ v2_funct_1('#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_390])).

tff(c_452,plain,(
    k10_relat_1('#skF_5',k2_relat_1('#skF_5')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_68,c_60,c_420,c_154,c_425])).

tff(c_1861,plain,(
    k10_relat_1('#skF_5','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1850,c_452])).

tff(c_14,plain,(
    ! [B_9,A_7] :
      ( k9_relat_1(B_9,k2_relat_1(A_7)) = k2_relat_1(k5_relat_1(A_7,B_9))
      | ~ v1_relat_1(B_9)
      | ~ v1_relat_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_20,plain,(
    ! [B_16,A_15] :
      ( k10_relat_1(B_16,k9_relat_1(B_16,A_15)) = A_15
      | ~ v2_funct_1(B_16)
      | ~ r1_tarski(A_15,k1_relat_1(B_16))
      | ~ v1_funct_1(B_16)
      | ~ v1_relat_1(B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_427,plain,(
    ! [A_15] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_15)) = A_15
      | ~ v2_funct_1('#skF_5')
      | ~ r1_tarski(A_15,'#skF_2')
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_420,c_20])).

tff(c_694,plain,(
    ! [A_115] :
      ( k10_relat_1('#skF_5',k9_relat_1('#skF_5',A_115)) = A_115
      | ~ r1_tarski(A_115,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_68,c_60,c_427])).

tff(c_716,plain,(
    ! [A_7] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_7,'#skF_5'))) = k2_relat_1(A_7)
      | ~ r1_tarski(k2_relat_1(A_7),'#skF_2')
      | ~ v1_relat_1('#skF_5')
      | ~ v1_relat_1(A_7) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_694])).

tff(c_729,plain,(
    ! [A_7] :
      ( k10_relat_1('#skF_5',k2_relat_1(k5_relat_1(A_7,'#skF_5'))) = k2_relat_1(A_7)
      | ~ r1_tarski(k2_relat_1(A_7),'#skF_2')
      | ~ v1_relat_1(A_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_92,c_716])).

tff(c_1759,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1740,c_729])).

tff(c_1813,plain,
    ( k10_relat_1('#skF_5','#skF_3') = k2_relat_1('#skF_4')
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_1759])).

tff(c_2553,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1861,c_1813])).

tff(c_2554,plain,(
    ~ r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_211,c_2553])).

tff(c_2557,plain,(
    ~ v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_901,c_2554])).

tff(c_2564,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_2557])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:32:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.63/1.88  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.89  
% 4.63/1.89  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.63/1.89  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k9_relat_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > k10_relat_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.63/1.89  
% 4.63/1.89  %Foreground sorts:
% 4.63/1.89  
% 4.63/1.89  
% 4.63/1.89  %Background operators:
% 4.63/1.89  
% 4.63/1.89  
% 4.63/1.89  %Foreground operators:
% 4.63/1.89  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.63/1.89  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.63/1.89  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.63/1.89  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 4.63/1.89  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.63/1.89  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.63/1.89  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.63/1.89  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.63/1.89  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.63/1.89  tff('#skF_5', type, '#skF_5': $i).
% 4.63/1.89  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.63/1.89  tff('#skF_2', type, '#skF_2': $i).
% 4.63/1.89  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 4.63/1.89  tff('#skF_3', type, '#skF_3': $i).
% 4.63/1.89  tff('#skF_1', type, '#skF_1': $i).
% 4.63/1.89  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.63/1.89  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 4.63/1.89  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.63/1.89  tff(k10_relat_1, type, k10_relat_1: ($i * $i) > $i).
% 4.63/1.89  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.63/1.89  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.63/1.89  tff('#skF_4', type, '#skF_4': $i).
% 4.63/1.89  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.63/1.89  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 4.63/1.89  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.63/1.89  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.63/1.89  
% 4.97/1.91  tff(f_161, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_funct_2)).
% 4.97/1.91  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 4.97/1.91  tff(f_75, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 4.97/1.91  tff(f_54, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 4.97/1.91  tff(f_41, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 4.97/1.91  tff(f_37, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d19_relat_1)).
% 4.97/1.91  tff(f_89, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.97/1.91  tff(f_129, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.97/1.91  tff(f_119, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 4.97/1.91  tff(f_61, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 4.97/1.91  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.97/1.91  tff(f_85, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.97/1.91  tff(f_107, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.97/1.91  tff(f_71, axiom, (![A, B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((r1_tarski(A, k1_relat_1(B)) & v2_funct_1(B)) => (k10_relat_1(B, k9_relat_1(B, A)) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t164_funct_1)).
% 4.97/1.91  tff(f_48, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (k2_relat_1(k5_relat_1(A, B)) = k9_relat_1(B, k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t160_relat_1)).
% 4.97/1.91  tff(c_70, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.91  tff(c_102, plain, (![C_55, B_56, A_57]: (v5_relat_1(C_55, B_56) | ~m1_subset_1(C_55, k1_zfmisc_1(k2_zfmisc_1(A_57, B_56))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.97/1.91  tff(c_109, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_70, c_102])).
% 4.97/1.91  tff(c_84, plain, (![C_49, A_50, B_51]: (v1_relat_1(C_49) | ~m1_subset_1(C_49, k1_zfmisc_1(k2_zfmisc_1(A_50, B_51))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.97/1.91  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_84])).
% 4.97/1.91  tff(c_93, plain, (![C_52, A_53, B_54]: (v4_relat_1(C_52, A_53) | ~m1_subset_1(C_52, k1_zfmisc_1(k2_zfmisc_1(A_53, B_54))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 4.97/1.91  tff(c_100, plain, (v4_relat_1('#skF_4', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_93])).
% 4.97/1.91  tff(c_115, plain, (![B_58, A_59]: (k7_relat_1(B_58, A_59)=B_58 | ~v4_relat_1(B_58, A_59) | ~v1_relat_1(B_58))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.97/1.91  tff(c_121, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_100, c_115])).
% 4.97/1.91  tff(c_127, plain, (k7_relat_1('#skF_4', '#skF_1')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_121])).
% 4.97/1.91  tff(c_136, plain, (![B_60, A_61]: (k2_relat_1(k7_relat_1(B_60, A_61))=k9_relat_1(B_60, A_61) | ~v1_relat_1(B_60))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.97/1.91  tff(c_145, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_127, c_136])).
% 4.97/1.91  tff(c_152, plain, (k9_relat_1('#skF_4', '#skF_1')=k2_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_145])).
% 4.97/1.91  tff(c_12, plain, (![B_6, A_5]: (k2_relat_1(k7_relat_1(B_6, A_5))=k9_relat_1(B_6, A_5) | ~v1_relat_1(B_6))), inference(cnfTransformation, [status(thm)], [f_41])).
% 4.97/1.91  tff(c_176, plain, (![B_65, A_66]: (r1_tarski(k2_relat_1(B_65), A_66) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.97/1.91  tff(c_880, plain, (![B_134, A_135, A_136]: (r1_tarski(k9_relat_1(B_134, A_135), A_136) | ~v5_relat_1(k7_relat_1(B_134, A_135), A_136) | ~v1_relat_1(k7_relat_1(B_134, A_135)) | ~v1_relat_1(B_134))), inference(superposition, [status(thm), theory('equality')], [c_12, c_176])).
% 4.97/1.91  tff(c_893, plain, (![A_136]: (r1_tarski(k9_relat_1('#skF_4', '#skF_1'), A_136) | ~v5_relat_1('#skF_4', A_136) | ~v1_relat_1(k7_relat_1('#skF_4', '#skF_1')) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_880])).
% 4.97/1.91  tff(c_901, plain, (![A_136]: (r1_tarski(k2_relat_1('#skF_4'), A_136) | ~v5_relat_1('#skF_4', A_136))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_91, c_127, c_152, c_893])).
% 4.97/1.91  tff(c_202, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.97/1.91  tff(c_209, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_202])).
% 4.97/1.91  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.91  tff(c_211, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_209, c_56])).
% 4.97/1.91  tff(c_64, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.91  tff(c_92, plain, (v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_84])).
% 4.97/1.91  tff(c_110, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_102])).
% 4.97/1.91  tff(c_74, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.91  tff(c_68, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.91  tff(c_732, plain, (![A_116, D_121, C_120, F_119, E_118, B_117]: (k1_partfun1(A_116, B_117, C_120, D_121, E_118, F_119)=k5_relat_1(E_118, F_119) | ~m1_subset_1(F_119, k1_zfmisc_1(k2_zfmisc_1(C_120, D_121))) | ~v1_funct_1(F_119) | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(cnfTransformation, [status(thm)], [f_129])).
% 4.97/1.91  tff(c_742, plain, (![A_116, B_117, E_118]: (k1_partfun1(A_116, B_117, '#skF_2', '#skF_3', E_118, '#skF_5')=k5_relat_1(E_118, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_118, k1_zfmisc_1(k2_zfmisc_1(A_116, B_117))) | ~v1_funct_1(E_118))), inference(resolution, [status(thm)], [c_64, c_732])).
% 4.97/1.92  tff(c_1244, plain, (![A_149, B_150, E_151]: (k1_partfun1(A_149, B_150, '#skF_2', '#skF_3', E_151, '#skF_5')=k5_relat_1(E_151, '#skF_5') | ~m1_subset_1(E_151, k1_zfmisc_1(k2_zfmisc_1(A_149, B_150))) | ~v1_funct_1(E_151))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_742])).
% 4.97/1.92  tff(c_1265, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_70, c_1244])).
% 4.97/1.92  tff(c_1285, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1265])).
% 4.97/1.92  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.92  tff(c_1662, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1285, c_62])).
% 4.97/1.92  tff(c_44, plain, (![B_33, C_34, E_36, F_37, A_32, D_35]: (m1_subset_1(k1_partfun1(A_32, B_33, C_34, D_35, E_36, F_37), k1_zfmisc_1(k2_zfmisc_1(A_32, D_35))) | ~m1_subset_1(F_37, k1_zfmisc_1(k2_zfmisc_1(C_34, D_35))) | ~v1_funct_1(F_37) | ~m1_subset_1(E_36, k1_zfmisc_1(k2_zfmisc_1(A_32, B_33))) | ~v1_funct_1(E_36))), inference(cnfTransformation, [status(thm)], [f_119])).
% 4.97/1.92  tff(c_1666, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~v1_funct_1('#skF_5') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1285, c_44])).
% 4.97/1.92  tff(c_1670, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_1666])).
% 4.97/1.92  tff(c_30, plain, (![A_26, B_27, C_28]: (k2_relset_1(A_26, B_27, C_28)=k2_relat_1(C_28) | ~m1_subset_1(C_28, k1_zfmisc_1(k2_zfmisc_1(A_26, B_27))))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.97/1.92  tff(c_1704, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_1670, c_30])).
% 4.97/1.92  tff(c_1740, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1662, c_1704])).
% 4.97/1.92  tff(c_101, plain, (v4_relat_1('#skF_5', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_93])).
% 4.97/1.92  tff(c_118, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5' | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_101, c_115])).
% 4.97/1.92  tff(c_124, plain, (k7_relat_1('#skF_5', '#skF_2')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_118])).
% 4.97/1.92  tff(c_148, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_124, c_136])).
% 4.97/1.92  tff(c_154, plain, (k9_relat_1('#skF_5', '#skF_2')=k2_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_92, c_148])).
% 4.97/1.92  tff(c_191, plain, (![A_68, B_69]: (r1_tarski(k2_relat_1(k5_relat_1(A_68, B_69)), k2_relat_1(B_69)) | ~v1_relat_1(B_69) | ~v1_relat_1(A_68))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.97/1.92  tff(c_1309, plain, (![A_152, B_153, A_154]: (r1_tarski(k2_relat_1(k5_relat_1(A_152, k7_relat_1(B_153, A_154))), k9_relat_1(B_153, A_154)) | ~v1_relat_1(k7_relat_1(B_153, A_154)) | ~v1_relat_1(A_152) | ~v1_relat_1(B_153))), inference(superposition, [status(thm), theory('equality')], [c_12, c_191])).
% 4.97/1.92  tff(c_1347, plain, (![A_152]: (r1_tarski(k2_relat_1(k5_relat_1(A_152, '#skF_5')), k9_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(k7_relat_1('#skF_5', '#skF_2')) | ~v1_relat_1(A_152) | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_124, c_1309])).
% 4.97/1.92  tff(c_1365, plain, (![A_152]: (r1_tarski(k2_relat_1(k5_relat_1(A_152, '#skF_5')), k2_relat_1('#skF_5')) | ~v1_relat_1(A_152))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_92, c_124, c_154, c_1347])).
% 4.97/1.92  tff(c_1750, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5')) | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1740, c_1365])).
% 4.97/1.92  tff(c_1807, plain, (r1_tarski('#skF_3', k2_relat_1('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1750])).
% 4.97/1.92  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.97/1.92  tff(c_186, plain, (![B_65, A_66]: (k2_relat_1(B_65)=A_66 | ~r1_tarski(A_66, k2_relat_1(B_65)) | ~v5_relat_1(B_65, A_66) | ~v1_relat_1(B_65))), inference(resolution, [status(thm)], [c_176, c_2])).
% 4.97/1.92  tff(c_1845, plain, (k2_relat_1('#skF_5')='#skF_3' | ~v5_relat_1('#skF_5', '#skF_3') | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_1807, c_186])).
% 4.97/1.92  tff(c_1850, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_110, c_1845])).
% 4.97/1.92  tff(c_60, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.92  tff(c_58, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.92  tff(c_66, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_161])).
% 4.97/1.92  tff(c_258, plain, (![A_77, B_78, C_79]: (k1_relset_1(A_77, B_78, C_79)=k1_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.97/1.92  tff(c_270, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_64, c_258])).
% 4.97/1.92  tff(c_403, plain, (![B_100, A_101, C_102]: (k1_xboole_0=B_100 | k1_relset_1(A_101, B_100, C_102)=A_101 | ~v1_funct_2(C_102, A_101, B_100) | ~m1_subset_1(C_102, k1_zfmisc_1(k2_zfmisc_1(A_101, B_100))))), inference(cnfTransformation, [status(thm)], [f_107])).
% 4.97/1.92  tff(c_412, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_64, c_403])).
% 4.97/1.92  tff(c_419, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_66, c_270, c_412])).
% 4.97/1.92  tff(c_420, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_58, c_419])).
% 4.97/1.92  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.97/1.92  tff(c_382, plain, (![B_97, A_98]: (k10_relat_1(B_97, k9_relat_1(B_97, A_98))=A_98 | ~v2_funct_1(B_97) | ~r1_tarski(A_98, k1_relat_1(B_97)) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.97/1.92  tff(c_390, plain, (![B_97]: (k10_relat_1(B_97, k9_relat_1(B_97, k1_relat_1(B_97)))=k1_relat_1(B_97) | ~v2_funct_1(B_97) | ~v1_funct_1(B_97) | ~v1_relat_1(B_97))), inference(resolution, [status(thm)], [c_6, c_382])).
% 4.97/1.92  tff(c_425, plain, (k10_relat_1('#skF_5', k9_relat_1('#skF_5', '#skF_2'))=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_420, c_390])).
% 4.97/1.92  tff(c_452, plain, (k10_relat_1('#skF_5', k2_relat_1('#skF_5'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_92, c_68, c_60, c_420, c_154, c_425])).
% 4.97/1.92  tff(c_1861, plain, (k10_relat_1('#skF_5', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1850, c_452])).
% 4.97/1.92  tff(c_14, plain, (![B_9, A_7]: (k9_relat_1(B_9, k2_relat_1(A_7))=k2_relat_1(k5_relat_1(A_7, B_9)) | ~v1_relat_1(B_9) | ~v1_relat_1(A_7))), inference(cnfTransformation, [status(thm)], [f_48])).
% 4.97/1.92  tff(c_20, plain, (![B_16, A_15]: (k10_relat_1(B_16, k9_relat_1(B_16, A_15))=A_15 | ~v2_funct_1(B_16) | ~r1_tarski(A_15, k1_relat_1(B_16)) | ~v1_funct_1(B_16) | ~v1_relat_1(B_16))), inference(cnfTransformation, [status(thm)], [f_71])).
% 4.97/1.92  tff(c_427, plain, (![A_15]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_15))=A_15 | ~v2_funct_1('#skF_5') | ~r1_tarski(A_15, '#skF_2') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_420, c_20])).
% 4.97/1.92  tff(c_694, plain, (![A_115]: (k10_relat_1('#skF_5', k9_relat_1('#skF_5', A_115))=A_115 | ~r1_tarski(A_115, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_68, c_60, c_427])).
% 4.97/1.92  tff(c_716, plain, (![A_7]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_7, '#skF_5')))=k2_relat_1(A_7) | ~r1_tarski(k2_relat_1(A_7), '#skF_2') | ~v1_relat_1('#skF_5') | ~v1_relat_1(A_7))), inference(superposition, [status(thm), theory('equality')], [c_14, c_694])).
% 4.97/1.92  tff(c_729, plain, (![A_7]: (k10_relat_1('#skF_5', k2_relat_1(k5_relat_1(A_7, '#skF_5')))=k2_relat_1(A_7) | ~r1_tarski(k2_relat_1(A_7), '#skF_2') | ~v1_relat_1(A_7))), inference(demodulation, [status(thm), theory('equality')], [c_92, c_716])).
% 4.97/1.92  tff(c_1759, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1740, c_729])).
% 4.97/1.92  tff(c_1813, plain, (k10_relat_1('#skF_5', '#skF_3')=k2_relat_1('#skF_4') | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_91, c_1759])).
% 4.97/1.92  tff(c_2553, plain, (k2_relat_1('#skF_4')='#skF_2' | ~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_1861, c_1813])).
% 4.97/1.92  tff(c_2554, plain, (~r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(negUnitSimplification, [status(thm)], [c_211, c_2553])).
% 4.97/1.92  tff(c_2557, plain, (~v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_901, c_2554])).
% 4.97/1.92  tff(c_2564, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_109, c_2557])).
% 4.97/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.97/1.92  
% 4.97/1.92  Inference rules
% 4.97/1.92  ----------------------
% 4.97/1.92  #Ref     : 0
% 4.97/1.92  #Sup     : 550
% 4.97/1.92  #Fact    : 0
% 4.97/1.92  #Define  : 0
% 4.97/1.92  #Split   : 5
% 4.97/1.92  #Chain   : 0
% 4.97/1.92  #Close   : 0
% 4.97/1.92  
% 4.97/1.92  Ordering : KBO
% 4.97/1.92  
% 4.97/1.92  Simplification rules
% 4.97/1.92  ----------------------
% 4.97/1.92  #Subsume      : 16
% 4.97/1.92  #Demod        : 844
% 4.97/1.92  #Tautology    : 198
% 4.97/1.92  #SimpNegUnit  : 8
% 4.97/1.92  #BackRed      : 23
% 4.97/1.92  
% 4.97/1.92  #Partial instantiations: 0
% 4.97/1.92  #Strategies tried      : 1
% 4.97/1.92  
% 4.97/1.92  Timing (in seconds)
% 4.97/1.92  ----------------------
% 4.97/1.92  Preprocessing        : 0.38
% 4.97/1.92  Parsing              : 0.21
% 4.97/1.92  CNF conversion       : 0.02
% 4.97/1.92  Main loop            : 0.72
% 4.97/1.92  Inferencing          : 0.25
% 4.97/1.92  Reduction            : 0.26
% 4.97/1.92  Demodulation         : 0.20
% 4.97/1.92  BG Simplification    : 0.03
% 4.97/1.92  Subsumption          : 0.11
% 4.97/1.92  Abstraction          : 0.03
% 4.97/1.92  MUC search           : 0.00
% 4.97/1.92  Cooper               : 0.00
% 4.97/1.92  Total                : 1.14
% 4.97/1.92  Index Insertion      : 0.00
% 4.97/1.92  Index Deletion       : 0.00
% 4.97/1.92  Index Matching       : 0.00
% 4.97/1.92  BG Taut test         : 0.00
%------------------------------------------------------------------------------
