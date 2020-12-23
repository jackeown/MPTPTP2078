%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:55 EST 2020

% Result     : Theorem 3.78s
% Output     : CNFRefutation 4.12s
% Verified   : 
% Statistics : Number of formulae       :  149 (1763 expanded)
%              Number of leaves         :   33 ( 528 expanded)
%              Depth                    :   17
%              Number of atoms          :  290 (6802 expanded)
%              Number of equality atoms :   68 (2530 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( v1_funct_1(D)
          & v1_funct_2(D,A,B)
          & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [E] :
            ( ( v1_funct_1(E)
              & v1_funct_2(E,B,C)
              & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
           => ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
             => ( ( C = k1_xboole_0
                  & B != k1_xboole_0 )
                | v2_funct_1(D) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_funct_2)).

tff(f_38,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_83,axiom,(
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

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(k5_relat_1(B,A))
              & r1_tarski(k2_relat_1(B),k1_relat_1(A)) )
           => v2_funct_1(B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_funct_1)).

tff(f_93,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_32,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_8,plain,(
    ! [A_6,B_7] : v1_relat_1(k2_zfmisc_1(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_65,plain,(
    ! [B_36,A_37] :
      ( v1_relat_1(B_36)
      | ~ m1_subset_1(B_36,k1_zfmisc_1(A_37))
      | ~ v1_relat_1(A_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_71,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_44,c_65])).

tff(c_78,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_71])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_128,plain,(
    ! [A_46,B_47,C_48] :
      ( k2_relset_1(A_46,B_47,C_48) = k2_relat_1(C_48)
      | ~ m1_subset_1(C_48,k1_zfmisc_1(k2_zfmisc_1(A_46,B_47))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_140,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_128])).

tff(c_167,plain,(
    ! [A_54,B_55,C_56] :
      ( m1_subset_1(k2_relset_1(A_54,B_55,C_56),k1_zfmisc_1(B_55))
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_54,B_55))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_187,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_140,c_167])).

tff(c_195,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_187])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | ~ m1_subset_1(A_1,k1_zfmisc_1(B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_215,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_195,c_2])).

tff(c_38,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_74,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_38,c_65])).

tff(c_81,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_74])).

tff(c_42,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_34,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_49,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_95,plain,(
    ! [A_40,B_41,C_42] :
      ( k1_relset_1(A_40,B_41,C_42) = k1_relat_1(C_42)
      | ~ m1_subset_1(C_42,k1_zfmisc_1(k2_zfmisc_1(A_40,B_41))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_108,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_38,c_95])).

tff(c_391,plain,(
    ! [B_87,A_88,C_89] :
      ( k1_xboole_0 = B_87
      | k1_relset_1(A_88,B_87,C_89) = A_88
      | ~ v1_funct_2(C_89,A_88,B_87)
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_88,B_87))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_405,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_38,c_391])).

tff(c_413,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_108,c_405])).

tff(c_414,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_413])).

tff(c_421,plain,(
    ! [B_90,A_91] :
      ( v2_funct_1(B_90)
      | ~ r1_tarski(k2_relat_1(B_90),k1_relat_1(A_91))
      | ~ v2_funct_1(k5_relat_1(B_90,A_91))
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_424,plain,(
    ! [B_90] :
      ( v2_funct_1(B_90)
      | ~ r1_tarski(k2_relat_1(B_90),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_90,'#skF_5'))
      | ~ v1_funct_1(B_90)
      | ~ v1_relat_1(B_90)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_414,c_421])).

tff(c_445,plain,(
    ! [B_92] :
      ( v2_funct_1(B_92)
      | ~ r1_tarski(k2_relat_1(B_92),'#skF_2')
      | ~ v2_funct_1(k5_relat_1(B_92,'#skF_5'))
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_81,c_42,c_424])).

tff(c_448,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_215,c_445])).

tff(c_451,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_48,c_448])).

tff(c_452,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_451])).

tff(c_519,plain,(
    ! [D_109,A_110,C_105,B_108,F_106,E_107] :
      ( k1_partfun1(A_110,B_108,C_105,D_109,E_107,F_106) = k5_relat_1(E_107,F_106)
      | ~ m1_subset_1(F_106,k1_zfmisc_1(k2_zfmisc_1(C_105,D_109)))
      | ~ v1_funct_1(F_106)
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_110,B_108)))
      | ~ v1_funct_1(E_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_529,plain,(
    ! [A_110,B_108,E_107] :
      ( k1_partfun1(A_110,B_108,'#skF_2','#skF_3',E_107,'#skF_5') = k5_relat_1(E_107,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_107,k1_zfmisc_1(k2_zfmisc_1(A_110,B_108)))
      | ~ v1_funct_1(E_107) ) ),
    inference(resolution,[status(thm)],[c_38,c_519])).

tff(c_569,plain,(
    ! [A_114,B_115,E_116] :
      ( k1_partfun1(A_114,B_115,'#skF_2','#skF_3',E_116,'#skF_5') = k5_relat_1(E_116,'#skF_5')
      | ~ m1_subset_1(E_116,k1_zfmisc_1(k2_zfmisc_1(A_114,B_115)))
      | ~ v1_funct_1(E_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_529])).

tff(c_580,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_569])).

tff(c_588,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_580])).

tff(c_36,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_592,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_588,c_36])).

tff(c_594,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_452,c_592])).

tff(c_596,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_595,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_601,plain,(
    '#skF_2' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_595])).

tff(c_614,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_44])).

tff(c_630,plain,(
    ! [B_123,A_124] :
      ( v1_relat_1(B_123)
      | ~ m1_subset_1(B_123,k1_zfmisc_1(A_124))
      | ~ v1_relat_1(A_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_636,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_614,c_630])).

tff(c_643,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_636])).

tff(c_46,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_610,plain,(
    v1_funct_2('#skF_4','#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_46])).

tff(c_20,plain,(
    ! [C_22,A_20] :
      ( k1_xboole_0 = C_22
      | ~ v1_funct_2(C_22,A_20,k1_xboole_0)
      | k1_xboole_0 = A_20
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,k1_xboole_0))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1352,plain,(
    ! [C_190,A_191] :
      ( C_190 = '#skF_3'
      | ~ v1_funct_2(C_190,A_191,'#skF_3')
      | A_191 = '#skF_3'
      | ~ m1_subset_1(C_190,k1_zfmisc_1(k2_zfmisc_1(A_191,'#skF_3'))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_596,c_596,c_596,c_596,c_20])).

tff(c_1363,plain,
    ( '#skF_3' = '#skF_4'
    | ~ v1_funct_2('#skF_4','#skF_1','#skF_3')
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_614,c_1352])).

tff(c_1371,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_610,c_1363])).

tff(c_1376,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_1371])).

tff(c_693,plain,(
    ! [A_133,B_134,C_135] :
      ( k2_relset_1(A_133,B_134,C_135) = k2_relat_1(C_135)
      | ~ m1_subset_1(C_135,k1_zfmisc_1(k2_zfmisc_1(A_133,B_134))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_705,plain,(
    k2_relset_1('#skF_1','#skF_3','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_614,c_693])).

tff(c_733,plain,(
    ! [A_141,B_142,C_143] :
      ( m1_subset_1(k2_relset_1(A_141,B_142,C_143),k1_zfmisc_1(B_142))
      | ~ m1_subset_1(C_143,k1_zfmisc_1(k2_zfmisc_1(A_141,B_142))) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_753,plain,
    ( m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_705,c_733])).

tff(c_761,plain,(
    m1_subset_1(k2_relat_1('#skF_4'),k1_zfmisc_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_614,c_753])).

tff(c_781,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_761,c_2])).

tff(c_1379,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_781])).

tff(c_613,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_3','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_38])).

tff(c_639,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_3','#skF_3')) ),
    inference(resolution,[status(thm)],[c_613,c_630])).

tff(c_646,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_639])).

tff(c_612,plain,(
    v1_funct_2('#skF_5','#skF_3','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_40])).

tff(c_1394,plain,(
    v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_1376,c_612])).

tff(c_647,plain,(
    ! [A_125,B_126,C_127] :
      ( k1_relset_1(A_125,B_126,C_127) = k1_relat_1(C_127)
      | ~ m1_subset_1(C_127,k1_zfmisc_1(k2_zfmisc_1(A_125,B_126))) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_660,plain,(
    k1_relset_1('#skF_3','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_613,c_647])).

tff(c_1388,plain,(
    k1_relset_1('#skF_1','#skF_1','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_1376,c_660])).

tff(c_1393,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_1376,c_613])).

tff(c_1397,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_596])).

tff(c_26,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1(k1_xboole_0,B_21,C_22) = k1_xboole_0
      | ~ v1_funct_2(C_22,k1_xboole_0,B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1422,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1('#skF_1',B_21,C_22) = '#skF_1'
      | ~ v1_funct_2(C_22,'#skF_1',B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_1',B_21))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1397,c_1397,c_1397,c_1397,c_26])).

tff(c_1549,plain,
    ( k1_relset_1('#skF_1','#skF_1','#skF_5') = '#skF_1'
    | ~ v1_funct_2('#skF_5','#skF_1','#skF_1') ),
    inference(resolution,[status(thm)],[c_1393,c_1422])).

tff(c_1566,plain,(
    k1_relat_1('#skF_5') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1394,c_1388,c_1549])).

tff(c_1771,plain,(
    ! [B_218,A_219] :
      ( v2_funct_1(B_218)
      | ~ r1_tarski(k2_relat_1(B_218),k1_relat_1(A_219))
      | ~ v2_funct_1(k5_relat_1(B_218,A_219))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | ~ v1_funct_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1774,plain,(
    ! [B_218] :
      ( v2_funct_1(B_218)
      | ~ r1_tarski(k2_relat_1(B_218),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_218,'#skF_5'))
      | ~ v1_funct_1(B_218)
      | ~ v1_relat_1(B_218)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1566,c_1771])).

tff(c_1843,plain,(
    ! [B_226] :
      ( v2_funct_1(B_226)
      | ~ r1_tarski(k2_relat_1(B_226),'#skF_1')
      | ~ v2_funct_1(k5_relat_1(B_226,'#skF_5'))
      | ~ v1_funct_1(B_226)
      | ~ v1_relat_1(B_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_42,c_1774])).

tff(c_1849,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1379,c_1843])).

tff(c_1855,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_48,c_1849])).

tff(c_1856,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_1855])).

tff(c_1392,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_614])).

tff(c_1857,plain,(
    ! [D_231,C_227,F_228,A_232,E_229,B_230] :
      ( k1_partfun1(A_232,B_230,C_227,D_231,E_229,F_228) = k5_relat_1(E_229,F_228)
      | ~ m1_subset_1(F_228,k1_zfmisc_1(k2_zfmisc_1(C_227,D_231)))
      | ~ v1_funct_1(F_228)
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1859,plain,(
    ! [A_232,B_230,E_229] :
      ( k1_partfun1(A_232,B_230,'#skF_1','#skF_1',E_229,'#skF_5') = k5_relat_1(E_229,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_229,k1_zfmisc_1(k2_zfmisc_1(A_232,B_230)))
      | ~ v1_funct_1(E_229) ) ),
    inference(resolution,[status(thm)],[c_1393,c_1857])).

tff(c_1932,plain,(
    ! [A_240,B_241,E_242] :
      ( k1_partfun1(A_240,B_241,'#skF_1','#skF_1',E_242,'#skF_5') = k5_relat_1(E_242,'#skF_5')
      | ~ m1_subset_1(E_242,k1_zfmisc_1(k2_zfmisc_1(A_240,B_241)))
      | ~ v1_funct_1(E_242) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_1859])).

tff(c_1938,plain,
    ( k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1392,c_1932])).

tff(c_1952,plain,(
    k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1938])).

tff(c_615,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_3','#skF_3','#skF_3','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_601,c_601,c_36])).

tff(c_1391,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_1','#skF_1','#skF_1','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1376,c_1376,c_1376,c_615])).

tff(c_1968,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1952,c_1391])).

tff(c_1970,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1856,c_1968])).

tff(c_1971,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_1371])).

tff(c_1975,plain,(
    r1_tarski(k2_relat_1('#skF_4'),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_781])).

tff(c_1990,plain,(
    v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_1971,c_612])).

tff(c_1984,plain,(
    k1_relset_1('#skF_4','#skF_4','#skF_5') = k1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_1971,c_660])).

tff(c_1989,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_4','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_1971,c_613])).

tff(c_1993,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_596])).

tff(c_2109,plain,(
    ! [B_21,C_22] :
      ( k1_relset_1('#skF_4',B_21,C_22) = '#skF_4'
      | ~ v1_funct_2(C_22,'#skF_4',B_21)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1('#skF_4',B_21))) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1993,c_1993,c_1993,c_1993,c_26])).

tff(c_2127,plain,
    ( k1_relset_1('#skF_4','#skF_4','#skF_5') = '#skF_4'
    | ~ v1_funct_2('#skF_5','#skF_4','#skF_4') ),
    inference(resolution,[status(thm)],[c_1989,c_2109])).

tff(c_2145,plain,(
    k1_relat_1('#skF_5') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1990,c_1984,c_2127])).

tff(c_2364,plain,(
    ! [B_273,A_274] :
      ( v2_funct_1(B_273)
      | ~ r1_tarski(k2_relat_1(B_273),k1_relat_1(A_274))
      | ~ v2_funct_1(k5_relat_1(B_273,A_274))
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273)
      | ~ v1_funct_1(A_274)
      | ~ v1_relat_1(A_274) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_2367,plain,(
    ! [B_273] :
      ( v2_funct_1(B_273)
      | ~ r1_tarski(k2_relat_1(B_273),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_273,'#skF_5'))
      | ~ v1_funct_1(B_273)
      | ~ v1_relat_1(B_273)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2145,c_2364])).

tff(c_2420,plain,(
    ! [B_281] :
      ( v2_funct_1(B_281)
      | ~ r1_tarski(k2_relat_1(B_281),'#skF_4')
      | ~ v2_funct_1(k5_relat_1(B_281,'#skF_5'))
      | ~ v1_funct_1(B_281)
      | ~ v1_relat_1(B_281) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_646,c_42,c_2367])).

tff(c_2426,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1975,c_2420])).

tff(c_2432,plain,
    ( v2_funct_1('#skF_4')
    | ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_643,c_48,c_2426])).

tff(c_2433,plain,(
    ~ v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_2432])).

tff(c_1988,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_614])).

tff(c_2434,plain,(
    ! [B_285,C_282,A_287,E_284,D_286,F_283] :
      ( k1_partfun1(A_287,B_285,C_282,D_286,E_284,F_283) = k5_relat_1(E_284,F_283)
      | ~ m1_subset_1(F_283,k1_zfmisc_1(k2_zfmisc_1(C_282,D_286)))
      | ~ v1_funct_1(F_283)
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_287,B_285)))
      | ~ v1_funct_1(E_284) ) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_2436,plain,(
    ! [A_287,B_285,E_284] :
      ( k1_partfun1(A_287,B_285,'#skF_4','#skF_4',E_284,'#skF_5') = k5_relat_1(E_284,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_284,k1_zfmisc_1(k2_zfmisc_1(A_287,B_285)))
      | ~ v1_funct_1(E_284) ) ),
    inference(resolution,[status(thm)],[c_1989,c_2434])).

tff(c_2542,plain,(
    ! [A_300,B_301,E_302] :
      ( k1_partfun1(A_300,B_301,'#skF_4','#skF_4',E_302,'#skF_5') = k5_relat_1(E_302,'#skF_5')
      | ~ m1_subset_1(E_302,k1_zfmisc_1(k2_zfmisc_1(A_300,B_301)))
      | ~ v1_funct_1(E_302) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_2436])).

tff(c_2548,plain,
    ( k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_1988,c_2542])).

tff(c_2562,plain,(
    k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_2548])).

tff(c_1987,plain,(
    v2_funct_1(k1_partfun1('#skF_1','#skF_4','#skF_4','#skF_4','#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1971,c_1971,c_1971,c_615])).

tff(c_2578,plain,(
    v2_funct_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2562,c_1987])).

tff(c_2580,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_2433,c_2578])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:35:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.78/1.68  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.70  
% 4.12/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.71  %$ v1_funct_2 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.12/1.71  
% 4.12/1.71  %Foreground sorts:
% 4.12/1.71  
% 4.12/1.71  
% 4.12/1.71  %Background operators:
% 4.12/1.71  
% 4.12/1.71  
% 4.12/1.71  %Foreground operators:
% 4.12/1.71  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.12/1.71  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.12/1.71  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 4.12/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.12/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.12/1.71  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.12/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.12/1.71  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.12/1.71  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.12/1.71  tff('#skF_5', type, '#skF_5': $i).
% 4.12/1.71  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.12/1.71  tff('#skF_2', type, '#skF_2': $i).
% 4.12/1.71  tff('#skF_3', type, '#skF_3': $i).
% 4.12/1.71  tff('#skF_1', type, '#skF_1': $i).
% 4.12/1.71  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 4.12/1.71  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.12/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.12/1.71  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.12/1.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.12/1.71  tff('#skF_4', type, '#skF_4': $i).
% 4.12/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.12/1.71  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.12/1.71  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.12/1.71  
% 4.12/1.73  tff(f_116, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (v2_funct_1(k1_partfun1(A, B, B, C, D, E)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | v2_funct_1(D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_funct_2)).
% 4.12/1.73  tff(f_38, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.12/1.73  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.12/1.73  tff(f_65, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.12/1.73  tff(f_57, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.12/1.73  tff(f_29, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.12/1.73  tff(f_61, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 4.12/1.73  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_funct_2)).
% 4.12/1.73  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(k5_relat_1(B, A)) & r1_tarski(k2_relat_1(B), k1_relat_1(A))) => v2_funct_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_funct_1)).
% 4.12/1.73  tff(f_93, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.12/1.73  tff(c_32, plain, (~v2_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_8, plain, (![A_6, B_7]: (v1_relat_1(k2_zfmisc_1(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 4.12/1.73  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_65, plain, (![B_36, A_37]: (v1_relat_1(B_36) | ~m1_subset_1(B_36, k1_zfmisc_1(A_37)) | ~v1_relat_1(A_37))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.12/1.73  tff(c_71, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_44, c_65])).
% 4.12/1.73  tff(c_78, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_71])).
% 4.12/1.73  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_128, plain, (![A_46, B_47, C_48]: (k2_relset_1(A_46, B_47, C_48)=k2_relat_1(C_48) | ~m1_subset_1(C_48, k1_zfmisc_1(k2_zfmisc_1(A_46, B_47))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.12/1.73  tff(c_140, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_128])).
% 4.12/1.73  tff(c_167, plain, (![A_54, B_55, C_56]: (m1_subset_1(k2_relset_1(A_54, B_55, C_56), k1_zfmisc_1(B_55)) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_54, B_55))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.73  tff(c_187, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_140, c_167])).
% 4.12/1.73  tff(c_195, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_187])).
% 4.12/1.73  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | ~m1_subset_1(A_1, k1_zfmisc_1(B_2)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.12/1.73  tff(c_215, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_2')), inference(resolution, [status(thm)], [c_195, c_2])).
% 4.12/1.73  tff(c_38, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_74, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_38, c_65])).
% 4.12/1.73  tff(c_81, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_74])).
% 4.12/1.73  tff(c_42, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_34, plain, (k1_xboole_0='#skF_2' | k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_49, plain, (k1_xboole_0!='#skF_3'), inference(splitLeft, [status(thm)], [c_34])).
% 4.12/1.73  tff(c_40, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_95, plain, (![A_40, B_41, C_42]: (k1_relset_1(A_40, B_41, C_42)=k1_relat_1(C_42) | ~m1_subset_1(C_42, k1_zfmisc_1(k2_zfmisc_1(A_40, B_41))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.12/1.73  tff(c_108, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_38, c_95])).
% 4.12/1.73  tff(c_391, plain, (![B_87, A_88, C_89]: (k1_xboole_0=B_87 | k1_relset_1(A_88, B_87, C_89)=A_88 | ~v1_funct_2(C_89, A_88, B_87) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_88, B_87))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.12/1.73  tff(c_405, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_38, c_391])).
% 4.12/1.73  tff(c_413, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_40, c_108, c_405])).
% 4.12/1.73  tff(c_414, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_49, c_413])).
% 4.12/1.73  tff(c_421, plain, (![B_90, A_91]: (v2_funct_1(B_90) | ~r1_tarski(k2_relat_1(B_90), k1_relat_1(A_91)) | ~v2_funct_1(k5_relat_1(B_90, A_91)) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.73  tff(c_424, plain, (![B_90]: (v2_funct_1(B_90) | ~r1_tarski(k2_relat_1(B_90), '#skF_2') | ~v2_funct_1(k5_relat_1(B_90, '#skF_5')) | ~v1_funct_1(B_90) | ~v1_relat_1(B_90) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_414, c_421])).
% 4.12/1.73  tff(c_445, plain, (![B_92]: (v2_funct_1(B_92) | ~r1_tarski(k2_relat_1(B_92), '#skF_2') | ~v2_funct_1(k5_relat_1(B_92, '#skF_5')) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92))), inference(demodulation, [status(thm), theory('equality')], [c_81, c_42, c_424])).
% 4.12/1.73  tff(c_448, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_215, c_445])).
% 4.12/1.73  tff(c_451, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_48, c_448])).
% 4.12/1.73  tff(c_452, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_32, c_451])).
% 4.12/1.73  tff(c_519, plain, (![D_109, A_110, C_105, B_108, F_106, E_107]: (k1_partfun1(A_110, B_108, C_105, D_109, E_107, F_106)=k5_relat_1(E_107, F_106) | ~m1_subset_1(F_106, k1_zfmisc_1(k2_zfmisc_1(C_105, D_109))) | ~v1_funct_1(F_106) | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_110, B_108))) | ~v1_funct_1(E_107))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.12/1.73  tff(c_529, plain, (![A_110, B_108, E_107]: (k1_partfun1(A_110, B_108, '#skF_2', '#skF_3', E_107, '#skF_5')=k5_relat_1(E_107, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_107, k1_zfmisc_1(k2_zfmisc_1(A_110, B_108))) | ~v1_funct_1(E_107))), inference(resolution, [status(thm)], [c_38, c_519])).
% 4.12/1.73  tff(c_569, plain, (![A_114, B_115, E_116]: (k1_partfun1(A_114, B_115, '#skF_2', '#skF_3', E_116, '#skF_5')=k5_relat_1(E_116, '#skF_5') | ~m1_subset_1(E_116, k1_zfmisc_1(k2_zfmisc_1(A_114, B_115))) | ~v1_funct_1(E_116))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_529])).
% 4.12/1.73  tff(c_580, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_569])).
% 4.12/1.73  tff(c_588, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_580])).
% 4.12/1.73  tff(c_36, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_592, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_588, c_36])).
% 4.12/1.73  tff(c_594, plain, $false, inference(negUnitSimplification, [status(thm)], [c_452, c_592])).
% 4.12/1.73  tff(c_596, plain, (k1_xboole_0='#skF_3'), inference(splitRight, [status(thm)], [c_34])).
% 4.12/1.73  tff(c_595, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_34])).
% 4.12/1.73  tff(c_601, plain, ('#skF_2'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_596, c_595])).
% 4.12/1.73  tff(c_614, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_44])).
% 4.12/1.73  tff(c_630, plain, (![B_123, A_124]: (v1_relat_1(B_123) | ~m1_subset_1(B_123, k1_zfmisc_1(A_124)) | ~v1_relat_1(A_124))), inference(cnfTransformation, [status(thm)], [f_36])).
% 4.12/1.73  tff(c_636, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_614, c_630])).
% 4.12/1.73  tff(c_643, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_636])).
% 4.12/1.73  tff(c_46, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_116])).
% 4.12/1.73  tff(c_610, plain, (v1_funct_2('#skF_4', '#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_46])).
% 4.12/1.73  tff(c_20, plain, (![C_22, A_20]: (k1_xboole_0=C_22 | ~v1_funct_2(C_22, A_20, k1_xboole_0) | k1_xboole_0=A_20 | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, k1_xboole_0))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.12/1.73  tff(c_1352, plain, (![C_190, A_191]: (C_190='#skF_3' | ~v1_funct_2(C_190, A_191, '#skF_3') | A_191='#skF_3' | ~m1_subset_1(C_190, k1_zfmisc_1(k2_zfmisc_1(A_191, '#skF_3'))))), inference(demodulation, [status(thm), theory('equality')], [c_596, c_596, c_596, c_596, c_20])).
% 4.12/1.73  tff(c_1363, plain, ('#skF_3'='#skF_4' | ~v1_funct_2('#skF_4', '#skF_1', '#skF_3') | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_614, c_1352])).
% 4.12/1.73  tff(c_1371, plain, ('#skF_3'='#skF_4' | '#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_610, c_1363])).
% 4.12/1.73  tff(c_1376, plain, ('#skF_3'='#skF_1'), inference(splitLeft, [status(thm)], [c_1371])).
% 4.12/1.73  tff(c_693, plain, (![A_133, B_134, C_135]: (k2_relset_1(A_133, B_134, C_135)=k2_relat_1(C_135) | ~m1_subset_1(C_135, k1_zfmisc_1(k2_zfmisc_1(A_133, B_134))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.12/1.73  tff(c_705, plain, (k2_relset_1('#skF_1', '#skF_3', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_614, c_693])).
% 4.12/1.73  tff(c_733, plain, (![A_141, B_142, C_143]: (m1_subset_1(k2_relset_1(A_141, B_142, C_143), k1_zfmisc_1(B_142)) | ~m1_subset_1(C_143, k1_zfmisc_1(k2_zfmisc_1(A_141, B_142))))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.12/1.73  tff(c_753, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(superposition, [status(thm), theory('equality')], [c_705, c_733])).
% 4.12/1.73  tff(c_761, plain, (m1_subset_1(k2_relat_1('#skF_4'), k1_zfmisc_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_614, c_753])).
% 4.12/1.73  tff(c_781, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_761, c_2])).
% 4.12/1.73  tff(c_1379, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_781])).
% 4.12/1.73  tff(c_613, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_3', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_38])).
% 4.12/1.73  tff(c_639, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_3', '#skF_3'))), inference(resolution, [status(thm)], [c_613, c_630])).
% 4.12/1.73  tff(c_646, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_639])).
% 4.12/1.73  tff(c_612, plain, (v1_funct_2('#skF_5', '#skF_3', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_601, c_40])).
% 4.12/1.73  tff(c_1394, plain, (v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_1376, c_612])).
% 4.12/1.73  tff(c_647, plain, (![A_125, B_126, C_127]: (k1_relset_1(A_125, B_126, C_127)=k1_relat_1(C_127) | ~m1_subset_1(C_127, k1_zfmisc_1(k2_zfmisc_1(A_125, B_126))))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.12/1.73  tff(c_660, plain, (k1_relset_1('#skF_3', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_613, c_647])).
% 4.12/1.73  tff(c_1388, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_1376, c_660])).
% 4.12/1.73  tff(c_1393, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_1376, c_613])).
% 4.12/1.73  tff(c_1397, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_596])).
% 4.12/1.73  tff(c_26, plain, (![B_21, C_22]: (k1_relset_1(k1_xboole_0, B_21, C_22)=k1_xboole_0 | ~v1_funct_2(C_22, k1_xboole_0, B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0, B_21))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.12/1.73  tff(c_1422, plain, (![B_21, C_22]: (k1_relset_1('#skF_1', B_21, C_22)='#skF_1' | ~v1_funct_2(C_22, '#skF_1', B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1('#skF_1', B_21))))), inference(demodulation, [status(thm), theory('equality')], [c_1397, c_1397, c_1397, c_1397, c_26])).
% 4.12/1.73  tff(c_1549, plain, (k1_relset_1('#skF_1', '#skF_1', '#skF_5')='#skF_1' | ~v1_funct_2('#skF_5', '#skF_1', '#skF_1')), inference(resolution, [status(thm)], [c_1393, c_1422])).
% 4.12/1.73  tff(c_1566, plain, (k1_relat_1('#skF_5')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_1394, c_1388, c_1549])).
% 4.12/1.73  tff(c_1771, plain, (![B_218, A_219]: (v2_funct_1(B_218) | ~r1_tarski(k2_relat_1(B_218), k1_relat_1(A_219)) | ~v2_funct_1(k5_relat_1(B_218, A_219)) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | ~v1_funct_1(A_219) | ~v1_relat_1(A_219))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.73  tff(c_1774, plain, (![B_218]: (v2_funct_1(B_218) | ~r1_tarski(k2_relat_1(B_218), '#skF_1') | ~v2_funct_1(k5_relat_1(B_218, '#skF_5')) | ~v1_funct_1(B_218) | ~v1_relat_1(B_218) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1566, c_1771])).
% 4.12/1.73  tff(c_1843, plain, (![B_226]: (v2_funct_1(B_226) | ~r1_tarski(k2_relat_1(B_226), '#skF_1') | ~v2_funct_1(k5_relat_1(B_226, '#skF_5')) | ~v1_funct_1(B_226) | ~v1_relat_1(B_226))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_42, c_1774])).
% 4.12/1.73  tff(c_1849, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1379, c_1843])).
% 4.12/1.73  tff(c_1855, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_48, c_1849])).
% 4.12/1.73  tff(c_1856, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_32, c_1855])).
% 4.12/1.73  tff(c_1392, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_614])).
% 4.12/1.73  tff(c_1857, plain, (![D_231, C_227, F_228, A_232, E_229, B_230]: (k1_partfun1(A_232, B_230, C_227, D_231, E_229, F_228)=k5_relat_1(E_229, F_228) | ~m1_subset_1(F_228, k1_zfmisc_1(k2_zfmisc_1(C_227, D_231))) | ~v1_funct_1(F_228) | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_229))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.12/1.73  tff(c_1859, plain, (![A_232, B_230, E_229]: (k1_partfun1(A_232, B_230, '#skF_1', '#skF_1', E_229, '#skF_5')=k5_relat_1(E_229, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_229, k1_zfmisc_1(k2_zfmisc_1(A_232, B_230))) | ~v1_funct_1(E_229))), inference(resolution, [status(thm)], [c_1393, c_1857])).
% 4.12/1.73  tff(c_1932, plain, (![A_240, B_241, E_242]: (k1_partfun1(A_240, B_241, '#skF_1', '#skF_1', E_242, '#skF_5')=k5_relat_1(E_242, '#skF_5') | ~m1_subset_1(E_242, k1_zfmisc_1(k2_zfmisc_1(A_240, B_241))) | ~v1_funct_1(E_242))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_1859])).
% 4.12/1.73  tff(c_1938, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1392, c_1932])).
% 4.12/1.73  tff(c_1952, plain, (k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1938])).
% 4.12/1.73  tff(c_615, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_3', '#skF_3', '#skF_3', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_601, c_601, c_36])).
% 4.12/1.73  tff(c_1391, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_1', '#skF_1', '#skF_1', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1376, c_1376, c_1376, c_615])).
% 4.12/1.73  tff(c_1968, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1952, c_1391])).
% 4.12/1.73  tff(c_1970, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1856, c_1968])).
% 4.12/1.73  tff(c_1971, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_1371])).
% 4.12/1.73  tff(c_1975, plain, (r1_tarski(k2_relat_1('#skF_4'), '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_781])).
% 4.12/1.73  tff(c_1990, plain, (v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_1971, c_612])).
% 4.12/1.73  tff(c_1984, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')=k1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_1971, c_660])).
% 4.12/1.73  tff(c_1989, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_4', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_1971, c_613])).
% 4.12/1.73  tff(c_1993, plain, (k1_xboole_0='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_596])).
% 4.12/1.73  tff(c_2109, plain, (![B_21, C_22]: (k1_relset_1('#skF_4', B_21, C_22)='#skF_4' | ~v1_funct_2(C_22, '#skF_4', B_21) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1('#skF_4', B_21))))), inference(demodulation, [status(thm), theory('equality')], [c_1993, c_1993, c_1993, c_1993, c_26])).
% 4.12/1.73  tff(c_2127, plain, (k1_relset_1('#skF_4', '#skF_4', '#skF_5')='#skF_4' | ~v1_funct_2('#skF_5', '#skF_4', '#skF_4')), inference(resolution, [status(thm)], [c_1989, c_2109])).
% 4.12/1.73  tff(c_2145, plain, (k1_relat_1('#skF_5')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_1990, c_1984, c_2127])).
% 4.12/1.73  tff(c_2364, plain, (![B_273, A_274]: (v2_funct_1(B_273) | ~r1_tarski(k2_relat_1(B_273), k1_relat_1(A_274)) | ~v2_funct_1(k5_relat_1(B_273, A_274)) | ~v1_funct_1(B_273) | ~v1_relat_1(B_273) | ~v1_funct_1(A_274) | ~v1_relat_1(A_274))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.12/1.73  tff(c_2367, plain, (![B_273]: (v2_funct_1(B_273) | ~r1_tarski(k2_relat_1(B_273), '#skF_4') | ~v2_funct_1(k5_relat_1(B_273, '#skF_5')) | ~v1_funct_1(B_273) | ~v1_relat_1(B_273) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_2145, c_2364])).
% 4.12/1.73  tff(c_2420, plain, (![B_281]: (v2_funct_1(B_281) | ~r1_tarski(k2_relat_1(B_281), '#skF_4') | ~v2_funct_1(k5_relat_1(B_281, '#skF_5')) | ~v1_funct_1(B_281) | ~v1_relat_1(B_281))), inference(demodulation, [status(thm), theory('equality')], [c_646, c_42, c_2367])).
% 4.12/1.73  tff(c_2426, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_1975, c_2420])).
% 4.12/1.73  tff(c_2432, plain, (v2_funct_1('#skF_4') | ~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_643, c_48, c_2426])).
% 4.12/1.73  tff(c_2433, plain, (~v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(negUnitSimplification, [status(thm)], [c_32, c_2432])).
% 4.12/1.73  tff(c_1988, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_614])).
% 4.12/1.73  tff(c_2434, plain, (![B_285, C_282, A_287, E_284, D_286, F_283]: (k1_partfun1(A_287, B_285, C_282, D_286, E_284, F_283)=k5_relat_1(E_284, F_283) | ~m1_subset_1(F_283, k1_zfmisc_1(k2_zfmisc_1(C_282, D_286))) | ~v1_funct_1(F_283) | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_287, B_285))) | ~v1_funct_1(E_284))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.12/1.73  tff(c_2436, plain, (![A_287, B_285, E_284]: (k1_partfun1(A_287, B_285, '#skF_4', '#skF_4', E_284, '#skF_5')=k5_relat_1(E_284, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_284, k1_zfmisc_1(k2_zfmisc_1(A_287, B_285))) | ~v1_funct_1(E_284))), inference(resolution, [status(thm)], [c_1989, c_2434])).
% 4.12/1.73  tff(c_2542, plain, (![A_300, B_301, E_302]: (k1_partfun1(A_300, B_301, '#skF_4', '#skF_4', E_302, '#skF_5')=k5_relat_1(E_302, '#skF_5') | ~m1_subset_1(E_302, k1_zfmisc_1(k2_zfmisc_1(A_300, B_301))) | ~v1_funct_1(E_302))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_2436])).
% 4.12/1.73  tff(c_2548, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_1988, c_2542])).
% 4.12/1.73  tff(c_2562, plain, (k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_2548])).
% 4.12/1.73  tff(c_1987, plain, (v2_funct_1(k1_partfun1('#skF_1', '#skF_4', '#skF_4', '#skF_4', '#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_1971, c_1971, c_1971, c_615])).
% 4.12/1.73  tff(c_2578, plain, (v2_funct_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2562, c_1987])).
% 4.12/1.73  tff(c_2580, plain, $false, inference(negUnitSimplification, [status(thm)], [c_2433, c_2578])).
% 4.12/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.12/1.73  
% 4.12/1.73  Inference rules
% 4.12/1.73  ----------------------
% 4.12/1.73  #Ref     : 0
% 4.12/1.73  #Sup     : 493
% 4.12/1.73  #Fact    : 0
% 4.12/1.73  #Define  : 0
% 4.12/1.73  #Split   : 11
% 4.12/1.73  #Chain   : 0
% 4.12/1.73  #Close   : 0
% 4.12/1.73  
% 4.12/1.73  Ordering : KBO
% 4.12/1.73  
% 4.12/1.73  Simplification rules
% 4.12/1.73  ----------------------
% 4.12/1.73  #Subsume      : 27
% 4.12/1.73  #Demod        : 597
% 4.12/1.73  #Tautology    : 262
% 4.12/1.73  #SimpNegUnit  : 17
% 4.12/1.73  #BackRed      : 93
% 4.12/1.73  
% 4.12/1.73  #Partial instantiations: 0
% 4.12/1.73  #Strategies tried      : 1
% 4.12/1.73  
% 4.12/1.73  Timing (in seconds)
% 4.12/1.73  ----------------------
% 4.12/1.74  Preprocessing        : 0.31
% 4.12/1.74  Parsing              : 0.16
% 4.12/1.74  CNF conversion       : 0.02
% 4.12/1.74  Main loop            : 0.62
% 4.12/1.74  Inferencing          : 0.23
% 4.12/1.74  Reduction            : 0.20
% 4.12/1.74  Demodulation         : 0.14
% 4.12/1.74  BG Simplification    : 0.03
% 4.12/1.74  Subsumption          : 0.09
% 4.12/1.74  Abstraction          : 0.03
% 4.12/1.74  MUC search           : 0.00
% 4.12/1.74  Cooper               : 0.00
% 4.12/1.74  Total                : 1.00
% 4.12/1.74  Index Insertion      : 0.00
% 4.12/1.74  Index Deletion       : 0.00
% 4.12/1.74  Index Matching       : 0.00
% 4.12/1.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------
