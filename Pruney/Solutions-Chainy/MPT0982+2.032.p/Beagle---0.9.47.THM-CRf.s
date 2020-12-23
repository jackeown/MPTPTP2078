%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:59 EST 2020

% Result     : Theorem 16.50s
% Output     : CNFRefutation 16.68s
% Verified   : 
% Statistics : Number of formulae       :  111 ( 337 expanded)
%              Number of leaves         :   40 ( 137 expanded)
%              Depth                    :   15
%              Number of atoms          :  228 (1176 expanded)
%              Number of equality atoms :   62 ( 340 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_relset_1,type,(
    k4_relset_1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_147,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_funct_2)).

tff(f_81,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_46,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_67,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_115,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_87,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_73,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k1_relset_1(A,B,C) = k1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

tff(f_105,axiom,(
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

tff(f_125,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_funct_1(A)
        & v1_funct_2(A,k1_relat_1(A),k2_relat_1(A))
        & m1_subset_1(A,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A),k2_relat_1(A)))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

tff(f_44,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( v5_relat_1(B,A)
      <=> r1_tarski(k2_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_61,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( k2_relat_1(k5_relat_1(B,A)) = k2_relat_1(A)
              & v2_funct_1(A) )
           => r1_tarski(k1_relat_1(A),k2_relat_1(B)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_funct_1)).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_168,plain,(
    ! [A_70,B_71,C_72] :
      ( k2_relset_1(A_70,B_71,C_72) = k2_relat_1(C_72)
      | ~ m1_subset_1(C_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_180,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_168])).

tff(c_50,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_4') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_185,plain,(
    k2_relat_1('#skF_4') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_50])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_79,plain,(
    ! [B_50,A_51] :
      ( v1_relat_1(B_50)
      | ~ m1_subset_1(B_50,k1_zfmisc_1(A_51))
      | ~ v1_relat_1(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_85,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_64,c_79])).

tff(c_91,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_85])).

tff(c_109,plain,(
    ! [C_57,B_58,A_59] :
      ( v5_relat_1(C_57,B_58)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_59,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_117,plain,(
    v5_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_109])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_62,plain,(
    v1_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_58,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_641,plain,(
    ! [A_108,D_111,F_110,B_109,C_113,E_112] :
      ( k1_partfun1(A_108,B_109,C_113,D_111,E_112,F_110) = k5_relat_1(E_112,F_110)
      | ~ m1_subset_1(F_110,k1_zfmisc_1(k2_zfmisc_1(C_113,D_111)))
      | ~ v1_funct_1(F_110)
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_112) ) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_655,plain,(
    ! [A_108,B_109,E_112] :
      ( k1_partfun1(A_108,B_109,'#skF_2','#skF_3',E_112,'#skF_5') = k5_relat_1(E_112,'#skF_5')
      | ~ v1_funct_1('#skF_5')
      | ~ m1_subset_1(E_112,k1_zfmisc_1(k2_zfmisc_1(A_108,B_109)))
      | ~ v1_funct_1(E_112) ) ),
    inference(resolution,[status(thm)],[c_58,c_641])).

tff(c_850,plain,(
    ! [A_117,B_118,E_119] :
      ( k1_partfun1(A_117,B_118,'#skF_2','#skF_3',E_119,'#skF_5') = k5_relat_1(E_119,'#skF_5')
      | ~ m1_subset_1(E_119,k1_zfmisc_1(k2_zfmisc_1(A_117,B_118)))
      | ~ v1_funct_1(E_119) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_655])).

tff(c_880,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_850])).

tff(c_898,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_880])).

tff(c_56,plain,(
    k2_relset_1('#skF_1','#skF_3',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_905,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_898,c_56])).

tff(c_357,plain,(
    ! [E_94,A_95,C_96,B_97,F_93,D_98] :
      ( k4_relset_1(A_95,B_97,C_96,D_98,E_94,F_93) = k5_relat_1(E_94,F_93)
      | ~ m1_subset_1(F_93,k1_zfmisc_1(k2_zfmisc_1(C_96,D_98)))
      | ~ m1_subset_1(E_94,k1_zfmisc_1(k2_zfmisc_1(A_95,B_97))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_417,plain,(
    ! [A_99,B_100,E_101] :
      ( k4_relset_1(A_99,B_100,'#skF_2','#skF_3',E_101,'#skF_5') = k5_relat_1(E_101,'#skF_5')
      | ~ m1_subset_1(E_101,k1_zfmisc_1(k2_zfmisc_1(A_99,B_100))) ) ),
    inference(resolution,[status(thm)],[c_58,c_357])).

tff(c_433,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2','#skF_3','#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_64,c_417])).

tff(c_22,plain,(
    ! [C_18,B_17,A_16,D_19,E_20,F_21] :
      ( m1_subset_1(k4_relset_1(A_16,B_17,C_18,D_19,E_20,F_21),k1_zfmisc_1(k2_zfmisc_1(A_16,D_19)))
      | ~ m1_subset_1(F_21,k1_zfmisc_1(k2_zfmisc_1(C_18,D_19)))
      | ~ m1_subset_1(E_20,k1_zfmisc_1(k2_zfmisc_1(A_16,B_17))) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_594,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3')))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_3')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_433,c_22])).

tff(c_598,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_3'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_58,c_594])).

tff(c_26,plain,(
    ! [A_25,B_26,C_27] :
      ( k2_relset_1(A_25,B_26,C_27) = k2_relat_1(C_27)
      | ~ m1_subset_1(C_27,k1_zfmisc_1(k2_zfmisc_1(A_25,B_26))) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_634,plain,(
    k2_relset_1('#skF_1','#skF_3',k5_relat_1('#skF_4','#skF_5')) = k2_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_598,c_26])).

tff(c_910,plain,(
    k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_905,c_634])).

tff(c_82,plain,
    ( v1_relat_1('#skF_5')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_3')) ),
    inference(resolution,[status(thm)],[c_58,c_79])).

tff(c_88,plain,(
    v1_relat_1('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_82])).

tff(c_116,plain,(
    v5_relat_1('#skF_5','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_109])).

tff(c_8,plain,(
    ! [B_5,A_3] :
      ( v1_relat_1(B_5)
      | ~ m1_subset_1(B_5,k1_zfmisc_1(A_3))
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_625,plain,
    ( v1_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_3')) ),
    inference(resolution,[status(thm)],[c_598,c_8])).

tff(c_640,plain,(
    v1_relat_1(k5_relat_1('#skF_4','#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_625])).

tff(c_52,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_60,plain,(
    v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_131,plain,(
    ! [A_65,B_66,C_67] :
      ( k1_relset_1(A_65,B_66,C_67) = k1_relat_1(C_67)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_65,B_66))) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_138,plain,(
    k1_relset_1('#skF_2','#skF_3','#skF_5') = k1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_58,c_131])).

tff(c_244,plain,(
    ! [B_88,A_89,C_90] :
      ( k1_xboole_0 = B_88
      | k1_relset_1(A_89,B_88,C_90) = A_89
      | ~ v1_funct_2(C_90,A_89,B_88)
      | ~ m1_subset_1(C_90,k1_zfmisc_1(k2_zfmisc_1(A_89,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_250,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relset_1('#skF_2','#skF_3','#skF_5') = '#skF_2'
    | ~ v1_funct_2('#skF_5','#skF_2','#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_244])).

tff(c_257,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_relat_1('#skF_5') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_138,c_250])).

tff(c_258,plain,(
    k1_relat_1('#skF_5') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_257])).

tff(c_44,plain,(
    ! [A_43] :
      ( m1_subset_1(A_43,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43),k2_relat_1(A_43))))
      | ~ v1_funct_1(A_43)
      | ~ v1_relat_1(A_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_125])).

tff(c_286,plain,
    ( m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5'))))
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_44])).

tff(c_301,plain,(
    m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_286])).

tff(c_1472,plain,(
    ! [A_156,B_157,A_158,E_159] :
      ( k4_relset_1(A_156,B_157,k1_relat_1(A_158),k2_relat_1(A_158),E_159,A_158) = k5_relat_1(E_159,A_158)
      | ~ m1_subset_1(E_159,k1_zfmisc_1(k2_zfmisc_1(A_156,B_157)))
      | ~ v1_funct_1(A_158)
      | ~ v1_relat_1(A_158) ) ),
    inference(resolution,[status(thm)],[c_44,c_357])).

tff(c_2135,plain,(
    ! [A_188] :
      ( k4_relset_1('#skF_1','#skF_2',k1_relat_1(A_188),k2_relat_1(A_188),'#skF_4',A_188) = k5_relat_1('#skF_4',A_188)
      | ~ v1_funct_1(A_188)
      | ~ v1_relat_1(A_188) ) ),
    inference(resolution,[status(thm)],[c_64,c_1472])).

tff(c_2153,plain,
    ( k4_relset_1('#skF_1','#skF_2','#skF_2',k2_relat_1('#skF_5'),'#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5')
    | ~ v1_funct_1('#skF_5')
    | ~ v1_relat_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_2135])).

tff(c_2163,plain,(
    k4_relset_1('#skF_1','#skF_2','#skF_2',k2_relat_1('#skF_5'),'#skF_4','#skF_5') = k5_relat_1('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_2153])).

tff(c_2167,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_5',k1_zfmisc_1(k2_zfmisc_1('#skF_2',k2_relat_1('#skF_5'))))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_2163,c_22])).

tff(c_2171,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_5'),k1_zfmisc_1(k2_zfmisc_1('#skF_1',k2_relat_1('#skF_5')))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_301,c_2167])).

tff(c_18,plain,(
    ! [C_15,B_14,A_13] :
      ( v5_relat_1(C_15,B_14)
      | ~ m1_subset_1(C_15,k1_zfmisc_1(k2_zfmisc_1(A_13,B_14))) ) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_2264,plain,(
    v5_relat_1(k5_relat_1('#skF_4','#skF_5'),k2_relat_1('#skF_5')) ),
    inference(resolution,[status(thm)],[c_2171,c_18])).

tff(c_12,plain,(
    ! [B_7,A_6] :
      ( r1_tarski(k2_relat_1(B_7),A_6)
      | ~ v5_relat_1(B_7,A_6)
      | ~ v1_relat_1(B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_101,plain,(
    ! [B_55,A_56] :
      ( r1_tarski(k2_relat_1(B_55),A_56)
      | ~ v5_relat_1(B_55,A_56)
      | ~ v1_relat_1(B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_191,plain,(
    ! [B_75,A_76] :
      ( k2_relat_1(B_75) = A_76
      | ~ r1_tarski(A_76,k2_relat_1(B_75))
      | ~ v5_relat_1(B_75,A_76)
      | ~ v1_relat_1(B_75) ) ),
    inference(resolution,[status(thm)],[c_101,c_2])).

tff(c_200,plain,(
    ! [B_75,B_7] :
      ( k2_relat_1(B_75) = k2_relat_1(B_7)
      | ~ v5_relat_1(B_75,k2_relat_1(B_7))
      | ~ v1_relat_1(B_75)
      | ~ v5_relat_1(B_7,k2_relat_1(B_75))
      | ~ v1_relat_1(B_7) ) ),
    inference(resolution,[status(thm)],[c_12,c_191])).

tff(c_2277,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_5')) = k2_relat_1('#skF_5')
    | ~ v1_relat_1(k5_relat_1('#skF_4','#skF_5'))
    | ~ v5_relat_1('#skF_5',k2_relat_1(k5_relat_1('#skF_4','#skF_5')))
    | ~ v1_relat_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_2264,c_200])).

tff(c_2282,plain,(
    k2_relat_1('#skF_5') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_116,c_910,c_640,c_910,c_2277])).

tff(c_54,plain,(
    v2_funct_1('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_147])).

tff(c_262,plain,(
    ! [A_91,B_92] :
      ( r1_tarski(k1_relat_1(A_91),k2_relat_1(B_92))
      | ~ v2_funct_1(A_91)
      | k2_relat_1(k5_relat_1(B_92,A_91)) != k2_relat_1(A_91)
      | ~ v1_funct_1(B_92)
      | ~ v1_relat_1(B_92)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1733,plain,(
    ! [B_170,A_171] :
      ( k2_relat_1(B_170) = k1_relat_1(A_171)
      | ~ r1_tarski(k2_relat_1(B_170),k1_relat_1(A_171))
      | ~ v2_funct_1(A_171)
      | k2_relat_1(k5_relat_1(B_170,A_171)) != k2_relat_1(A_171)
      | ~ v1_funct_1(B_170)
      | ~ v1_relat_1(B_170)
      | ~ v1_funct_1(A_171)
      | ~ v1_relat_1(A_171) ) ),
    inference(resolution,[status(thm)],[c_262,c_2])).

tff(c_14872,plain,(
    ! [B_770,A_771] :
      ( k2_relat_1(B_770) = k1_relat_1(A_771)
      | ~ v2_funct_1(A_771)
      | k2_relat_1(k5_relat_1(B_770,A_771)) != k2_relat_1(A_771)
      | ~ v1_funct_1(B_770)
      | ~ v1_funct_1(A_771)
      | ~ v1_relat_1(A_771)
      | ~ v5_relat_1(B_770,k1_relat_1(A_771))
      | ~ v1_relat_1(B_770) ) ),
    inference(resolution,[status(thm)],[c_12,c_1733])).

tff(c_14886,plain,(
    ! [B_770] :
      ( k2_relat_1(B_770) = k1_relat_1('#skF_5')
      | ~ v2_funct_1('#skF_5')
      | k2_relat_1(k5_relat_1(B_770,'#skF_5')) != k2_relat_1('#skF_5')
      | ~ v1_funct_1(B_770)
      | ~ v1_funct_1('#skF_5')
      | ~ v1_relat_1('#skF_5')
      | ~ v5_relat_1(B_770,'#skF_2')
      | ~ v1_relat_1(B_770) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_258,c_14872])).

tff(c_20053,plain,(
    ! [B_968] :
      ( k2_relat_1(B_968) = '#skF_2'
      | k2_relat_1(k5_relat_1(B_968,'#skF_5')) != '#skF_3'
      | ~ v1_funct_1(B_968)
      | ~ v5_relat_1(B_968,'#skF_2')
      | ~ v1_relat_1(B_968) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_62,c_2282,c_54,c_258,c_14886])).

tff(c_20056,plain,
    ( k2_relat_1('#skF_4') = '#skF_2'
    | ~ v1_funct_1('#skF_4')
    | ~ v5_relat_1('#skF_4','#skF_2')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_910,c_20053])).

tff(c_20059,plain,(
    k2_relat_1('#skF_4') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_91,c_117,c_68,c_20056])).

tff(c_20061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_185,c_20059])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n017.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 09:54:01 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 16.50/7.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.50/7.51  
% 16.50/7.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.50/7.51  %$ v1_funct_2 > v5_relat_1 > v4_relat_1 > r1_tarski > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k1_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 16.50/7.51  
% 16.50/7.51  %Foreground sorts:
% 16.50/7.51  
% 16.50/7.51  
% 16.50/7.51  %Background operators:
% 16.50/7.51  
% 16.50/7.51  
% 16.50/7.51  %Foreground operators:
% 16.50/7.51  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 16.50/7.51  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 16.50/7.51  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 16.50/7.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 16.50/7.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 16.50/7.51  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 16.50/7.51  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.50/7.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 16.50/7.51  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 16.50/7.51  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 16.50/7.51  tff('#skF_5', type, '#skF_5': $i).
% 16.50/7.51  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 16.50/7.51  tff('#skF_2', type, '#skF_2': $i).
% 16.50/7.51  tff('#skF_3', type, '#skF_3': $i).
% 16.50/7.51  tff('#skF_1', type, '#skF_1': $i).
% 16.50/7.51  tff(k1_relset_1, type, k1_relset_1: ($i * $i * $i) > $i).
% 16.50/7.51  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 16.50/7.51  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 16.50/7.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 16.50/7.51  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 16.50/7.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 16.50/7.51  tff('#skF_4', type, '#skF_4': $i).
% 16.50/7.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 16.50/7.51  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 16.50/7.51  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 16.50/7.51  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 16.50/7.51  
% 16.68/7.53  tff(f_147, negated_conjecture, ~(![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => (((k2_relset_1(A, C, k1_partfun1(A, B, B, C, D, E)) = C) & v2_funct_1(E)) => ((C = k1_xboole_0) | (k2_relset_1(A, B, D) = B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_funct_2)).
% 16.68/7.53  tff(f_81, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 16.68/7.53  tff(f_46, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc6_relat_1)).
% 16.68/7.53  tff(f_38, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relat_1)).
% 16.68/7.53  tff(f_67, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 16.68/7.53  tff(f_115, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 16.68/7.53  tff(f_87, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 16.68/7.53  tff(f_73, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 16.68/7.53  tff(f_77, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k1_relset_1(A, B, C) = k1_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_relset_1)).
% 16.68/7.53  tff(f_105, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => ((((B = k1_xboole_0) => (A = k1_xboole_0)) => (v1_funct_2(C, A, B) <=> (A = k1_relset_1(A, B, C)))) & ((B = k1_xboole_0) => ((A = k1_xboole_0) | (v1_funct_2(C, A, B) <=> (C = k1_xboole_0))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_funct_2)).
% 16.68/7.53  tff(f_125, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => ((v1_funct_1(A) & v1_funct_2(A, k1_relat_1(A), k2_relat_1(A))) & m1_subset_1(A, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A), k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_funct_2)).
% 16.68/7.53  tff(f_44, axiom, (![A, B]: (v1_relat_1(B) => (v5_relat_1(B, A) <=> r1_tarski(k2_relat_1(B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d19_relat_1)).
% 16.68/7.53  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 16.68/7.53  tff(f_61, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => (((k2_relat_1(k5_relat_1(B, A)) = k2_relat_1(A)) & v2_funct_1(A)) => r1_tarski(k1_relat_1(A), k2_relat_1(B))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_funct_1)).
% 16.68/7.53  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_168, plain, (![A_70, B_71, C_72]: (k2_relset_1(A_70, B_71, C_72)=k2_relat_1(C_72) | ~m1_subset_1(C_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.68/7.53  tff(c_180, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_168])).
% 16.68/7.53  tff(c_50, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_4')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_185, plain, (k2_relat_1('#skF_4')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_50])).
% 16.68/7.53  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 16.68/7.53  tff(c_79, plain, (![B_50, A_51]: (v1_relat_1(B_50) | ~m1_subset_1(B_50, k1_zfmisc_1(A_51)) | ~v1_relat_1(A_51))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.68/7.53  tff(c_85, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_64, c_79])).
% 16.68/7.53  tff(c_91, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_85])).
% 16.68/7.53  tff(c_109, plain, (![C_57, B_58, A_59]: (v5_relat_1(C_57, B_58) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_59, B_58))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.68/7.53  tff(c_117, plain, (v5_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_109])).
% 16.68/7.53  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_62, plain, (v1_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_58, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3')))), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_641, plain, (![A_108, D_111, F_110, B_109, C_113, E_112]: (k1_partfun1(A_108, B_109, C_113, D_111, E_112, F_110)=k5_relat_1(E_112, F_110) | ~m1_subset_1(F_110, k1_zfmisc_1(k2_zfmisc_1(C_113, D_111))) | ~v1_funct_1(F_110) | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_112))), inference(cnfTransformation, [status(thm)], [f_115])).
% 16.68/7.53  tff(c_655, plain, (![A_108, B_109, E_112]: (k1_partfun1(A_108, B_109, '#skF_2', '#skF_3', E_112, '#skF_5')=k5_relat_1(E_112, '#skF_5') | ~v1_funct_1('#skF_5') | ~m1_subset_1(E_112, k1_zfmisc_1(k2_zfmisc_1(A_108, B_109))) | ~v1_funct_1(E_112))), inference(resolution, [status(thm)], [c_58, c_641])).
% 16.68/7.53  tff(c_850, plain, (![A_117, B_118, E_119]: (k1_partfun1(A_117, B_118, '#skF_2', '#skF_3', E_119, '#skF_5')=k5_relat_1(E_119, '#skF_5') | ~m1_subset_1(E_119, k1_zfmisc_1(k2_zfmisc_1(A_117, B_118))) | ~v1_funct_1(E_119))), inference(demodulation, [status(thm), theory('equality')], [c_62, c_655])).
% 16.68/7.53  tff(c_880, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_850])).
% 16.68/7.53  tff(c_898, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_68, c_880])).
% 16.68/7.53  tff(c_56, plain, (k2_relset_1('#skF_1', '#skF_3', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_905, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_898, c_56])).
% 16.68/7.53  tff(c_357, plain, (![E_94, A_95, C_96, B_97, F_93, D_98]: (k4_relset_1(A_95, B_97, C_96, D_98, E_94, F_93)=k5_relat_1(E_94, F_93) | ~m1_subset_1(F_93, k1_zfmisc_1(k2_zfmisc_1(C_96, D_98))) | ~m1_subset_1(E_94, k1_zfmisc_1(k2_zfmisc_1(A_95, B_97))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 16.68/7.53  tff(c_417, plain, (![A_99, B_100, E_101]: (k4_relset_1(A_99, B_100, '#skF_2', '#skF_3', E_101, '#skF_5')=k5_relat_1(E_101, '#skF_5') | ~m1_subset_1(E_101, k1_zfmisc_1(k2_zfmisc_1(A_99, B_100))))), inference(resolution, [status(thm)], [c_58, c_357])).
% 16.68/7.53  tff(c_433, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', '#skF_3', '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_64, c_417])).
% 16.68/7.53  tff(c_22, plain, (![C_18, B_17, A_16, D_19, E_20, F_21]: (m1_subset_1(k4_relset_1(A_16, B_17, C_18, D_19, E_20, F_21), k1_zfmisc_1(k2_zfmisc_1(A_16, D_19))) | ~m1_subset_1(F_21, k1_zfmisc_1(k2_zfmisc_1(C_18, D_19))) | ~m1_subset_1(E_20, k1_zfmisc_1(k2_zfmisc_1(A_16, B_17))))), inference(cnfTransformation, [status(thm)], [f_73])).
% 16.68/7.53  tff(c_594, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3'))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_3'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_433, c_22])).
% 16.68/7.53  tff(c_598, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_58, c_594])).
% 16.68/7.53  tff(c_26, plain, (![A_25, B_26, C_27]: (k2_relset_1(A_25, B_26, C_27)=k2_relat_1(C_27) | ~m1_subset_1(C_27, k1_zfmisc_1(k2_zfmisc_1(A_25, B_26))))), inference(cnfTransformation, [status(thm)], [f_81])).
% 16.68/7.53  tff(c_634, plain, (k2_relset_1('#skF_1', '#skF_3', k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_598, c_26])).
% 16.68/7.53  tff(c_910, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_905, c_634])).
% 16.68/7.53  tff(c_82, plain, (v1_relat_1('#skF_5') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_3'))), inference(resolution, [status(thm)], [c_58, c_79])).
% 16.68/7.53  tff(c_88, plain, (v1_relat_1('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_82])).
% 16.68/7.53  tff(c_116, plain, (v5_relat_1('#skF_5', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_109])).
% 16.68/7.53  tff(c_8, plain, (![B_5, A_3]: (v1_relat_1(B_5) | ~m1_subset_1(B_5, k1_zfmisc_1(A_3)) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_38])).
% 16.68/7.53  tff(c_625, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_3'))), inference(resolution, [status(thm)], [c_598, c_8])).
% 16.68/7.53  tff(c_640, plain, (v1_relat_1(k5_relat_1('#skF_4', '#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_625])).
% 16.68/7.53  tff(c_52, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_60, plain, (v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_131, plain, (![A_65, B_66, C_67]: (k1_relset_1(A_65, B_66, C_67)=k1_relat_1(C_67) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_65, B_66))))), inference(cnfTransformation, [status(thm)], [f_77])).
% 16.68/7.53  tff(c_138, plain, (k1_relset_1('#skF_2', '#skF_3', '#skF_5')=k1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_58, c_131])).
% 16.68/7.53  tff(c_244, plain, (![B_88, A_89, C_90]: (k1_xboole_0=B_88 | k1_relset_1(A_89, B_88, C_90)=A_89 | ~v1_funct_2(C_90, A_89, B_88) | ~m1_subset_1(C_90, k1_zfmisc_1(k2_zfmisc_1(A_89, B_88))))), inference(cnfTransformation, [status(thm)], [f_105])).
% 16.68/7.53  tff(c_250, plain, (k1_xboole_0='#skF_3' | k1_relset_1('#skF_2', '#skF_3', '#skF_5')='#skF_2' | ~v1_funct_2('#skF_5', '#skF_2', '#skF_3')), inference(resolution, [status(thm)], [c_58, c_244])).
% 16.68/7.53  tff(c_257, plain, (k1_xboole_0='#skF_3' | k1_relat_1('#skF_5')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_138, c_250])).
% 16.68/7.53  tff(c_258, plain, (k1_relat_1('#skF_5')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_52, c_257])).
% 16.68/7.53  tff(c_44, plain, (![A_43]: (m1_subset_1(A_43, k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(A_43), k2_relat_1(A_43)))) | ~v1_funct_1(A_43) | ~v1_relat_1(A_43))), inference(cnfTransformation, [status(thm)], [f_125])).
% 16.68/7.53  tff(c_286, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5')))) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_258, c_44])).
% 16.68/7.53  tff(c_301, plain, (m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_286])).
% 16.68/7.53  tff(c_1472, plain, (![A_156, B_157, A_158, E_159]: (k4_relset_1(A_156, B_157, k1_relat_1(A_158), k2_relat_1(A_158), E_159, A_158)=k5_relat_1(E_159, A_158) | ~m1_subset_1(E_159, k1_zfmisc_1(k2_zfmisc_1(A_156, B_157))) | ~v1_funct_1(A_158) | ~v1_relat_1(A_158))), inference(resolution, [status(thm)], [c_44, c_357])).
% 16.68/7.53  tff(c_2135, plain, (![A_188]: (k4_relset_1('#skF_1', '#skF_2', k1_relat_1(A_188), k2_relat_1(A_188), '#skF_4', A_188)=k5_relat_1('#skF_4', A_188) | ~v1_funct_1(A_188) | ~v1_relat_1(A_188))), inference(resolution, [status(thm)], [c_64, c_1472])).
% 16.68/7.53  tff(c_2153, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', k2_relat_1('#skF_5'), '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5') | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_258, c_2135])).
% 16.68/7.53  tff(c_2163, plain, (k4_relset_1('#skF_1', '#skF_2', '#skF_2', k2_relat_1('#skF_5'), '#skF_4', '#skF_5')=k5_relat_1('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_2153])).
% 16.68/7.53  tff(c_2167, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_5')))) | ~m1_subset_1('#skF_5', k1_zfmisc_1(k2_zfmisc_1('#skF_2', k2_relat_1('#skF_5')))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_2163, c_22])).
% 16.68/7.53  tff(c_2171, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_5'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', k2_relat_1('#skF_5'))))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_301, c_2167])).
% 16.68/7.53  tff(c_18, plain, (![C_15, B_14, A_13]: (v5_relat_1(C_15, B_14) | ~m1_subset_1(C_15, k1_zfmisc_1(k2_zfmisc_1(A_13, B_14))))), inference(cnfTransformation, [status(thm)], [f_67])).
% 16.68/7.53  tff(c_2264, plain, (v5_relat_1(k5_relat_1('#skF_4', '#skF_5'), k2_relat_1('#skF_5'))), inference(resolution, [status(thm)], [c_2171, c_18])).
% 16.68/7.53  tff(c_12, plain, (![B_7, A_6]: (r1_tarski(k2_relat_1(B_7), A_6) | ~v5_relat_1(B_7, A_6) | ~v1_relat_1(B_7))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.68/7.53  tff(c_101, plain, (![B_55, A_56]: (r1_tarski(k2_relat_1(B_55), A_56) | ~v5_relat_1(B_55, A_56) | ~v1_relat_1(B_55))), inference(cnfTransformation, [status(thm)], [f_44])).
% 16.68/7.53  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 16.68/7.53  tff(c_191, plain, (![B_75, A_76]: (k2_relat_1(B_75)=A_76 | ~r1_tarski(A_76, k2_relat_1(B_75)) | ~v5_relat_1(B_75, A_76) | ~v1_relat_1(B_75))), inference(resolution, [status(thm)], [c_101, c_2])).
% 16.68/7.53  tff(c_200, plain, (![B_75, B_7]: (k2_relat_1(B_75)=k2_relat_1(B_7) | ~v5_relat_1(B_75, k2_relat_1(B_7)) | ~v1_relat_1(B_75) | ~v5_relat_1(B_7, k2_relat_1(B_75)) | ~v1_relat_1(B_7))), inference(resolution, [status(thm)], [c_12, c_191])).
% 16.68/7.53  tff(c_2277, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))=k2_relat_1('#skF_5') | ~v1_relat_1(k5_relat_1('#skF_4', '#skF_5')) | ~v5_relat_1('#skF_5', k2_relat_1(k5_relat_1('#skF_4', '#skF_5'))) | ~v1_relat_1('#skF_5')), inference(resolution, [status(thm)], [c_2264, c_200])).
% 16.68/7.53  tff(c_2282, plain, (k2_relat_1('#skF_5')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_88, c_116, c_910, c_640, c_910, c_2277])).
% 16.68/7.53  tff(c_54, plain, (v2_funct_1('#skF_5')), inference(cnfTransformation, [status(thm)], [f_147])).
% 16.68/7.53  tff(c_262, plain, (![A_91, B_92]: (r1_tarski(k1_relat_1(A_91), k2_relat_1(B_92)) | ~v2_funct_1(A_91) | k2_relat_1(k5_relat_1(B_92, A_91))!=k2_relat_1(A_91) | ~v1_funct_1(B_92) | ~v1_relat_1(B_92) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(cnfTransformation, [status(thm)], [f_61])).
% 16.68/7.53  tff(c_1733, plain, (![B_170, A_171]: (k2_relat_1(B_170)=k1_relat_1(A_171) | ~r1_tarski(k2_relat_1(B_170), k1_relat_1(A_171)) | ~v2_funct_1(A_171) | k2_relat_1(k5_relat_1(B_170, A_171))!=k2_relat_1(A_171) | ~v1_funct_1(B_170) | ~v1_relat_1(B_170) | ~v1_funct_1(A_171) | ~v1_relat_1(A_171))), inference(resolution, [status(thm)], [c_262, c_2])).
% 16.68/7.53  tff(c_14872, plain, (![B_770, A_771]: (k2_relat_1(B_770)=k1_relat_1(A_771) | ~v2_funct_1(A_771) | k2_relat_1(k5_relat_1(B_770, A_771))!=k2_relat_1(A_771) | ~v1_funct_1(B_770) | ~v1_funct_1(A_771) | ~v1_relat_1(A_771) | ~v5_relat_1(B_770, k1_relat_1(A_771)) | ~v1_relat_1(B_770))), inference(resolution, [status(thm)], [c_12, c_1733])).
% 16.68/7.53  tff(c_14886, plain, (![B_770]: (k2_relat_1(B_770)=k1_relat_1('#skF_5') | ~v2_funct_1('#skF_5') | k2_relat_1(k5_relat_1(B_770, '#skF_5'))!=k2_relat_1('#skF_5') | ~v1_funct_1(B_770) | ~v1_funct_1('#skF_5') | ~v1_relat_1('#skF_5') | ~v5_relat_1(B_770, '#skF_2') | ~v1_relat_1(B_770))), inference(superposition, [status(thm), theory('equality')], [c_258, c_14872])).
% 16.68/7.53  tff(c_20053, plain, (![B_968]: (k2_relat_1(B_968)='#skF_2' | k2_relat_1(k5_relat_1(B_968, '#skF_5'))!='#skF_3' | ~v1_funct_1(B_968) | ~v5_relat_1(B_968, '#skF_2') | ~v1_relat_1(B_968))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_62, c_2282, c_54, c_258, c_14886])).
% 16.68/7.53  tff(c_20056, plain, (k2_relat_1('#skF_4')='#skF_2' | ~v1_funct_1('#skF_4') | ~v5_relat_1('#skF_4', '#skF_2') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_910, c_20053])).
% 16.68/7.53  tff(c_20059, plain, (k2_relat_1('#skF_4')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_91, c_117, c_68, c_20056])).
% 16.68/7.53  tff(c_20061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_185, c_20059])).
% 16.68/7.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 16.68/7.53  
% 16.68/7.53  Inference rules
% 16.68/7.53  ----------------------
% 16.68/7.53  #Ref     : 0
% 16.68/7.53  #Sup     : 4926
% 16.68/7.53  #Fact    : 0
% 16.68/7.53  #Define  : 0
% 16.68/7.53  #Split   : 30
% 16.68/7.53  #Chain   : 0
% 16.68/7.53  #Close   : 0
% 16.68/7.53  
% 16.68/7.53  Ordering : KBO
% 16.68/7.53  
% 16.68/7.53  Simplification rules
% 16.68/7.53  ----------------------
% 16.68/7.53  #Subsume      : 442
% 16.68/7.53  #Demod        : 6208
% 16.68/7.53  #Tautology    : 1319
% 16.68/7.53  #SimpNegUnit  : 334
% 16.68/7.53  #BackRed      : 456
% 16.68/7.53  
% 16.68/7.53  #Partial instantiations: 0
% 16.68/7.53  #Strategies tried      : 1
% 16.68/7.53  
% 16.68/7.53  Timing (in seconds)
% 16.68/7.53  ----------------------
% 16.68/7.54  Preprocessing        : 0.38
% 16.68/7.54  Parsing              : 0.20
% 16.68/7.54  CNF conversion       : 0.02
% 16.68/7.54  Main loop            : 6.33
% 16.68/7.54  Inferencing          : 1.50
% 16.68/7.54  Reduction            : 2.99
% 16.68/7.54  Demodulation         : 2.40
% 16.68/7.54  BG Simplification    : 0.13
% 16.68/7.54  Subsumption          : 1.23
% 16.68/7.54  Abstraction          : 0.22
% 16.68/7.54  MUC search           : 0.00
% 16.68/7.54  Cooper               : 0.00
% 16.68/7.54  Total                : 6.75
% 16.68/7.54  Index Insertion      : 0.00
% 16.68/7.54  Index Deletion       : 0.00
% 16.68/7.54  Index Matching       : 0.00
% 16.68/7.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------
