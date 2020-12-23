%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:11:54 EST 2020

% Result     : Theorem 4.48s
% Output     : CNFRefutation 4.86s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 175 expanded)
%              Number of leaves         :   38 (  76 expanded)
%              Depth                    :    8
%              Number of atoms          :  148 ( 442 expanded)
%              Number of equality atoms :   37 (  92 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

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

tff(v1_funct_2,type,(
    v1_funct_2: ( $i * $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_partfun1,type,(
    k6_partfun1: $i > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(v1_relat_1,type,(
    v1_relat_1: $i > $o )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff(k6_relat_1,type,(
    k6_relat_1: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_115,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( r2_relset_1(B,B,k1_partfun1(B,A,A,B,D,C),k6_partfun1(B))
             => k2_relset_1(A,B,C) = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

tff(f_69,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_44,axiom,(
    ! [A,B] : v1_relat_1(k2_zfmisc_1(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

tff(f_42,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( m1_subset_1(B,k1_zfmisc_1(A))
         => v1_relat_1(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

tff(f_59,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => m1_subset_1(k2_relset_1(A,B,C),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_relset_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( m1_subset_1(A,k1_zfmisc_1(B))
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

tff(f_97,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_55,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_75,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k4_relset_1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k4_relset_1)).

tff(f_65,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => m1_subset_1(k4_relset_1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k4_relset_1)).

tff(f_95,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_85,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_83,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_51,axiom,(
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

tff(c_50,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_233,plain,(
    ! [A_80,B_81,C_82] :
      ( k2_relset_1(A_80,B_81,C_82) = k2_relat_1(C_82)
      | ~ m1_subset_1(C_82,k1_zfmisc_1(k2_zfmisc_1(A_80,B_81))) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_250,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_50,c_233])).

tff(c_40,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_261,plain,(
    k2_relat_1('#skF_3') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_250,c_40])).

tff(c_14,plain,(
    ! [A_8,B_9] : v1_relat_1(k2_zfmisc_1(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_44,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_124,plain,(
    ! [B_59,A_60] :
      ( v1_relat_1(B_59)
      | ~ m1_subset_1(B_59,k1_zfmisc_1(A_60))
      | ~ v1_relat_1(A_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_136,plain,
    ( v1_relat_1('#skF_4')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_2','#skF_1')) ),
    inference(resolution,[status(thm)],[c_44,c_124])).

tff(c_146,plain,(
    v1_relat_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_136])).

tff(c_133,plain,
    ( v1_relat_1('#skF_3')
    | ~ v1_relat_1(k2_zfmisc_1('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_50,c_124])).

tff(c_143,plain,(
    v1_relat_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_133])).

tff(c_296,plain,(
    ! [A_87,B_88,C_89] :
      ( m1_subset_1(k2_relset_1(A_87,B_88,C_89),k1_zfmisc_1(B_88))
      | ~ m1_subset_1(C_89,k1_zfmisc_1(k2_zfmisc_1(A_87,B_88))) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_315,plain,
    ( m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_250,c_296])).

tff(c_326,plain,(
    m1_subset_1(k2_relat_1('#skF_3'),k1_zfmisc_1('#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_315])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r1_tarski(A_3,B_4)
      | ~ m1_subset_1(A_3,k1_zfmisc_1(B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_371,plain,(
    r1_tarski(k2_relat_1('#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_326,c_8])).

tff(c_38,plain,(
    ! [A_43] : k6_relat_1(A_43) = k6_partfun1(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_97])).

tff(c_20,plain,(
    ! [A_13] : k2_relat_1(k6_relat_1(A_13)) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_56,plain,(
    ! [A_13] : k2_relat_1(k6_partfun1(A_13)) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_20])).

tff(c_48,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_464,plain,(
    ! [C_105,B_102,F_104,E_106,D_101,A_103] :
      ( k4_relset_1(A_103,B_102,C_105,D_101,E_106,F_104) = k5_relat_1(E_106,F_104)
      | ~ m1_subset_1(F_104,k1_zfmisc_1(k2_zfmisc_1(C_105,D_101)))
      | ~ m1_subset_1(E_106,k1_zfmisc_1(k2_zfmisc_1(A_103,B_102))) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_682,plain,(
    ! [A_126,B_127,E_128] :
      ( k4_relset_1(A_126,B_127,'#skF_1','#skF_2',E_128,'#skF_3') = k5_relat_1(E_128,'#skF_3')
      | ~ m1_subset_1(E_128,k1_zfmisc_1(k2_zfmisc_1(A_126,B_127))) ) ),
    inference(resolution,[status(thm)],[c_50,c_464])).

tff(c_722,plain,(
    k4_relset_1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_44,c_682])).

tff(c_24,plain,(
    ! [E_21,D_20,C_19,B_18,A_17,F_22] :
      ( m1_subset_1(k4_relset_1(A_17,B_18,C_19,D_20,E_21,F_22),k1_zfmisc_1(k2_zfmisc_1(A_17,D_20)))
      | ~ m1_subset_1(F_22,k1_zfmisc_1(k2_zfmisc_1(C_19,D_20)))
      | ~ m1_subset_1(E_21,k1_zfmisc_1(k2_zfmisc_1(A_17,B_18))) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_917,plain,
    ( m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_722,c_24])).

tff(c_921,plain,(
    m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_50,c_917])).

tff(c_54,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_784,plain,(
    ! [E_133,F_131,D_132,C_134,B_130,A_129] :
      ( k1_partfun1(A_129,B_130,C_134,D_132,E_133,F_131) = k5_relat_1(E_133,F_131)
      | ~ m1_subset_1(F_131,k1_zfmisc_1(k2_zfmisc_1(C_134,D_132)))
      | ~ v1_funct_1(F_131)
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_133) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_806,plain,(
    ! [A_129,B_130,E_133] :
      ( k1_partfun1(A_129,B_130,'#skF_1','#skF_2',E_133,'#skF_3') = k5_relat_1(E_133,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_133,k1_zfmisc_1(k2_zfmisc_1(A_129,B_130)))
      | ~ v1_funct_1(E_133) ) ),
    inference(resolution,[status(thm)],[c_50,c_784])).

tff(c_1277,plain,(
    ! [A_152,B_153,E_154] :
      ( k1_partfun1(A_152,B_153,'#skF_1','#skF_2',E_154,'#skF_3') = k5_relat_1(E_154,'#skF_3')
      | ~ m1_subset_1(E_154,k1_zfmisc_1(k2_zfmisc_1(A_152,B_153)))
      | ~ v1_funct_1(E_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_806])).

tff(c_1323,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_1277])).

tff(c_1341,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1323])).

tff(c_34,plain,(
    ! [A_36] : m1_subset_1(k6_relat_1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_55,plain,(
    ! [A_36] : m1_subset_1(k6_partfun1(A_36),k1_zfmisc_1(k2_zfmisc_1(A_36,A_36))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_34])).

tff(c_42,plain,(
    r2_relset_1('#skF_2','#skF_2',k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k6_partfun1('#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_115])).

tff(c_383,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_393,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k6_partfun1('#skF_2'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2')))
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_42,c_383])).

tff(c_412,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2')
    | ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_55,c_393])).

tff(c_413,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_412])).

tff(c_1355,plain,(
    ~ m1_subset_1(k5_relat_1('#skF_4','#skF_3'),k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1341,c_413])).

tff(c_1359,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_921,c_1355])).

tff(c_1360,plain,(
    k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(splitRight,[status(thm)],[c_412])).

tff(c_1702,plain,(
    ! [F_188,E_190,D_189,A_186,C_191,B_187] :
      ( k1_partfun1(A_186,B_187,C_191,D_189,E_190,F_188) = k5_relat_1(E_190,F_188)
      | ~ m1_subset_1(F_188,k1_zfmisc_1(k2_zfmisc_1(C_191,D_189)))
      | ~ v1_funct_1(F_188)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_1(E_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_1724,plain,(
    ! [A_186,B_187,E_190] :
      ( k1_partfun1(A_186,B_187,'#skF_1','#skF_2',E_190,'#skF_3') = k5_relat_1(E_190,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_186,B_187)))
      | ~ v1_funct_1(E_190) ) ),
    inference(resolution,[status(thm)],[c_50,c_1702])).

tff(c_2467,plain,(
    ! [A_223,B_224,E_225] :
      ( k1_partfun1(A_223,B_224,'#skF_1','#skF_2',E_225,'#skF_3') = k5_relat_1(E_225,'#skF_3')
      | ~ m1_subset_1(E_225,k1_zfmisc_1(k2_zfmisc_1(A_223,B_224)))
      | ~ v1_funct_1(E_225) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1724])).

tff(c_2519,plain,
    ( k1_partfun1('#skF_2','#skF_1','#skF_1','#skF_2','#skF_4','#skF_3') = k5_relat_1('#skF_4','#skF_3')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_44,c_2467])).

tff(c_2539,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_1360,c_2519])).

tff(c_206,plain,(
    ! [A_73,B_74] :
      ( r1_tarski(k2_relat_1(k5_relat_1(A_73,B_74)),k2_relat_1(B_74))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( B_2 = A_1
      | ~ r1_tarski(B_2,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_216,plain,(
    ! [A_73,B_74] :
      ( k2_relat_1(k5_relat_1(A_73,B_74)) = k2_relat_1(B_74)
      | ~ r1_tarski(k2_relat_1(B_74),k2_relat_1(k5_relat_1(A_73,B_74)))
      | ~ v1_relat_1(B_74)
      | ~ v1_relat_1(A_73) ) ),
    inference(resolution,[status(thm)],[c_206,c_2])).

tff(c_2558,plain,
    ( k2_relat_1(k5_relat_1('#skF_4','#skF_3')) = k2_relat_1('#skF_3')
    | ~ r1_tarski(k2_relat_1('#skF_3'),k2_relat_1(k6_partfun1('#skF_2')))
    | ~ v1_relat_1('#skF_3')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2539,c_216])).

tff(c_2565,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_146,c_143,c_371,c_56,c_56,c_2539,c_2558])).

tff(c_2567,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_261,c_2565])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:28:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.48/1.85  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.86  
% 4.48/1.86  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.48/1.86  %$ r2_relset_1 > v1_funct_2 > r1_tarski > m1_subset_1 > v1_relat_1 > v1_funct_1 > k4_relset_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k1_zfmisc_1 > k1_relat_1 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 4.48/1.86  
% 4.48/1.86  %Foreground sorts:
% 4.48/1.86  
% 4.48/1.86  
% 4.48/1.86  %Background operators:
% 4.48/1.86  
% 4.48/1.86  
% 4.48/1.86  %Foreground operators:
% 4.48/1.86  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 4.48/1.86  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 4.48/1.86  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.48/1.86  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 4.48/1.86  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 4.48/1.86  tff(k4_relset_1, type, k4_relset_1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.48/1.86  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.48/1.86  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 4.48/1.86  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.48/1.86  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 4.48/1.86  tff('#skF_2', type, '#skF_2': $i).
% 4.48/1.86  tff('#skF_3', type, '#skF_3': $i).
% 4.48/1.86  tff('#skF_1', type, '#skF_1': $i).
% 4.48/1.86  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 4.48/1.86  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 4.48/1.86  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.48/1.86  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 4.48/1.86  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 4.48/1.86  tff('#skF_4', type, '#skF_4': $i).
% 4.48/1.86  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 4.48/1.86  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.48/1.86  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 4.48/1.86  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 4.48/1.86  
% 4.86/1.88  tff(f_115, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 4.86/1.88  tff(f_69, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 4.86/1.88  tff(f_44, axiom, (![A, B]: v1_relat_1(k2_zfmisc_1(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc6_relat_1)).
% 4.86/1.88  tff(f_42, axiom, (![A]: (v1_relat_1(A) => (![B]: (m1_subset_1(B, k1_zfmisc_1(A)) => v1_relat_1(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relat_1)).
% 4.86/1.88  tff(f_59, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => m1_subset_1(k2_relset_1(A, B, C), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_relset_1)).
% 4.86/1.88  tff(f_35, axiom, (![A, B]: (m1_subset_1(A, k1_zfmisc_1(B)) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_subset)).
% 4.86/1.88  tff(f_97, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 4.86/1.88  tff(f_55, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 4.86/1.88  tff(f_75, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k4_relset_1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k4_relset_1)).
% 4.86/1.88  tff(f_65, axiom, (![A, B, C, D, E, F]: ((m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => m1_subset_1(k4_relset_1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k4_relset_1)).
% 4.86/1.88  tff(f_95, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 4.86/1.88  tff(f_85, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 4.86/1.88  tff(f_83, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 4.86/1.88  tff(f_51, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => r1_tarski(k2_relat_1(k5_relat_1(A, B)), k2_relat_1(B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_relat_1)).
% 4.86/1.88  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.86/1.88  tff(c_50, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.86/1.88  tff(c_233, plain, (![A_80, B_81, C_82]: (k2_relset_1(A_80, B_81, C_82)=k2_relat_1(C_82) | ~m1_subset_1(C_82, k1_zfmisc_1(k2_zfmisc_1(A_80, B_81))))), inference(cnfTransformation, [status(thm)], [f_69])).
% 4.86/1.88  tff(c_250, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_50, c_233])).
% 4.86/1.88  tff(c_40, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.86/1.88  tff(c_261, plain, (k2_relat_1('#skF_3')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_250, c_40])).
% 4.86/1.88  tff(c_14, plain, (![A_8, B_9]: (v1_relat_1(k2_zfmisc_1(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 4.86/1.88  tff(c_44, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.86/1.88  tff(c_124, plain, (![B_59, A_60]: (v1_relat_1(B_59) | ~m1_subset_1(B_59, k1_zfmisc_1(A_60)) | ~v1_relat_1(A_60))), inference(cnfTransformation, [status(thm)], [f_42])).
% 4.86/1.88  tff(c_136, plain, (v1_relat_1('#skF_4') | ~v1_relat_1(k2_zfmisc_1('#skF_2', '#skF_1'))), inference(resolution, [status(thm)], [c_44, c_124])).
% 4.86/1.88  tff(c_146, plain, (v1_relat_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_136])).
% 4.86/1.88  tff(c_133, plain, (v1_relat_1('#skF_3') | ~v1_relat_1(k2_zfmisc_1('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_50, c_124])).
% 4.86/1.88  tff(c_143, plain, (v1_relat_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_133])).
% 4.86/1.88  tff(c_296, plain, (![A_87, B_88, C_89]: (m1_subset_1(k2_relset_1(A_87, B_88, C_89), k1_zfmisc_1(B_88)) | ~m1_subset_1(C_89, k1_zfmisc_1(k2_zfmisc_1(A_87, B_88))))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.86/1.88  tff(c_315, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_250, c_296])).
% 4.86/1.88  tff(c_326, plain, (m1_subset_1(k2_relat_1('#skF_3'), k1_zfmisc_1('#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_315])).
% 4.86/1.88  tff(c_8, plain, (![A_3, B_4]: (r1_tarski(A_3, B_4) | ~m1_subset_1(A_3, k1_zfmisc_1(B_4)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.86/1.88  tff(c_371, plain, (r1_tarski(k2_relat_1('#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_326, c_8])).
% 4.86/1.88  tff(c_38, plain, (![A_43]: (k6_relat_1(A_43)=k6_partfun1(A_43))), inference(cnfTransformation, [status(thm)], [f_97])).
% 4.86/1.88  tff(c_20, plain, (![A_13]: (k2_relat_1(k6_relat_1(A_13))=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.86/1.88  tff(c_56, plain, (![A_13]: (k2_relat_1(k6_partfun1(A_13))=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_38, c_20])).
% 4.86/1.88  tff(c_48, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.86/1.88  tff(c_464, plain, (![C_105, B_102, F_104, E_106, D_101, A_103]: (k4_relset_1(A_103, B_102, C_105, D_101, E_106, F_104)=k5_relat_1(E_106, F_104) | ~m1_subset_1(F_104, k1_zfmisc_1(k2_zfmisc_1(C_105, D_101))) | ~m1_subset_1(E_106, k1_zfmisc_1(k2_zfmisc_1(A_103, B_102))))), inference(cnfTransformation, [status(thm)], [f_75])).
% 4.86/1.88  tff(c_682, plain, (![A_126, B_127, E_128]: (k4_relset_1(A_126, B_127, '#skF_1', '#skF_2', E_128, '#skF_3')=k5_relat_1(E_128, '#skF_3') | ~m1_subset_1(E_128, k1_zfmisc_1(k2_zfmisc_1(A_126, B_127))))), inference(resolution, [status(thm)], [c_50, c_464])).
% 4.86/1.88  tff(c_722, plain, (k4_relset_1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_44, c_682])).
% 4.86/1.88  tff(c_24, plain, (![E_21, D_20, C_19, B_18, A_17, F_22]: (m1_subset_1(k4_relset_1(A_17, B_18, C_19, D_20, E_21, F_22), k1_zfmisc_1(k2_zfmisc_1(A_17, D_20))) | ~m1_subset_1(F_22, k1_zfmisc_1(k2_zfmisc_1(C_19, D_20))) | ~m1_subset_1(E_21, k1_zfmisc_1(k2_zfmisc_1(A_17, B_18))))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.86/1.88  tff(c_917, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_722, c_24])).
% 4.86/1.88  tff(c_921, plain, (m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_50, c_917])).
% 4.86/1.88  tff(c_54, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.86/1.88  tff(c_784, plain, (![E_133, F_131, D_132, C_134, B_130, A_129]: (k1_partfun1(A_129, B_130, C_134, D_132, E_133, F_131)=k5_relat_1(E_133, F_131) | ~m1_subset_1(F_131, k1_zfmisc_1(k2_zfmisc_1(C_134, D_132))) | ~v1_funct_1(F_131) | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_133))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.86/1.88  tff(c_806, plain, (![A_129, B_130, E_133]: (k1_partfun1(A_129, B_130, '#skF_1', '#skF_2', E_133, '#skF_3')=k5_relat_1(E_133, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_133, k1_zfmisc_1(k2_zfmisc_1(A_129, B_130))) | ~v1_funct_1(E_133))), inference(resolution, [status(thm)], [c_50, c_784])).
% 4.86/1.88  tff(c_1277, plain, (![A_152, B_153, E_154]: (k1_partfun1(A_152, B_153, '#skF_1', '#skF_2', E_154, '#skF_3')=k5_relat_1(E_154, '#skF_3') | ~m1_subset_1(E_154, k1_zfmisc_1(k2_zfmisc_1(A_152, B_153))) | ~v1_funct_1(E_154))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_806])).
% 4.86/1.88  tff(c_1323, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_1277])).
% 4.86/1.88  tff(c_1341, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1323])).
% 4.86/1.88  tff(c_34, plain, (![A_36]: (m1_subset_1(k6_relat_1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.86/1.88  tff(c_55, plain, (![A_36]: (m1_subset_1(k6_partfun1(A_36), k1_zfmisc_1(k2_zfmisc_1(A_36, A_36))))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_34])).
% 4.86/1.88  tff(c_42, plain, (r2_relset_1('#skF_2', '#skF_2', k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k6_partfun1('#skF_2'))), inference(cnfTransformation, [status(thm)], [f_115])).
% 4.86/1.88  tff(c_383, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.86/1.88  tff(c_393, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k6_partfun1('#skF_2'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2'))) | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(resolution, [status(thm)], [c_42, c_383])).
% 4.86/1.88  tff(c_412, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2') | ~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_55, c_393])).
% 4.86/1.88  tff(c_413, plain, (~m1_subset_1(k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(splitLeft, [status(thm)], [c_412])).
% 4.86/1.88  tff(c_1355, plain, (~m1_subset_1(k5_relat_1('#skF_4', '#skF_3'), k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_1341, c_413])).
% 4.86/1.88  tff(c_1359, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_921, c_1355])).
% 4.86/1.88  tff(c_1360, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(splitRight, [status(thm)], [c_412])).
% 4.86/1.88  tff(c_1702, plain, (![F_188, E_190, D_189, A_186, C_191, B_187]: (k1_partfun1(A_186, B_187, C_191, D_189, E_190, F_188)=k5_relat_1(E_190, F_188) | ~m1_subset_1(F_188, k1_zfmisc_1(k2_zfmisc_1(C_191, D_189))) | ~v1_funct_1(F_188) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_1(E_190))), inference(cnfTransformation, [status(thm)], [f_95])).
% 4.86/1.88  tff(c_1724, plain, (![A_186, B_187, E_190]: (k1_partfun1(A_186, B_187, '#skF_1', '#skF_2', E_190, '#skF_3')=k5_relat_1(E_190, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_186, B_187))) | ~v1_funct_1(E_190))), inference(resolution, [status(thm)], [c_50, c_1702])).
% 4.86/1.88  tff(c_2467, plain, (![A_223, B_224, E_225]: (k1_partfun1(A_223, B_224, '#skF_1', '#skF_2', E_225, '#skF_3')=k5_relat_1(E_225, '#skF_3') | ~m1_subset_1(E_225, k1_zfmisc_1(k2_zfmisc_1(A_223, B_224))) | ~v1_funct_1(E_225))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1724])).
% 4.86/1.88  tff(c_2519, plain, (k1_partfun1('#skF_2', '#skF_1', '#skF_1', '#skF_2', '#skF_4', '#skF_3')=k5_relat_1('#skF_4', '#skF_3') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_44, c_2467])).
% 4.86/1.88  tff(c_2539, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_48, c_1360, c_2519])).
% 4.86/1.88  tff(c_206, plain, (![A_73, B_74]: (r1_tarski(k2_relat_1(k5_relat_1(A_73, B_74)), k2_relat_1(B_74)) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.86/1.88  tff(c_2, plain, (![B_2, A_1]: (B_2=A_1 | ~r1_tarski(B_2, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.86/1.88  tff(c_216, plain, (![A_73, B_74]: (k2_relat_1(k5_relat_1(A_73, B_74))=k2_relat_1(B_74) | ~r1_tarski(k2_relat_1(B_74), k2_relat_1(k5_relat_1(A_73, B_74))) | ~v1_relat_1(B_74) | ~v1_relat_1(A_73))), inference(resolution, [status(thm)], [c_206, c_2])).
% 4.86/1.88  tff(c_2558, plain, (k2_relat_1(k5_relat_1('#skF_4', '#skF_3'))=k2_relat_1('#skF_3') | ~r1_tarski(k2_relat_1('#skF_3'), k2_relat_1(k6_partfun1('#skF_2'))) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2539, c_216])).
% 4.86/1.88  tff(c_2565, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_146, c_143, c_371, c_56, c_56, c_2539, c_2558])).
% 4.86/1.88  tff(c_2567, plain, $false, inference(negUnitSimplification, [status(thm)], [c_261, c_2565])).
% 4.86/1.88  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.86/1.88  
% 4.86/1.88  Inference rules
% 4.86/1.88  ----------------------
% 4.86/1.88  #Ref     : 0
% 4.86/1.88  #Sup     : 593
% 4.86/1.88  #Fact    : 0
% 4.86/1.88  #Define  : 0
% 4.86/1.88  #Split   : 7
% 4.86/1.88  #Chain   : 0
% 4.86/1.88  #Close   : 0
% 4.86/1.88  
% 4.86/1.88  Ordering : KBO
% 4.86/1.88  
% 4.86/1.88  Simplification rules
% 4.86/1.88  ----------------------
% 4.86/1.88  #Subsume      : 42
% 4.86/1.88  #Demod        : 224
% 4.86/1.88  #Tautology    : 144
% 4.86/1.88  #SimpNegUnit  : 2
% 4.86/1.88  #BackRed      : 16
% 4.86/1.88  
% 4.86/1.88  #Partial instantiations: 0
% 4.86/1.88  #Strategies tried      : 1
% 4.86/1.88  
% 4.86/1.88  Timing (in seconds)
% 4.86/1.88  ----------------------
% 4.86/1.88  Preprocessing        : 0.33
% 4.86/1.88  Parsing              : 0.18
% 4.86/1.88  CNF conversion       : 0.02
% 4.86/1.88  Main loop            : 0.77
% 4.86/1.88  Inferencing          : 0.28
% 4.86/1.88  Reduction            : 0.26
% 4.86/1.88  Demodulation         : 0.19
% 4.86/1.88  BG Simplification    : 0.03
% 4.86/1.88  Subsumption          : 0.13
% 4.86/1.89  Abstraction          : 0.05
% 4.86/1.89  MUC search           : 0.00
% 4.86/1.89  Cooper               : 0.00
% 4.86/1.89  Total                : 1.14
% 4.86/1.89  Index Insertion      : 0.00
% 4.86/1.89  Index Deletion       : 0.00
% 4.86/1.89  Index Matching       : 0.00
% 4.86/1.89  BG Taut test         : 0.00
%------------------------------------------------------------------------------
