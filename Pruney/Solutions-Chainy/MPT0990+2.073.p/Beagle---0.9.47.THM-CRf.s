%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:13:06 EST 2020

% Result     : Theorem 7.71s
% Output     : CNFRefutation 8.03s
% Verified   : 
% Statistics : Number of formulae       :  162 (1190 expanded)
%              Number of leaves         :   44 ( 439 expanded)
%              Depth                    :   17
%              Number of atoms          :  367 (4249 expanded)
%              Number of equality atoms :  124 (1530 expanded)
%              Maximal formula depth    :   16 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(k2_relset_1,type,(
    k2_relset_1: ( $i * $i * $i ) > $i )).

tff(v1_funct_1,type,(
    v1_funct_1: $i > $o )).

tff(k2_funct_1,type,(
    k2_funct_1: $i > $i )).

tff(v2_funct_1,type,(
    v2_funct_1: $i > $o )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_relset_1,type,(
    r2_relset_1: ( $i * $i * $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_relat_1,type,(
    k5_relat_1: ( $i * $i ) > $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k1_partfun1,type,(
    k1_partfun1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(f_208,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( v1_funct_1(C)
          & v1_funct_2(C,A,B)
          & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
       => ! [D] :
            ( ( v1_funct_1(D)
              & v1_funct_2(D,B,A)
              & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(B,A))) )
           => ( ( k2_relset_1(A,B,C) = B
                & r2_relset_1(A,A,k1_partfun1(A,B,B,A,C,D),k6_partfun1(A))
                & v2_funct_1(C) )
             => ( A = k1_xboole_0
                | B = k1_xboole_0
                | D = k2_funct_1(C) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_55,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_123,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_59,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_39,axiom,(
    ! [A] :
      ( k1_relat_1(k6_relat_1(A)) = A
      & k2_relat_1(k6_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

tff(f_43,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(k6_relat_1(k1_relat_1(A)),A) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

tff(f_79,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_87,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_47,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k5_relat_1(A,k6_relat_1(k2_relat_1(A))) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

tff(f_35,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_182,axiom,(
    ! [A,B,C] :
      ( ( v1_funct_1(C)
        & v1_funct_2(C,A,B)
        & m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( ( k2_relset_1(A,B,C) = B
          & v2_funct_1(C) )
       => ( B = k1_xboole_0
          | ( k5_relat_1(C,k2_funct_1(C)) = k6_partfun1(A)
            & k5_relat_1(k2_funct_1(C),C) = k6_partfun1(B) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

tff(f_111,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_95,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_107,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_140,axiom,(
    ! [A,B,C] :
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

tff(f_166,axiom,(
    ! [A,B,C,D] :
      ( ( v1_funct_1(D)
        & v1_funct_2(D,A,B)
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ! [E] :
          ( ( v1_funct_1(E)
            & v1_funct_2(E,B,C)
            & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(B,C))) )
         => ( ( v2_funct_1(k1_partfun1(A,B,B,C,D,E))
              & k2_relset_1(A,B,D) = B )
           => ( ( C = k1_xboole_0
                & B != k1_xboole_0 )
              | ( v2_funct_1(D)
                & v2_funct_1(E) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

tff(f_69,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k2_relat_1(A) = k1_relat_1(k2_funct_1(A))
          & k1_relat_1(A) = k2_relat_1(k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

tff(f_121,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(c_62,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_80,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_167,plain,(
    ! [C_66,A_67,B_68] :
      ( v1_relat_1(C_66)
      | ~ m1_subset_1(C_66,k1_zfmisc_1(k2_zfmisc_1(A_67,B_68))) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_179,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_167])).

tff(c_84,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_14,plain,(
    ! [A_11] :
      ( v1_relat_1(k2_funct_1(A_11))
      | ~ v1_funct_1(A_11)
      | ~ v1_relat_1(A_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_68,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_46,plain,(
    ! [A_38] : k6_relat_1(A_38) = k6_partfun1(A_38) ),
    inference(cnfTransformation,[status(thm)],[f_123])).

tff(c_16,plain,(
    ! [A_12] : v1_relat_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_88,plain,(
    ! [A_12] : v1_relat_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_16])).

tff(c_4,plain,(
    ! [A_8] : k1_relat_1(k6_relat_1(A_8)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_92,plain,(
    ! [A_8] : k1_relat_1(k6_partfun1(A_8)) = A_8 ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_4])).

tff(c_8,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_130,plain,(
    ! [A_63] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_63)),A_63) = A_63
      | ~ v1_relat_1(A_63) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_139,plain,(
    ! [A_8] :
      ( k5_relat_1(k6_partfun1(A_8),k6_partfun1(A_8)) = k6_partfun1(A_8)
      | ~ v1_relat_1(k6_partfun1(A_8)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_92,c_130])).

tff(c_143,plain,(
    ! [A_8] : k5_relat_1(k6_partfun1(A_8),k6_partfun1(A_8)) = k6_partfun1(A_8) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_139])).

tff(c_26,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k2_funct_1(A_14)) = k6_relat_1(k1_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_85,plain,(
    ! [A_14] :
      ( k5_relat_1(A_14,k2_funct_1(A_14)) = k6_partfun1(k1_relat_1(A_14))
      | ~ v2_funct_1(A_14)
      | ~ v1_funct_1(A_14)
      | ~ v1_relat_1(A_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_26])).

tff(c_72,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_216,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_222,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_216])).

tff(c_229,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_222])).

tff(c_10,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_relat_1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_89,plain,(
    ! [A_10] :
      ( k5_relat_1(A_10,k6_partfun1(k2_relat_1(A_10))) = A_10
      | ~ v1_relat_1(A_10) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_10])).

tff(c_234,plain,
    ( k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_89])).

tff(c_238,plain,(
    k5_relat_1('#skF_3',k6_partfun1('#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_234])).

tff(c_90,plain,(
    ! [A_9] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),A_9) = A_9
      | ~ v1_relat_1(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_8])).

tff(c_266,plain,(
    ! [A_80,B_81,C_82] :
      ( k5_relat_1(k5_relat_1(A_80,B_81),C_82) = k5_relat_1(A_80,k5_relat_1(B_81,C_82))
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(B_81)
      | ~ v1_relat_1(A_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_301,plain,(
    ! [A_9,C_82] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_9)),k5_relat_1(A_9,C_82)) = k5_relat_1(A_9,C_82)
      | ~ v1_relat_1(C_82)
      | ~ v1_relat_1(A_9)
      | ~ v1_relat_1(k6_partfun1(k1_relat_1(A_9)))
      | ~ v1_relat_1(A_9) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_266])).

tff(c_4715,plain,(
    ! [A_275,C_276] :
      ( k5_relat_1(k6_partfun1(k1_relat_1(A_275)),k5_relat_1(A_275,C_276)) = k5_relat_1(A_275,C_276)
      | ~ v1_relat_1(C_276)
      | ~ v1_relat_1(A_275) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_301])).

tff(c_4760,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = k5_relat_1('#skF_3',k6_partfun1('#skF_2'))
    | ~ v1_relat_1(k6_partfun1('#skF_2'))
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_4715])).

tff(c_4802,plain,(
    k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_88,c_238,c_4760])).

tff(c_2,plain,(
    ! [A_1,B_5,C_7] :
      ( k5_relat_1(k5_relat_1(A_1,B_5),C_7) = k5_relat_1(A_1,k5_relat_1(B_5,C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1(B_5)
      | ~ v1_relat_1(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_5488,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_7)) = k5_relat_1('#skF_3',C_7)
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4802,c_2])).

tff(c_5565,plain,(
    ! [C_312] :
      ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k5_relat_1('#skF_3',C_312)) = k5_relat_1('#skF_3',C_312)
      | ~ v1_relat_1(C_312) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_88,c_179,c_5488])).

tff(c_5603,plain,
    ( k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')),k6_partfun1(k1_relat_1('#skF_3'))) = k5_relat_1('#skF_3',k2_funct_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_85,c_5565])).

tff(c_5632,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3'))
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_84,c_68,c_143,c_5603])).

tff(c_5637,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_5632])).

tff(c_5640,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_14,c_5637])).

tff(c_5644,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_84,c_5640])).

tff(c_5646,plain,(
    v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5632])).

tff(c_74,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_180,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_167])).

tff(c_66,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_78,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_76,plain,(
    v1_funct_2('#skF_4','#skF_2','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_230,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = k2_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_216])).

tff(c_5906,plain,(
    ! [B_332,C_333,A_334] :
      ( k6_partfun1(B_332) = k5_relat_1(k2_funct_1(C_333),C_333)
      | k1_xboole_0 = B_332
      | ~ v2_funct_1(C_333)
      | k2_relset_1(A_334,B_332,C_333) != B_332
      | ~ m1_subset_1(C_333,k1_zfmisc_1(k2_zfmisc_1(A_334,B_332)))
      | ~ v1_funct_2(C_333,A_334,B_332)
      | ~ v1_funct_1(C_333) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_5912,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_5906])).

tff(c_5922,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_230,c_5912])).

tff(c_5923,plain,
    ( k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1')
    | ~ v2_funct_1('#skF_4')
    | k2_relat_1('#skF_4') != '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_5922])).

tff(c_5974,plain,(
    k2_relat_1('#skF_4') != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_5923])).

tff(c_82,plain,(
    v1_funct_2('#skF_3','#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_42,plain,(
    ! [A_31] : m1_subset_1(k6_partfun1(A_31),k1_zfmisc_1(k2_zfmisc_1(A_31,A_31))) ),
    inference(cnfTransformation,[status(thm)],[f_111])).

tff(c_193,plain,(
    ! [A_70,B_71,D_72] :
      ( r2_relset_1(A_70,B_71,D_72,D_72)
      | ~ m1_subset_1(D_72,k1_zfmisc_1(k2_zfmisc_1(A_70,B_71))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_200,plain,(
    ! [A_31] : r2_relset_1(A_31,A_31,k6_partfun1(A_31),k6_partfun1(A_31)) ),
    inference(resolution,[status(thm)],[c_42,c_193])).

tff(c_5441,plain,(
    ! [F_308,C_307,D_305,B_309,A_306,E_310] :
      ( m1_subset_1(k1_partfun1(A_306,B_309,C_307,D_305,E_310,F_308),k1_zfmisc_1(k2_zfmisc_1(A_306,D_305)))
      | ~ m1_subset_1(F_308,k1_zfmisc_1(k2_zfmisc_1(C_307,D_305)))
      | ~ v1_funct_1(F_308)
      | ~ m1_subset_1(E_310,k1_zfmisc_1(k2_zfmisc_1(A_306,B_309)))
      | ~ v1_funct_1(E_310) ) ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_70,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_4645,plain,(
    ! [D_270,C_271,A_272,B_273] :
      ( D_270 = C_271
      | ~ r2_relset_1(A_272,B_273,C_271,D_270)
      | ~ m1_subset_1(D_270,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273)))
      | ~ m1_subset_1(C_271,k1_zfmisc_1(k2_zfmisc_1(A_272,B_273))) ) ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_4653,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_70,c_4645])).

tff(c_4668,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_4653])).

tff(c_4811,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_4668])).

tff(c_5458,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_5441,c_4811])).

tff(c_5476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_80,c_78,c_74,c_5458])).

tff(c_5477,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_4668])).

tff(c_6749,plain,(
    ! [A_370,B_371,C_372,D_373] :
      ( k2_relset_1(A_370,B_371,C_372) = B_371
      | ~ r2_relset_1(B_371,B_371,k1_partfun1(B_371,A_370,A_370,B_371,D_373,C_372),k6_partfun1(B_371))
      | ~ m1_subset_1(D_373,k1_zfmisc_1(k2_zfmisc_1(B_371,A_370)))
      | ~ v1_funct_2(D_373,B_371,A_370)
      | ~ v1_funct_1(D_373)
      | ~ m1_subset_1(C_372,k1_zfmisc_1(k2_zfmisc_1(A_370,B_371)))
      | ~ v1_funct_2(C_372,A_370,B_371)
      | ~ v1_funct_1(C_372) ) ),
    inference(cnfTransformation,[status(thm)],[f_140])).

tff(c_6755,plain,
    ( k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1'
    | ~ r2_relset_1('#skF_1','#skF_1',k6_partfun1('#skF_1'),k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3')
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_5477,c_6749])).

tff(c_6759,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_74,c_84,c_82,c_80,c_200,c_230,c_6755])).

tff(c_6761,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_5974,c_6759])).

tff(c_6763,plain,(
    k2_relat_1('#skF_4') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_5923])).

tff(c_6768,plain,
    ( k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6763,c_89])).

tff(c_6772,plain,(
    k5_relat_1('#skF_4',k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_6768])).

tff(c_64,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_208])).

tff(c_5645,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1(k1_relat_1('#skF_3')) ),
    inference(splitRight,[status(thm)],[c_5632])).

tff(c_7798,plain,(
    ! [A_413,C_414,B_415] :
      ( k6_partfun1(A_413) = k5_relat_1(C_414,k2_funct_1(C_414))
      | k1_xboole_0 = B_415
      | ~ v2_funct_1(C_414)
      | k2_relset_1(A_413,B_415,C_414) != B_415
      | ~ m1_subset_1(C_414,k1_zfmisc_1(k2_zfmisc_1(A_413,B_415)))
      | ~ v1_funct_2(C_414,A_413,B_415)
      | ~ v1_funct_1(C_414) ) ),
    inference(cnfTransformation,[status(thm)],[f_182])).

tff(c_7802,plain,
    ( k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2'
    | ~ v2_funct_1('#skF_3')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_7798])).

tff(c_7810,plain,
    ( k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1')
    | k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_72,c_68,c_5645,c_7802])).

tff(c_7811,plain,(
    k6_partfun1(k1_relat_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_7810])).

tff(c_7819,plain,(
    k5_relat_1('#skF_3',k2_funct_1('#skF_3')) = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7811,c_5645])).

tff(c_6762,plain,
    ( ~ v2_funct_1('#skF_4')
    | k5_relat_1(k2_funct_1('#skF_4'),'#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_5923])).

tff(c_6792,plain,(
    ~ v2_funct_1('#skF_4') ),
    inference(splitLeft,[status(thm)],[c_6762])).

tff(c_18,plain,(
    ! [A_12] : v2_funct_1(k6_relat_1(A_12)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_87,plain,(
    ! [A_12] : v2_funct_1(k6_partfun1(A_12)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_7639,plain,(
    ! [D_405,C_406,A_409,B_407,E_408] :
      ( k1_xboole_0 = C_406
      | v2_funct_1(E_408)
      | k2_relset_1(A_409,B_407,D_405) != B_407
      | ~ v2_funct_1(k1_partfun1(A_409,B_407,B_407,C_406,D_405,E_408))
      | ~ m1_subset_1(E_408,k1_zfmisc_1(k2_zfmisc_1(B_407,C_406)))
      | ~ v1_funct_2(E_408,B_407,C_406)
      | ~ v1_funct_1(E_408)
      | ~ m1_subset_1(D_405,k1_zfmisc_1(k2_zfmisc_1(A_409,B_407)))
      | ~ v1_funct_2(D_405,A_409,B_407)
      | ~ v1_funct_1(D_405) ) ),
    inference(cnfTransformation,[status(thm)],[f_166])).

tff(c_7641,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4')
    | k2_relset_1('#skF_1','#skF_2','#skF_3') != '#skF_2'
    | ~ v2_funct_1(k6_partfun1('#skF_1'))
    | ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_2('#skF_3','#skF_1','#skF_2')
    | ~ v1_funct_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_5477,c_7639])).

tff(c_7643,plain,
    ( k1_xboole_0 = '#skF_1'
    | v2_funct_1('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_82,c_80,c_78,c_76,c_74,c_87,c_72,c_7641])).

tff(c_7645,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6792,c_66,c_7643])).

tff(c_7647,plain,(
    v2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_6762])).

tff(c_204,plain,(
    ! [A_74] :
      ( k1_relat_1(k2_funct_1(A_74)) = k2_relat_1(A_74)
      | ~ v2_funct_1(A_74)
      | ~ v1_funct_1(A_74)
      | ~ v1_relat_1(A_74) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_8802,plain,(
    ! [A_452] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_452)),k2_funct_1(A_452)) = k2_funct_1(A_452)
      | ~ v1_relat_1(k2_funct_1(A_452))
      | ~ v2_funct_1(A_452)
      | ~ v1_funct_1(A_452)
      | ~ v1_relat_1(A_452) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_90])).

tff(c_8823,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4'))
    | ~ v2_funct_1('#skF_4')
    | ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6763,c_8802])).

tff(c_8842,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_78,c_7647,c_8823])).

tff(c_8876,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_8842])).

tff(c_8879,plain,
    ( ~ v1_funct_1('#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_14,c_8876])).

tff(c_8883,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_78,c_8879])).

tff(c_8885,plain,(
    v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(splitRight,[status(thm)],[c_8842])).

tff(c_6764,plain,(
    k2_relset_1('#skF_2','#skF_1','#skF_4') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_6763,c_230])).

tff(c_7804,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1'
    | ~ v2_funct_1('#skF_4')
    | k2_relset_1('#skF_2','#skF_1','#skF_4') != '#skF_1'
    | ~ v1_funct_2('#skF_4','#skF_2','#skF_1')
    | ~ v1_funct_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_74,c_7798])).

tff(c_7814,plain,
    ( k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2')
    | k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_76,c_6764,c_7647,c_7804])).

tff(c_7815,plain,(
    k5_relat_1('#skF_4',k2_funct_1('#skF_4')) = k6_partfun1('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_66,c_7814])).

tff(c_8884,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),k2_funct_1('#skF_4')) = k2_funct_1('#skF_4') ),
    inference(splitRight,[status(thm)],[c_8842])).

tff(c_5853,plain,(
    ! [E_323,D_328,C_326,F_325,A_327,B_324] :
      ( k1_partfun1(A_327,B_324,C_326,D_328,E_323,F_325) = k5_relat_1(E_323,F_325)
      | ~ m1_subset_1(F_325,k1_zfmisc_1(k2_zfmisc_1(C_326,D_328)))
      | ~ v1_funct_1(F_325)
      | ~ m1_subset_1(E_323,k1_zfmisc_1(k2_zfmisc_1(A_327,B_324)))
      | ~ v1_funct_1(E_323) ) ),
    inference(cnfTransformation,[status(thm)],[f_121])).

tff(c_5859,plain,(
    ! [A_327,B_324,E_323] :
      ( k1_partfun1(A_327,B_324,'#skF_2','#skF_1',E_323,'#skF_4') = k5_relat_1(E_323,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_323,k1_zfmisc_1(k2_zfmisc_1(A_327,B_324)))
      | ~ v1_funct_1(E_323) ) ),
    inference(resolution,[status(thm)],[c_74,c_5853])).

tff(c_7713,plain,(
    ! [A_410,B_411,E_412] :
      ( k1_partfun1(A_410,B_411,'#skF_2','#skF_1',E_412,'#skF_4') = k5_relat_1(E_412,'#skF_4')
      | ~ m1_subset_1(E_412,k1_zfmisc_1(k2_zfmisc_1(A_410,B_411)))
      | ~ v1_funct_1(E_412) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_5859])).

tff(c_7719,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_80,c_7713])).

tff(c_7726,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_84,c_5477,c_7719])).

tff(c_7739,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_4')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_7726,c_2])).

tff(c_7747,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_1'),C_7) = k5_relat_1('#skF_3',k5_relat_1('#skF_4',C_7))
      | ~ v1_relat_1(C_7) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_180,c_7739])).

tff(c_8893,plain,
    ( k5_relat_1('#skF_3',k5_relat_1('#skF_4',k2_funct_1('#skF_4'))) = k2_funct_1('#skF_4')
    | ~ v1_relat_1(k2_funct_1('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8884,c_7747])).

tff(c_8911,plain,(
    k2_funct_1('#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_8885,c_238,c_7815,c_8893])).

tff(c_8923,plain,(
    k5_relat_1('#skF_4','#skF_3') = k6_partfun1('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8911,c_7815])).

tff(c_8993,plain,(
    ! [C_7] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_7) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_7))
      | ~ v1_relat_1(C_7)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8923,c_2])).

tff(c_9258,plain,(
    ! [C_456] :
      ( k5_relat_1(k6_partfun1('#skF_2'),C_456) = k5_relat_1('#skF_4',k5_relat_1('#skF_3',C_456))
      | ~ v1_relat_1(C_456) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_180,c_179,c_8993])).

tff(c_8826,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3'))
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_8802])).

tff(c_8844,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),k2_funct_1('#skF_3')) = k2_funct_1('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_179,c_84,c_68,c_5646,c_8826])).

tff(c_9264,plain,
    ( k5_relat_1('#skF_4',k5_relat_1('#skF_3',k2_funct_1('#skF_3'))) = k2_funct_1('#skF_3')
    | ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_9258,c_8844])).

tff(c_9340,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5646,c_6772,c_7819,c_9264])).

tff(c_9342,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_9340])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:40:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.71/2.80  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/2.82  
% 8.03/2.82  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/2.83  %$ r2_relset_1 > v1_funct_2 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 8.03/2.83  
% 8.03/2.83  %Foreground sorts:
% 8.03/2.83  
% 8.03/2.83  
% 8.03/2.83  %Background operators:
% 8.03/2.83  
% 8.03/2.83  
% 8.03/2.83  %Foreground operators:
% 8.03/2.83  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 8.03/2.83  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 8.03/2.83  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 8.03/2.83  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 8.03/2.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 8.03/2.83  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 8.03/2.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 8.03/2.83  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 8.03/2.83  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 8.03/2.83  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 8.03/2.83  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 8.03/2.83  tff('#skF_2', type, '#skF_2': $i).
% 8.03/2.83  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 8.03/2.83  tff('#skF_3', type, '#skF_3': $i).
% 8.03/2.83  tff('#skF_1', type, '#skF_1': $i).
% 8.03/2.83  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 8.03/2.83  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 8.03/2.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 8.03/2.83  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 8.03/2.83  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 8.03/2.83  tff('#skF_4', type, '#skF_4': $i).
% 8.03/2.83  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 8.03/2.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 8.03/2.83  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 8.03/2.83  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 8.03/2.83  
% 8.03/2.85  tff(f_208, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 8.03/2.85  tff(f_83, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 8.03/2.85  tff(f_55, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 8.03/2.85  tff(f_123, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 8.03/2.85  tff(f_59, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 8.03/2.85  tff(f_39, axiom, (![A]: ((k1_relat_1(k6_relat_1(A)) = A) & (k2_relat_1(k6_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_relat_1)).
% 8.03/2.85  tff(f_43, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(k6_relat_1(k1_relat_1(A)), A) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_relat_1)).
% 8.03/2.85  tff(f_79, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 8.03/2.85  tff(f_87, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 8.03/2.85  tff(f_47, axiom, (![A]: (v1_relat_1(A) => (k5_relat_1(A, k6_relat_1(k2_relat_1(A))) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_relat_1)).
% 8.03/2.85  tff(f_35, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 8.03/2.85  tff(f_182, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (((k2_relset_1(A, B, C) = B) & v2_funct_1(C)) => ((B = k1_xboole_0) | ((k5_relat_1(C, k2_funct_1(C)) = k6_partfun1(A)) & (k5_relat_1(k2_funct_1(C), C) = k6_partfun1(B))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t35_funct_2)).
% 8.03/2.85  tff(f_111, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 8.03/2.85  tff(f_95, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 8.03/2.85  tff(f_107, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 8.03/2.85  tff(f_140, axiom, (![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => (r2_relset_1(B, B, k1_partfun1(B, A, A, B, D, C), k6_partfun1(B)) => (k2_relset_1(A, B, C) = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_funct_2)).
% 8.03/2.85  tff(f_166, axiom, (![A, B, C, D]: (((v1_funct_1(D) & v1_funct_2(D, A, B)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![E]: (((v1_funct_1(E) & v1_funct_2(E, B, C)) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(B, C)))) => ((v2_funct_1(k1_partfun1(A, B, B, C, D, E)) & (k2_relset_1(A, B, D) = B)) => (((C = k1_xboole_0) & ~(B = k1_xboole_0)) | (v2_funct_1(D) & v2_funct_1(E)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t30_funct_2)).
% 8.03/2.85  tff(f_69, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k2_relat_1(A) = k1_relat_1(k2_funct_1(A))) & (k1_relat_1(A) = k2_relat_1(k2_funct_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_funct_1)).
% 8.03/2.85  tff(f_121, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 8.03/2.85  tff(c_62, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_80, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_167, plain, (![C_66, A_67, B_68]: (v1_relat_1(C_66) | ~m1_subset_1(C_66, k1_zfmisc_1(k2_zfmisc_1(A_67, B_68))))), inference(cnfTransformation, [status(thm)], [f_83])).
% 8.03/2.85  tff(c_179, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_167])).
% 8.03/2.85  tff(c_84, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_14, plain, (![A_11]: (v1_relat_1(k2_funct_1(A_11)) | ~v1_funct_1(A_11) | ~v1_relat_1(A_11))), inference(cnfTransformation, [status(thm)], [f_55])).
% 8.03/2.85  tff(c_68, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_46, plain, (![A_38]: (k6_relat_1(A_38)=k6_partfun1(A_38))), inference(cnfTransformation, [status(thm)], [f_123])).
% 8.03/2.85  tff(c_16, plain, (![A_12]: (v1_relat_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.03/2.85  tff(c_88, plain, (![A_12]: (v1_relat_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_16])).
% 8.03/2.85  tff(c_4, plain, (![A_8]: (k1_relat_1(k6_relat_1(A_8))=A_8)), inference(cnfTransformation, [status(thm)], [f_39])).
% 8.03/2.85  tff(c_92, plain, (![A_8]: (k1_relat_1(k6_partfun1(A_8))=A_8)), inference(demodulation, [status(thm), theory('equality')], [c_46, c_4])).
% 8.03/2.85  tff(c_8, plain, (![A_9]: (k5_relat_1(k6_relat_1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(cnfTransformation, [status(thm)], [f_43])).
% 8.03/2.85  tff(c_130, plain, (![A_63]: (k5_relat_1(k6_partfun1(k1_relat_1(A_63)), A_63)=A_63 | ~v1_relat_1(A_63))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 8.03/2.85  tff(c_139, plain, (![A_8]: (k5_relat_1(k6_partfun1(A_8), k6_partfun1(A_8))=k6_partfun1(A_8) | ~v1_relat_1(k6_partfun1(A_8)))), inference(superposition, [status(thm), theory('equality')], [c_92, c_130])).
% 8.03/2.85  tff(c_143, plain, (![A_8]: (k5_relat_1(k6_partfun1(A_8), k6_partfun1(A_8))=k6_partfun1(A_8))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_139])).
% 8.03/2.85  tff(c_26, plain, (![A_14]: (k5_relat_1(A_14, k2_funct_1(A_14))=k6_relat_1(k1_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(cnfTransformation, [status(thm)], [f_79])).
% 8.03/2.85  tff(c_85, plain, (![A_14]: (k5_relat_1(A_14, k2_funct_1(A_14))=k6_partfun1(k1_relat_1(A_14)) | ~v2_funct_1(A_14) | ~v1_funct_1(A_14) | ~v1_relat_1(A_14))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_26])).
% 8.03/2.85  tff(c_72, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_216, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_87])).
% 8.03/2.85  tff(c_222, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_216])).
% 8.03/2.85  tff(c_229, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_72, c_222])).
% 8.03/2.85  tff(c_10, plain, (![A_10]: (k5_relat_1(A_10, k6_relat_1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(cnfTransformation, [status(thm)], [f_47])).
% 8.03/2.85  tff(c_89, plain, (![A_10]: (k5_relat_1(A_10, k6_partfun1(k2_relat_1(A_10)))=A_10 | ~v1_relat_1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_10])).
% 8.03/2.85  tff(c_234, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_229, c_89])).
% 8.03/2.85  tff(c_238, plain, (k5_relat_1('#skF_3', k6_partfun1('#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_234])).
% 8.03/2.85  tff(c_90, plain, (![A_9]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), A_9)=A_9 | ~v1_relat_1(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_8])).
% 8.03/2.85  tff(c_266, plain, (![A_80, B_81, C_82]: (k5_relat_1(k5_relat_1(A_80, B_81), C_82)=k5_relat_1(A_80, k5_relat_1(B_81, C_82)) | ~v1_relat_1(C_82) | ~v1_relat_1(B_81) | ~v1_relat_1(A_80))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.03/2.85  tff(c_301, plain, (![A_9, C_82]: (k5_relat_1(k6_partfun1(k1_relat_1(A_9)), k5_relat_1(A_9, C_82))=k5_relat_1(A_9, C_82) | ~v1_relat_1(C_82) | ~v1_relat_1(A_9) | ~v1_relat_1(k6_partfun1(k1_relat_1(A_9))) | ~v1_relat_1(A_9))), inference(superposition, [status(thm), theory('equality')], [c_90, c_266])).
% 8.03/2.85  tff(c_4715, plain, (![A_275, C_276]: (k5_relat_1(k6_partfun1(k1_relat_1(A_275)), k5_relat_1(A_275, C_276))=k5_relat_1(A_275, C_276) | ~v1_relat_1(C_276) | ~v1_relat_1(A_275))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_301])).
% 8.03/2.85  tff(c_4760, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')=k5_relat_1('#skF_3', k6_partfun1('#skF_2')) | ~v1_relat_1(k6_partfun1('#skF_2')) | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_238, c_4715])).
% 8.03/2.85  tff(c_4802, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_179, c_88, c_238, c_4760])).
% 8.03/2.85  tff(c_2, plain, (![A_1, B_5, C_7]: (k5_relat_1(k5_relat_1(A_1, B_5), C_7)=k5_relat_1(A_1, k5_relat_1(B_5, C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1(B_5) | ~v1_relat_1(A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 8.03/2.85  tff(c_5488, plain, (![C_7]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_7))=k5_relat_1('#skF_3', C_7) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k6_partfun1(k1_relat_1('#skF_3'))))), inference(superposition, [status(thm), theory('equality')], [c_4802, c_2])).
% 8.03/2.85  tff(c_5565, plain, (![C_312]: (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k5_relat_1('#skF_3', C_312))=k5_relat_1('#skF_3', C_312) | ~v1_relat_1(C_312))), inference(demodulation, [status(thm), theory('equality')], [c_88, c_179, c_5488])).
% 8.03/2.85  tff(c_5603, plain, (k5_relat_1(k6_partfun1(k1_relat_1('#skF_3')), k6_partfun1(k1_relat_1('#skF_3')))=k5_relat_1('#skF_3', k2_funct_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_85, c_5565])).
% 8.03/2.85  tff(c_5632, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3')) | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_84, c_68, c_143, c_5603])).
% 8.03/2.85  tff(c_5637, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_5632])).
% 8.03/2.85  tff(c_5640, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_14, c_5637])).
% 8.03/2.85  tff(c_5644, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_179, c_84, c_5640])).
% 8.03/2.85  tff(c_5646, plain, (v1_relat_1(k2_funct_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5632])).
% 8.03/2.85  tff(c_74, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_180, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_167])).
% 8.03/2.85  tff(c_66, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_78, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_76, plain, (v1_funct_2('#skF_4', '#skF_2', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_230, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')=k2_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_216])).
% 8.03/2.85  tff(c_5906, plain, (![B_332, C_333, A_334]: (k6_partfun1(B_332)=k5_relat_1(k2_funct_1(C_333), C_333) | k1_xboole_0=B_332 | ~v2_funct_1(C_333) | k2_relset_1(A_334, B_332, C_333)!=B_332 | ~m1_subset_1(C_333, k1_zfmisc_1(k2_zfmisc_1(A_334, B_332))) | ~v1_funct_2(C_333, A_334, B_332) | ~v1_funct_1(C_333))), inference(cnfTransformation, [status(thm)], [f_182])).
% 8.03/2.85  tff(c_5912, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_5906])).
% 8.03/2.85  tff(c_5922, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_230, c_5912])).
% 8.03/2.85  tff(c_5923, plain, (k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1') | ~v2_funct_1('#skF_4') | k2_relat_1('#skF_4')!='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_66, c_5922])).
% 8.03/2.85  tff(c_5974, plain, (k2_relat_1('#skF_4')!='#skF_1'), inference(splitLeft, [status(thm)], [c_5923])).
% 8.03/2.85  tff(c_82, plain, (v1_funct_2('#skF_3', '#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_42, plain, (![A_31]: (m1_subset_1(k6_partfun1(A_31), k1_zfmisc_1(k2_zfmisc_1(A_31, A_31))))), inference(cnfTransformation, [status(thm)], [f_111])).
% 8.03/2.85  tff(c_193, plain, (![A_70, B_71, D_72]: (r2_relset_1(A_70, B_71, D_72, D_72) | ~m1_subset_1(D_72, k1_zfmisc_1(k2_zfmisc_1(A_70, B_71))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.03/2.85  tff(c_200, plain, (![A_31]: (r2_relset_1(A_31, A_31, k6_partfun1(A_31), k6_partfun1(A_31)))), inference(resolution, [status(thm)], [c_42, c_193])).
% 8.03/2.85  tff(c_5441, plain, (![F_308, C_307, D_305, B_309, A_306, E_310]: (m1_subset_1(k1_partfun1(A_306, B_309, C_307, D_305, E_310, F_308), k1_zfmisc_1(k2_zfmisc_1(A_306, D_305))) | ~m1_subset_1(F_308, k1_zfmisc_1(k2_zfmisc_1(C_307, D_305))) | ~v1_funct_1(F_308) | ~m1_subset_1(E_310, k1_zfmisc_1(k2_zfmisc_1(A_306, B_309))) | ~v1_funct_1(E_310))), inference(cnfTransformation, [status(thm)], [f_107])).
% 8.03/2.85  tff(c_70, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_4645, plain, (![D_270, C_271, A_272, B_273]: (D_270=C_271 | ~r2_relset_1(A_272, B_273, C_271, D_270) | ~m1_subset_1(D_270, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))) | ~m1_subset_1(C_271, k1_zfmisc_1(k2_zfmisc_1(A_272, B_273))))), inference(cnfTransformation, [status(thm)], [f_95])).
% 8.03/2.85  tff(c_4653, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_70, c_4645])).
% 8.03/2.85  tff(c_4668, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_4653])).
% 8.03/2.85  tff(c_4811, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_4668])).
% 8.03/2.85  tff(c_5458, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_5441, c_4811])).
% 8.03/2.85  tff(c_5476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_84, c_80, c_78, c_74, c_5458])).
% 8.03/2.85  tff(c_5477, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_4668])).
% 8.03/2.85  tff(c_6749, plain, (![A_370, B_371, C_372, D_373]: (k2_relset_1(A_370, B_371, C_372)=B_371 | ~r2_relset_1(B_371, B_371, k1_partfun1(B_371, A_370, A_370, B_371, D_373, C_372), k6_partfun1(B_371)) | ~m1_subset_1(D_373, k1_zfmisc_1(k2_zfmisc_1(B_371, A_370))) | ~v1_funct_2(D_373, B_371, A_370) | ~v1_funct_1(D_373) | ~m1_subset_1(C_372, k1_zfmisc_1(k2_zfmisc_1(A_370, B_371))) | ~v1_funct_2(C_372, A_370, B_371) | ~v1_funct_1(C_372))), inference(cnfTransformation, [status(thm)], [f_140])).
% 8.03/2.85  tff(c_6755, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1' | ~r2_relset_1('#skF_1', '#skF_1', k6_partfun1('#skF_1'), k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3') | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_5477, c_6749])).
% 8.03/2.85  tff(c_6759, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_74, c_84, c_82, c_80, c_200, c_230, c_6755])).
% 8.03/2.85  tff(c_6761, plain, $false, inference(negUnitSimplification, [status(thm)], [c_5974, c_6759])).
% 8.03/2.85  tff(c_6763, plain, (k2_relat_1('#skF_4')='#skF_1'), inference(splitRight, [status(thm)], [c_5923])).
% 8.03/2.85  tff(c_6768, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6763, c_89])).
% 8.03/2.85  tff(c_6772, plain, (k5_relat_1('#skF_4', k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_180, c_6768])).
% 8.03/2.85  tff(c_64, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_208])).
% 8.03/2.85  tff(c_5645, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1(k1_relat_1('#skF_3'))), inference(splitRight, [status(thm)], [c_5632])).
% 8.03/2.85  tff(c_7798, plain, (![A_413, C_414, B_415]: (k6_partfun1(A_413)=k5_relat_1(C_414, k2_funct_1(C_414)) | k1_xboole_0=B_415 | ~v2_funct_1(C_414) | k2_relset_1(A_413, B_415, C_414)!=B_415 | ~m1_subset_1(C_414, k1_zfmisc_1(k2_zfmisc_1(A_413, B_415))) | ~v1_funct_2(C_414, A_413, B_415) | ~v1_funct_1(C_414))), inference(cnfTransformation, [status(thm)], [f_182])).
% 8.03/2.85  tff(c_7802, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2' | ~v2_funct_1('#skF_3') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_7798])).
% 8.03/2.85  tff(c_7810, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1') | k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_72, c_68, c_5645, c_7802])).
% 8.03/2.85  tff(c_7811, plain, (k6_partfun1(k1_relat_1('#skF_3'))=k6_partfun1('#skF_1')), inference(negUnitSimplification, [status(thm)], [c_64, c_7810])).
% 8.03/2.85  tff(c_7819, plain, (k5_relat_1('#skF_3', k2_funct_1('#skF_3'))=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_7811, c_5645])).
% 8.03/2.85  tff(c_6762, plain, (~v2_funct_1('#skF_4') | k5_relat_1(k2_funct_1('#skF_4'), '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_5923])).
% 8.03/2.85  tff(c_6792, plain, (~v2_funct_1('#skF_4')), inference(splitLeft, [status(thm)], [c_6762])).
% 8.03/2.85  tff(c_18, plain, (![A_12]: (v2_funct_1(k6_relat_1(A_12)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 8.03/2.85  tff(c_87, plain, (![A_12]: (v2_funct_1(k6_partfun1(A_12)))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_18])).
% 8.03/2.85  tff(c_7639, plain, (![D_405, C_406, A_409, B_407, E_408]: (k1_xboole_0=C_406 | v2_funct_1(E_408) | k2_relset_1(A_409, B_407, D_405)!=B_407 | ~v2_funct_1(k1_partfun1(A_409, B_407, B_407, C_406, D_405, E_408)) | ~m1_subset_1(E_408, k1_zfmisc_1(k2_zfmisc_1(B_407, C_406))) | ~v1_funct_2(E_408, B_407, C_406) | ~v1_funct_1(E_408) | ~m1_subset_1(D_405, k1_zfmisc_1(k2_zfmisc_1(A_409, B_407))) | ~v1_funct_2(D_405, A_409, B_407) | ~v1_funct_1(D_405))), inference(cnfTransformation, [status(thm)], [f_166])).
% 8.03/2.85  tff(c_7641, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4') | k2_relset_1('#skF_1', '#skF_2', '#skF_3')!='#skF_2' | ~v2_funct_1(k6_partfun1('#skF_1')) | ~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_2('#skF_3', '#skF_1', '#skF_2') | ~v1_funct_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_5477, c_7639])).
% 8.03/2.85  tff(c_7643, plain, (k1_xboole_0='#skF_1' | v2_funct_1('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_82, c_80, c_78, c_76, c_74, c_87, c_72, c_7641])).
% 8.03/2.85  tff(c_7645, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6792, c_66, c_7643])).
% 8.03/2.85  tff(c_7647, plain, (v2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_6762])).
% 8.03/2.85  tff(c_204, plain, (![A_74]: (k1_relat_1(k2_funct_1(A_74))=k2_relat_1(A_74) | ~v2_funct_1(A_74) | ~v1_funct_1(A_74) | ~v1_relat_1(A_74))), inference(cnfTransformation, [status(thm)], [f_69])).
% 8.03/2.85  tff(c_8802, plain, (![A_452]: (k5_relat_1(k6_partfun1(k2_relat_1(A_452)), k2_funct_1(A_452))=k2_funct_1(A_452) | ~v1_relat_1(k2_funct_1(A_452)) | ~v2_funct_1(A_452) | ~v1_funct_1(A_452) | ~v1_relat_1(A_452))), inference(superposition, [status(thm), theory('equality')], [c_204, c_90])).
% 8.03/2.85  tff(c_8823, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4')) | ~v2_funct_1('#skF_4') | ~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6763, c_8802])).
% 8.03/2.85  tff(c_8842, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_78, c_7647, c_8823])).
% 8.03/2.85  tff(c_8876, plain, (~v1_relat_1(k2_funct_1('#skF_4'))), inference(splitLeft, [status(thm)], [c_8842])).
% 8.03/2.85  tff(c_8879, plain, (~v1_funct_1('#skF_4') | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_14, c_8876])).
% 8.03/2.85  tff(c_8883, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_180, c_78, c_8879])).
% 8.03/2.85  tff(c_8885, plain, (v1_relat_1(k2_funct_1('#skF_4'))), inference(splitRight, [status(thm)], [c_8842])).
% 8.03/2.85  tff(c_6764, plain, (k2_relset_1('#skF_2', '#skF_1', '#skF_4')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_6763, c_230])).
% 8.03/2.85  tff(c_7804, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1' | ~v2_funct_1('#skF_4') | k2_relset_1('#skF_2', '#skF_1', '#skF_4')!='#skF_1' | ~v1_funct_2('#skF_4', '#skF_2', '#skF_1') | ~v1_funct_1('#skF_4')), inference(resolution, [status(thm)], [c_74, c_7798])).
% 8.03/2.85  tff(c_7814, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2') | k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_78, c_76, c_6764, c_7647, c_7804])).
% 8.03/2.85  tff(c_7815, plain, (k5_relat_1('#skF_4', k2_funct_1('#skF_4'))=k6_partfun1('#skF_2')), inference(negUnitSimplification, [status(thm)], [c_66, c_7814])).
% 8.03/2.85  tff(c_8884, plain, (k5_relat_1(k6_partfun1('#skF_1'), k2_funct_1('#skF_4'))=k2_funct_1('#skF_4')), inference(splitRight, [status(thm)], [c_8842])).
% 8.03/2.85  tff(c_5853, plain, (![E_323, D_328, C_326, F_325, A_327, B_324]: (k1_partfun1(A_327, B_324, C_326, D_328, E_323, F_325)=k5_relat_1(E_323, F_325) | ~m1_subset_1(F_325, k1_zfmisc_1(k2_zfmisc_1(C_326, D_328))) | ~v1_funct_1(F_325) | ~m1_subset_1(E_323, k1_zfmisc_1(k2_zfmisc_1(A_327, B_324))) | ~v1_funct_1(E_323))), inference(cnfTransformation, [status(thm)], [f_121])).
% 8.03/2.85  tff(c_5859, plain, (![A_327, B_324, E_323]: (k1_partfun1(A_327, B_324, '#skF_2', '#skF_1', E_323, '#skF_4')=k5_relat_1(E_323, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_323, k1_zfmisc_1(k2_zfmisc_1(A_327, B_324))) | ~v1_funct_1(E_323))), inference(resolution, [status(thm)], [c_74, c_5853])).
% 8.03/2.85  tff(c_7713, plain, (![A_410, B_411, E_412]: (k1_partfun1(A_410, B_411, '#skF_2', '#skF_1', E_412, '#skF_4')=k5_relat_1(E_412, '#skF_4') | ~m1_subset_1(E_412, k1_zfmisc_1(k2_zfmisc_1(A_410, B_411))) | ~v1_funct_1(E_412))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_5859])).
% 8.03/2.85  tff(c_7719, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_80, c_7713])).
% 8.03/2.85  tff(c_7726, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_84, c_5477, c_7719])).
% 8.03/2.85  tff(c_7739, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_4') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_7726, c_2])).
% 8.03/2.85  tff(c_7747, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_1'), C_7)=k5_relat_1('#skF_3', k5_relat_1('#skF_4', C_7)) | ~v1_relat_1(C_7))), inference(demodulation, [status(thm), theory('equality')], [c_179, c_180, c_7739])).
% 8.03/2.85  tff(c_8893, plain, (k5_relat_1('#skF_3', k5_relat_1('#skF_4', k2_funct_1('#skF_4')))=k2_funct_1('#skF_4') | ~v1_relat_1(k2_funct_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8884, c_7747])).
% 8.03/2.85  tff(c_8911, plain, (k2_funct_1('#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_8885, c_238, c_7815, c_8893])).
% 8.03/2.85  tff(c_8923, plain, (k5_relat_1('#skF_4', '#skF_3')=k6_partfun1('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_8911, c_7815])).
% 8.03/2.85  tff(c_8993, plain, (![C_7]: (k5_relat_1(k6_partfun1('#skF_2'), C_7)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_7)) | ~v1_relat_1(C_7) | ~v1_relat_1('#skF_3') | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_8923, c_2])).
% 8.03/2.85  tff(c_9258, plain, (![C_456]: (k5_relat_1(k6_partfun1('#skF_2'), C_456)=k5_relat_1('#skF_4', k5_relat_1('#skF_3', C_456)) | ~v1_relat_1(C_456))), inference(demodulation, [status(thm), theory('equality')], [c_180, c_179, c_8993])).
% 8.03/2.85  tff(c_8826, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_229, c_8802])).
% 8.03/2.85  tff(c_8844, plain, (k5_relat_1(k6_partfun1('#skF_2'), k2_funct_1('#skF_3'))=k2_funct_1('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_179, c_84, c_68, c_5646, c_8826])).
% 8.03/2.85  tff(c_9264, plain, (k5_relat_1('#skF_4', k5_relat_1('#skF_3', k2_funct_1('#skF_3')))=k2_funct_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_9258, c_8844])).
% 8.03/2.85  tff(c_9340, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_5646, c_6772, c_7819, c_9264])).
% 8.03/2.85  tff(c_9342, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_9340])).
% 8.03/2.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 8.03/2.85  
% 8.03/2.85  Inference rules
% 8.03/2.85  ----------------------
% 8.03/2.85  #Ref     : 0
% 8.03/2.85  #Sup     : 2006
% 8.03/2.85  #Fact    : 0
% 8.03/2.85  #Define  : 0
% 8.03/2.85  #Split   : 33
% 8.03/2.85  #Chain   : 0
% 8.03/2.85  #Close   : 0
% 8.03/2.85  
% 8.03/2.85  Ordering : KBO
% 8.03/2.85  
% 8.03/2.85  Simplification rules
% 8.03/2.85  ----------------------
% 8.03/2.85  #Subsume      : 84
% 8.03/2.85  #Demod        : 3554
% 8.03/2.85  #Tautology    : 1144
% 8.03/2.85  #SimpNegUnit  : 77
% 8.03/2.85  #BackRed      : 91
% 8.03/2.85  
% 8.03/2.85  #Partial instantiations: 0
% 8.03/2.85  #Strategies tried      : 1
% 8.03/2.85  
% 8.03/2.85  Timing (in seconds)
% 8.03/2.85  ----------------------
% 8.03/2.85  Preprocessing        : 0.38
% 8.03/2.85  Parsing              : 0.20
% 8.03/2.85  CNF conversion       : 0.03
% 8.03/2.85  Main loop            : 1.67
% 8.03/2.85  Inferencing          : 0.56
% 8.03/2.86  Reduction            : 0.68
% 8.03/2.86  Demodulation         : 0.52
% 8.03/2.86  BG Simplification    : 0.06
% 8.03/2.86  Subsumption          : 0.26
% 8.03/2.86  Abstraction          : 0.08
% 8.03/2.86  MUC search           : 0.00
% 8.03/2.86  Cooper               : 0.00
% 8.03/2.86  Total                : 2.12
% 8.03/2.86  Index Insertion      : 0.00
% 8.03/2.86  Index Deletion       : 0.00
% 8.03/2.86  Index Matching       : 0.00
% 8.03/2.86  BG Taut test         : 0.00
%------------------------------------------------------------------------------
