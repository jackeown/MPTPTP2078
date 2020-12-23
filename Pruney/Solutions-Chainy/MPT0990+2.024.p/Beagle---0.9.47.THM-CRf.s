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
% DateTime   : Thu Dec  3 10:12:59 EST 2020

% Result     : Theorem 10.91s
% Output     : CNFRefutation 10.91s
% Verified   : 
% Statistics : Number of formulae       :  173 ( 775 expanded)
%              Number of leaves         :   45 ( 292 expanded)
%              Depth                    :   20
%              Number of atoms          :  340 (1934 expanded)
%              Number of equality atoms :   84 ( 604 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(v5_relat_1,type,(
    v5_relat_1: ( $i * $i ) > $o )).

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

tff(v4_relat_1,type,(
    v4_relat_1: ( $i * $i ) > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(m1_subset_1,type,(
    m1_subset_1: ( $i * $i ) > $o )).

tff(f_162,negated_conjecture,(
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

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_136,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_112,axiom,(
    ! [A] : m1_subset_1(k6_relat_1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

tff(f_134,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_124,axiom,(
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
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_88,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

tff(f_86,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ! [B] :
          ( ( v1_relat_1(B)
            & v1_funct_1(B) )
         => ( ( v2_funct_1(A)
              & v2_funct_1(B) )
           => k2_funct_1(k5_relat_1(A,B)) = k5_relat_1(k2_funct_1(B),k2_funct_1(A)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_funct_1)).

tff(c_50,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_68,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_120,plain,(
    ! [C_56,A_57,B_58] :
      ( v1_relat_1(C_56)
      | ~ m1_subset_1(C_56,k1_zfmisc_1(k2_zfmisc_1(A_57,B_58))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_132,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_120])).

tff(c_72,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_56,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_158,plain,(
    ! [C_67,A_68,B_69] :
      ( v4_relat_1(C_67,A_68)
      | ~ m1_subset_1(C_67,k1_zfmisc_1(k2_zfmisc_1(A_68,B_69))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_169,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_68,c_158])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_173,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_169,c_2])).

tff(c_176,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_173])).

tff(c_48,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_6,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_81,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_partfun1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_6])).

tff(c_14,plain,(
    ! [A_13] : v1_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_79,plain,(
    ! [A_13] : v1_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_40,plain,(
    ! [A_33] : m1_subset_1(k6_relat_1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_73,plain,(
    ! [A_33] : m1_subset_1(k6_partfun1(A_33),k1_zfmisc_1(k2_zfmisc_1(A_33,A_33))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_40])).

tff(c_1972,plain,(
    ! [D_170,E_168,A_169,C_172,B_173,F_171] :
      ( k1_partfun1(A_169,B_173,C_172,D_170,E_168,F_171) = k5_relat_1(E_168,F_171)
      | ~ m1_subset_1(F_171,k1_zfmisc_1(k2_zfmisc_1(C_172,D_170)))
      | ~ v1_funct_1(F_171)
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_173)))
      | ~ v1_funct_1(E_168) ) ),
    inference(cnfTransformation,[status(thm)],[f_134])).

tff(c_1980,plain,(
    ! [A_169,B_173,E_168] :
      ( k1_partfun1(A_169,B_173,'#skF_1','#skF_2',E_168,'#skF_3') = k5_relat_1(E_168,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_173)))
      | ~ v1_funct_1(E_168) ) ),
    inference(resolution,[status(thm)],[c_68,c_1972])).

tff(c_2714,plain,(
    ! [A_209,B_210,E_211] :
      ( k1_partfun1(A_209,B_210,'#skF_1','#skF_2',E_211,'#skF_3') = k5_relat_1(E_211,'#skF_3')
      | ~ m1_subset_1(E_211,k1_zfmisc_1(k2_zfmisc_1(A_209,B_210)))
      | ~ v1_funct_1(E_211) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1980])).

tff(c_2726,plain,(
    ! [A_33] :
      ( k1_partfun1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3') = k5_relat_1(k6_partfun1(A_33),'#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_73,c_2714])).

tff(c_2742,plain,(
    ! [A_33] : k1_partfun1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3') = k5_relat_1(k6_partfun1(A_33),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_2726])).

tff(c_2296,plain,(
    ! [D_188,B_191,F_189,A_187,E_190,C_192] :
      ( m1_subset_1(k1_partfun1(A_187,B_191,C_192,D_188,E_190,F_189),k1_zfmisc_1(k2_zfmisc_1(A_187,D_188)))
      | ~ m1_subset_1(F_189,k1_zfmisc_1(k2_zfmisc_1(C_192,D_188)))
      | ~ v1_funct_1(F_189)
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_187,B_191)))
      | ~ v1_funct_1(E_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_28,plain,(
    ! [C_22,A_20,B_21] :
      ( v1_relat_1(C_22)
      | ~ m1_subset_1(C_22,k1_zfmisc_1(k2_zfmisc_1(A_20,B_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_4215,plain,(
    ! [E_255,F_254,C_253,A_256,D_258,B_257] :
      ( v1_relat_1(k1_partfun1(A_256,B_257,C_253,D_258,E_255,F_254))
      | ~ m1_subset_1(F_254,k1_zfmisc_1(k2_zfmisc_1(C_253,D_258)))
      | ~ v1_funct_1(F_254)
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ v1_funct_1(E_255) ) ),
    inference(resolution,[status(thm)],[c_2296,c_28])).

tff(c_4235,plain,(
    ! [A_256,B_257,E_255] :
      ( v1_relat_1(k1_partfun1(A_256,B_257,'#skF_1','#skF_2',E_255,'#skF_3'))
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_255,k1_zfmisc_1(k2_zfmisc_1(A_256,B_257)))
      | ~ v1_funct_1(E_255) ) ),
    inference(resolution,[status(thm)],[c_68,c_4215])).

tff(c_4273,plain,(
    ! [A_259,B_260,E_261] :
      ( v1_relat_1(k1_partfun1(A_259,B_260,'#skF_1','#skF_2',E_261,'#skF_3'))
      | ~ m1_subset_1(E_261,k1_zfmisc_1(k2_zfmisc_1(A_259,B_260)))
      | ~ v1_funct_1(E_261) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4235])).

tff(c_4300,plain,(
    ! [A_33] :
      ( v1_relat_1(k1_partfun1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3'))
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_73,c_4273])).

tff(c_4331,plain,(
    ! [A_33] : v1_relat_1(k1_partfun1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_4300])).

tff(c_7940,plain,(
    ! [A_351] : v1_relat_1(k5_relat_1(k6_partfun1(A_351),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2742,c_4331])).

tff(c_7964,plain,(
    ! [A_10] :
      ( v1_relat_1(k7_relat_1('#skF_3',A_10))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7940])).

tff(c_7974,plain,(
    ! [A_10] : v1_relat_1(k7_relat_1('#skF_3',A_10)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_7964])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_4708,plain,(
    ! [A_282,D_284,E_281,B_283,C_279,F_280] :
      ( v4_relat_1(k1_partfun1(A_282,B_283,C_279,D_284,E_281,F_280),A_282)
      | ~ m1_subset_1(F_280,k1_zfmisc_1(k2_zfmisc_1(C_279,D_284)))
      | ~ v1_funct_1(F_280)
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(E_281) ) ),
    inference(resolution,[status(thm)],[c_2296,c_32])).

tff(c_4728,plain,(
    ! [A_282,B_283,E_281] :
      ( v4_relat_1(k1_partfun1(A_282,B_283,'#skF_1','#skF_2',E_281,'#skF_3'),A_282)
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(E_281) ) ),
    inference(resolution,[status(thm)],[c_68,c_4708])).

tff(c_4787,plain,(
    ! [A_286,B_287,E_288] :
      ( v4_relat_1(k1_partfun1(A_286,B_287,'#skF_1','#skF_2',E_288,'#skF_3'),A_286)
      | ~ m1_subset_1(E_288,k1_zfmisc_1(k2_zfmisc_1(A_286,B_287)))
      | ~ v1_funct_1(E_288) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_4728])).

tff(c_4805,plain,(
    ! [A_33] :
      ( v4_relat_1(k1_partfun1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3'),A_33)
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_73,c_4787])).

tff(c_4834,plain,(
    ! [A_33] : v4_relat_1(k1_partfun1(A_33,A_33,'#skF_1','#skF_2',k6_partfun1(A_33),'#skF_3'),A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_4805])).

tff(c_7991,plain,(
    ! [A_353] : v4_relat_1(k5_relat_1(k6_partfun1(A_353),'#skF_3'),A_353) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2742,c_4834])).

tff(c_8022,plain,(
    ! [A_10] :
      ( v4_relat_1(k7_relat_1('#skF_3',A_10),A_10)
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_7991])).

tff(c_8034,plain,(
    ! [A_354] : v4_relat_1(k7_relat_1('#skF_3',A_354),A_354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_8022])).

tff(c_8037,plain,(
    ! [A_354] :
      ( k7_relat_1(k7_relat_1('#skF_3',A_354),A_354) = k7_relat_1('#skF_3',A_354)
      | ~ v1_relat_1(k7_relat_1('#skF_3',A_354)) ) ),
    inference(resolution,[status(thm)],[c_8034,c_2])).

tff(c_8051,plain,(
    ! [A_354] : k7_relat_1(k7_relat_1('#skF_3',A_354),A_354) = k7_relat_1('#skF_3',A_354) ),
    inference(demodulation,[status(thm),theory(equality)],[c_7974,c_8037])).

tff(c_7775,plain,(
    ! [A_33] : v1_relat_1(k5_relat_1(k6_partfun1(A_33),'#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2742,c_4331])).

tff(c_7994,plain,(
    ! [A_353] :
      ( k7_relat_1(k5_relat_1(k6_partfun1(A_353),'#skF_3'),A_353) = k5_relat_1(k6_partfun1(A_353),'#skF_3')
      | ~ v1_relat_1(k5_relat_1(k6_partfun1(A_353),'#skF_3')) ) ),
    inference(resolution,[status(thm)],[c_7991,c_2])).

tff(c_10213,plain,(
    ! [A_396] : k7_relat_1(k5_relat_1(k6_partfun1(A_396),'#skF_3'),A_396) = k5_relat_1(k6_partfun1(A_396),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_7775,c_7994])).

tff(c_10269,plain,(
    ! [A_10] :
      ( k7_relat_1(k7_relat_1('#skF_3',A_10),A_10) = k5_relat_1(k6_partfun1(A_10),'#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_10213])).

tff(c_10293,plain,(
    ! [A_10] : k5_relat_1(k6_partfun1(A_10),'#skF_3') = k7_relat_1('#skF_3',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_8051,c_10269])).

tff(c_62,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_133,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_62,c_120])).

tff(c_170,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_62,c_158])).

tff(c_179,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_170,c_2])).

tff(c_182,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_179])).

tff(c_16,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [A_14] : v1_relat_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_16])).

tff(c_18,plain,(
    ! [A_14] : v2_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_77,plain,(
    ! [A_14] : v2_funct_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_18])).

tff(c_26,plain,(
    ! [A_19] : k2_funct_1(k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_74,plain,(
    ! [A_19] : k2_funct_1(k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_48,c_26])).

tff(c_183,plain,(
    ! [A_70] : v4_relat_1(k6_partfun1(A_70),A_70) ),
    inference(resolution,[status(thm)],[c_73,c_158])).

tff(c_186,plain,(
    ! [A_70] :
      ( k7_relat_1(k6_partfun1(A_70),A_70) = k6_partfun1(A_70)
      | ~ v1_relat_1(k6_partfun1(A_70)) ) ),
    inference(resolution,[status(thm)],[c_183,c_2])).

tff(c_189,plain,(
    ! [A_70] : k7_relat_1(k6_partfun1(A_70),A_70) = k6_partfun1(A_70) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_186])).

tff(c_22,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_249,plain,(
    ! [A_80] :
      ( k5_relat_1(A_80,k2_funct_1(A_80)) = k6_partfun1(k1_relat_1(A_80))
      | ~ v2_funct_1(A_80)
      | ~ v1_funct_1(A_80)
      | ~ v1_relat_1(A_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_22])).

tff(c_256,plain,(
    ! [A_10] :
      ( k7_relat_1(k2_funct_1(k6_partfun1(A_10)),A_10) = k6_partfun1(k1_relat_1(k6_partfun1(A_10)))
      | ~ v1_relat_1(k2_funct_1(k6_partfun1(A_10)))
      | ~ v2_funct_1(k6_partfun1(A_10))
      | ~ v1_funct_1(k6_partfun1(A_10))
      | ~ v1_relat_1(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_81])).

tff(c_269,plain,(
    ! [A_10] : k6_partfun1(k1_relat_1(k6_partfun1(A_10))) = k6_partfun1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79,c_77,c_78,c_74,c_189,c_74,c_256])).

tff(c_266,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(k1_relat_1(k6_partfun1(A_19)))
      | ~ v2_funct_1(k6_partfun1(A_19))
      | ~ v1_funct_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_249])).

tff(c_274,plain,(
    ! [A_19] : k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(k1_relat_1(k6_partfun1(A_19))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79,c_77,c_266])).

tff(c_424,plain,(
    ! [A_19] : k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_269,c_274])).

tff(c_20,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_275,plain,(
    ! [A_81] :
      ( k5_relat_1(k2_funct_1(A_81),A_81) = k6_partfun1(k2_relat_1(A_81))
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_284,plain,(
    ! [A_19] :
      ( k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(k2_relat_1(k6_partfun1(A_19)))
      | ~ v2_funct_1(k6_partfun1(A_19))
      | ~ v1_funct_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_275])).

tff(c_288,plain,(
    ! [A_19] : k5_relat_1(k6_partfun1(A_19),k6_partfun1(A_19)) = k6_partfun1(k2_relat_1(k6_partfun1(A_19))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79,c_77,c_284])).

tff(c_458,plain,(
    ! [A_19] : k6_partfun1(k2_relat_1(k6_partfun1(A_19))) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_288])).

tff(c_66,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_1982,plain,(
    ! [A_169,B_173,E_168] :
      ( k1_partfun1(A_169,B_173,'#skF_2','#skF_1',E_168,'#skF_4') = k5_relat_1(E_168,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_168,k1_zfmisc_1(k2_zfmisc_1(A_169,B_173)))
      | ~ v1_funct_1(E_168) ) ),
    inference(resolution,[status(thm)],[c_62,c_1972])).

tff(c_3097,plain,(
    ! [A_224,B_225,E_226] :
      ( k1_partfun1(A_224,B_225,'#skF_2','#skF_1',E_226,'#skF_4') = k5_relat_1(E_226,'#skF_4')
      | ~ m1_subset_1(E_226,k1_zfmisc_1(k2_zfmisc_1(A_224,B_225)))
      | ~ v1_funct_1(E_226) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1982])).

tff(c_3115,plain,(
    ! [A_33] :
      ( k1_partfun1(A_33,A_33,'#skF_2','#skF_1',k6_partfun1(A_33),'#skF_4') = k5_relat_1(k6_partfun1(A_33),'#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_73,c_3097])).

tff(c_3137,plain,(
    ! [A_33] : k1_partfun1(A_33,A_33,'#skF_2','#skF_1',k6_partfun1(A_33),'#skF_4') = k5_relat_1(k6_partfun1(A_33),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_3115])).

tff(c_4730,plain,(
    ! [A_282,B_283,E_281] :
      ( v4_relat_1(k1_partfun1(A_282,B_283,'#skF_2','#skF_1',E_281,'#skF_4'),A_282)
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_281,k1_zfmisc_1(k2_zfmisc_1(A_282,B_283)))
      | ~ v1_funct_1(E_281) ) ),
    inference(resolution,[status(thm)],[c_62,c_4708])).

tff(c_5198,plain,(
    ! [A_295,B_296,E_297] :
      ( v4_relat_1(k1_partfun1(A_295,B_296,'#skF_2','#skF_1',E_297,'#skF_4'),A_295)
      | ~ m1_subset_1(E_297,k1_zfmisc_1(k2_zfmisc_1(A_295,B_296)))
      | ~ v1_funct_1(E_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_4730])).

tff(c_5216,plain,(
    ! [A_33] :
      ( v4_relat_1(k1_partfun1(A_33,A_33,'#skF_2','#skF_1',k6_partfun1(A_33),'#skF_4'),A_33)
      | ~ v1_funct_1(k6_partfun1(A_33)) ) ),
    inference(resolution,[status(thm)],[c_73,c_5198])).

tff(c_5245,plain,(
    ! [A_33] : v4_relat_1(k1_partfun1(A_33,A_33,'#skF_2','#skF_1',k6_partfun1(A_33),'#skF_4'),A_33) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_5216])).

tff(c_11466,plain,(
    ! [A_432] : v4_relat_1(k5_relat_1(k6_partfun1(A_432),'#skF_4'),A_432) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3137,c_5245])).

tff(c_11751,plain,(
    ! [A_436] : v4_relat_1(k5_relat_1(k6_partfun1(A_436),'#skF_4'),k2_relat_1(k6_partfun1(A_436))) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_11466])).

tff(c_11794,plain,(
    ! [A_10] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_10),k2_relat_1(k6_partfun1(A_10)))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_81,c_11751])).

tff(c_11810,plain,(
    ! [A_437] : v4_relat_1(k7_relat_1('#skF_4',A_437),k2_relat_1(k6_partfun1(A_437))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_11794])).

tff(c_11836,plain,(
    v4_relat_1('#skF_4',k2_relat_1(k6_partfun1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_11810])).

tff(c_11847,plain,
    ( k7_relat_1('#skF_4',k2_relat_1(k6_partfun1('#skF_2'))) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_11836,c_2])).

tff(c_11850,plain,(
    k7_relat_1('#skF_4',k2_relat_1(k6_partfun1('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_11847])).

tff(c_459,plain,(
    ! [A_90] : k6_partfun1(k2_relat_1(k6_partfun1(A_90))) = k6_partfun1(A_90) ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_288])).

tff(c_513,plain,(
    ! [B_11,A_90] :
      ( k7_relat_1(B_11,k2_relat_1(k6_partfun1(A_90))) = k5_relat_1(k6_partfun1(A_90),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_459,c_81])).

tff(c_11869,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_11850,c_513])).

tff(c_11883,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_11869])).

tff(c_1481,plain,(
    ! [C_147,E_145,A_142,D_143,B_146,F_144] :
      ( m1_subset_1(k1_partfun1(A_142,B_146,C_147,D_143,E_145,F_144),k1_zfmisc_1(k2_zfmisc_1(A_142,D_143)))
      | ~ m1_subset_1(F_144,k1_zfmisc_1(k2_zfmisc_1(C_147,D_143)))
      | ~ v1_funct_1(F_144)
      | ~ m1_subset_1(E_145,k1_zfmisc_1(k2_zfmisc_1(A_142,B_146)))
      | ~ v1_funct_1(E_145) ) ),
    inference(cnfTransformation,[status(thm)],[f_124])).

tff(c_58,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_557,plain,(
    ! [D_91,C_92,A_93,B_94] :
      ( D_91 = C_92
      | ~ r2_relset_1(A_93,B_94,C_92,D_91)
      | ~ m1_subset_1(D_91,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94)))
      | ~ m1_subset_1(C_92,k1_zfmisc_1(k2_zfmisc_1(A_93,B_94))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_565,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_58,c_557])).

tff(c_580,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_73,c_565])).

tff(c_646,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_580])).

tff(c_1494,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1481,c_646])).

tff(c_1516,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_68,c_66,c_62,c_1494])).

tff(c_1517,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_580])).

tff(c_3118,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_3097])).

tff(c_3140,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1517,c_3118])).

tff(c_10,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_60,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_162])).

tff(c_217,plain,(
    ! [A_75,B_76,C_77] :
      ( k2_relset_1(A_75,B_76,C_77) = k2_relat_1(C_77)
      | ~ m1_subset_1(C_77,k1_zfmisc_1(k2_zfmisc_1(A_75,B_76))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_223,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_217])).

tff(c_229,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_223])).

tff(c_76,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_partfun1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_20])).

tff(c_363,plain,(
    ! [A_84,B_85,C_86] :
      ( k5_relat_1(k5_relat_1(A_84,B_85),C_86) = k5_relat_1(A_84,k5_relat_1(B_85,C_86))
      | ~ v1_relat_1(C_86)
      | ~ v1_relat_1(B_85)
      | ~ v1_relat_1(A_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_3534,plain,(
    ! [A_238,C_239] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_238)),C_239) = k5_relat_1(k2_funct_1(A_238),k5_relat_1(A_238,C_239))
      | ~ v1_relat_1(C_239)
      | ~ v1_relat_1(A_238)
      | ~ v1_relat_1(k2_funct_1(A_238))
      | ~ v2_funct_1(A_238)
      | ~ v1_funct_1(A_238)
      | ~ v1_relat_1(A_238) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_363])).

tff(c_3677,plain,(
    ! [C_239] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_239)) = k5_relat_1(k6_partfun1('#skF_2'),C_239)
      | ~ v1_relat_1(C_239)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_229,c_3534])).

tff(c_3732,plain,(
    ! [C_239] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_239)) = k5_relat_1(k6_partfun1('#skF_2'),C_239)
      | ~ v1_relat_1(C_239)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_72,c_56,c_132,c_3677])).

tff(c_12362,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3732])).

tff(c_12365,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_12362])).

tff(c_12369,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_72,c_12365])).

tff(c_13061,plain,(
    ! [C_455] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_455)) = k5_relat_1(k6_partfun1('#skF_2'),C_455)
      | ~ v1_relat_1(C_455) ) ),
    inference(splitRight,[status(thm)],[c_3732])).

tff(c_13115,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_3140,c_13061])).

tff(c_13149,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_133,c_11883,c_13115])).

tff(c_1739,plain,(
    ! [B_154,A_155] :
      ( k5_relat_1(k2_funct_1(B_154),k2_funct_1(A_155)) = k2_funct_1(k5_relat_1(A_155,B_154))
      | ~ v2_funct_1(B_154)
      | ~ v2_funct_1(A_155)
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1(A_155)
      | ~ v1_relat_1(A_155) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1770,plain,(
    ! [B_154,A_19] :
      ( k5_relat_1(k2_funct_1(B_154),k6_partfun1(A_19)) = k2_funct_1(k5_relat_1(k6_partfun1(A_19),B_154))
      | ~ v2_funct_1(B_154)
      | ~ v2_funct_1(k6_partfun1(A_19))
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154)
      | ~ v1_funct_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1739])).

tff(c_1776,plain,(
    ! [B_154,A_19] :
      ( k5_relat_1(k2_funct_1(B_154),k6_partfun1(A_19)) = k2_funct_1(k5_relat_1(k6_partfun1(A_19),B_154))
      | ~ v2_funct_1(B_154)
      | ~ v1_funct_1(B_154)
      | ~ v1_relat_1(B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_78,c_79,c_77,c_1770])).

tff(c_13167,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')) = '#skF_4'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_13149,c_1776])).

tff(c_13188,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_72,c_56,c_176,c_10293,c_13167])).

tff(c_13190,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_13188])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:26 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.91/4.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.91/4.10  
% 10.91/4.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.91/4.10  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.91/4.10  
% 10.91/4.10  %Foreground sorts:
% 10.91/4.10  
% 10.91/4.10  
% 10.91/4.10  %Background operators:
% 10.91/4.10  
% 10.91/4.10  
% 10.91/4.10  %Foreground operators:
% 10.91/4.10  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.91/4.10  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.91/4.10  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.91/4.10  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.91/4.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.91/4.10  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.91/4.10  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.91/4.10  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.91/4.10  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.91/4.10  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.91/4.10  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.91/4.10  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.91/4.10  tff('#skF_2', type, '#skF_2': $i).
% 10.91/4.10  tff('#skF_3', type, '#skF_3': $i).
% 10.91/4.10  tff('#skF_1', type, '#skF_1': $i).
% 10.91/4.10  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.91/4.10  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.91/4.10  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.91/4.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.91/4.10  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.91/4.10  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.91/4.10  tff('#skF_4', type, '#skF_4': $i).
% 10.91/4.10  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.91/4.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.91/4.10  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.91/4.10  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.91/4.10  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.91/4.10  
% 10.91/4.13  tff(f_162, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_funct_2)).
% 10.91/4.13  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.91/4.13  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.91/4.13  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t209_relat_1)).
% 10.91/4.13  tff(f_136, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.91/4.13  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_relat_1)).
% 10.91/4.13  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.91/4.13  tff(f_112, axiom, (![A]: m1_subset_1(k6_relat_1(A), k1_zfmisc_1(k2_zfmisc_1(A, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t29_relset_1)).
% 10.91/4.13  tff(f_134, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.91/4.13  tff(f_124, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.91/4.13  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.91/4.13  tff(f_88, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t67_funct_1)).
% 10.91/4.13  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_funct_1)).
% 10.91/4.13  tff(f_110, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.91/4.13  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.91/4.13  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.91/4.13  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_relat_1)).
% 10.91/4.13  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_funct_1)).
% 10.91/4.13  tff(c_50, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_68, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_120, plain, (![C_56, A_57, B_58]: (v1_relat_1(C_56) | ~m1_subset_1(C_56, k1_zfmisc_1(k2_zfmisc_1(A_57, B_58))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.91/4.13  tff(c_132, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_120])).
% 10.91/4.13  tff(c_72, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_56, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_158, plain, (![C_67, A_68, B_69]: (v4_relat_1(C_67, A_68) | ~m1_subset_1(C_67, k1_zfmisc_1(k2_zfmisc_1(A_68, B_69))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.91/4.13  tff(c_169, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_68, c_158])).
% 10.91/4.13  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.91/4.13  tff(c_173, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_169, c_2])).
% 10.91/4.13  tff(c_176, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_173])).
% 10.91/4.13  tff(c_48, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.91/4.13  tff(c_6, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.91/4.13  tff(c_81, plain, (![A_10, B_11]: (k5_relat_1(k6_partfun1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_6])).
% 10.91/4.13  tff(c_14, plain, (![A_13]: (v1_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.91/4.13  tff(c_79, plain, (![A_13]: (v1_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_14])).
% 10.91/4.13  tff(c_40, plain, (![A_33]: (m1_subset_1(k6_relat_1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(cnfTransformation, [status(thm)], [f_112])).
% 10.91/4.13  tff(c_73, plain, (![A_33]: (m1_subset_1(k6_partfun1(A_33), k1_zfmisc_1(k2_zfmisc_1(A_33, A_33))))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_40])).
% 10.91/4.13  tff(c_1972, plain, (![D_170, E_168, A_169, C_172, B_173, F_171]: (k1_partfun1(A_169, B_173, C_172, D_170, E_168, F_171)=k5_relat_1(E_168, F_171) | ~m1_subset_1(F_171, k1_zfmisc_1(k2_zfmisc_1(C_172, D_170))) | ~v1_funct_1(F_171) | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_173))) | ~v1_funct_1(E_168))), inference(cnfTransformation, [status(thm)], [f_134])).
% 10.91/4.13  tff(c_1980, plain, (![A_169, B_173, E_168]: (k1_partfun1(A_169, B_173, '#skF_1', '#skF_2', E_168, '#skF_3')=k5_relat_1(E_168, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_173))) | ~v1_funct_1(E_168))), inference(resolution, [status(thm)], [c_68, c_1972])).
% 10.91/4.13  tff(c_2714, plain, (![A_209, B_210, E_211]: (k1_partfun1(A_209, B_210, '#skF_1', '#skF_2', E_211, '#skF_3')=k5_relat_1(E_211, '#skF_3') | ~m1_subset_1(E_211, k1_zfmisc_1(k2_zfmisc_1(A_209, B_210))) | ~v1_funct_1(E_211))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1980])).
% 10.91/4.13  tff(c_2726, plain, (![A_33]: (k1_partfun1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')=k5_relat_1(k6_partfun1(A_33), '#skF_3') | ~v1_funct_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_73, c_2714])).
% 10.91/4.13  tff(c_2742, plain, (![A_33]: (k1_partfun1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')=k5_relat_1(k6_partfun1(A_33), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_2726])).
% 10.91/4.13  tff(c_2296, plain, (![D_188, B_191, F_189, A_187, E_190, C_192]: (m1_subset_1(k1_partfun1(A_187, B_191, C_192, D_188, E_190, F_189), k1_zfmisc_1(k2_zfmisc_1(A_187, D_188))) | ~m1_subset_1(F_189, k1_zfmisc_1(k2_zfmisc_1(C_192, D_188))) | ~v1_funct_1(F_189) | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_187, B_191))) | ~v1_funct_1(E_190))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.91/4.13  tff(c_28, plain, (![C_22, A_20, B_21]: (v1_relat_1(C_22) | ~m1_subset_1(C_22, k1_zfmisc_1(k2_zfmisc_1(A_20, B_21))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.91/4.13  tff(c_4215, plain, (![E_255, F_254, C_253, A_256, D_258, B_257]: (v1_relat_1(k1_partfun1(A_256, B_257, C_253, D_258, E_255, F_254)) | ~m1_subset_1(F_254, k1_zfmisc_1(k2_zfmisc_1(C_253, D_258))) | ~v1_funct_1(F_254) | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~v1_funct_1(E_255))), inference(resolution, [status(thm)], [c_2296, c_28])).
% 10.91/4.13  tff(c_4235, plain, (![A_256, B_257, E_255]: (v1_relat_1(k1_partfun1(A_256, B_257, '#skF_1', '#skF_2', E_255, '#skF_3')) | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_255, k1_zfmisc_1(k2_zfmisc_1(A_256, B_257))) | ~v1_funct_1(E_255))), inference(resolution, [status(thm)], [c_68, c_4215])).
% 10.91/4.13  tff(c_4273, plain, (![A_259, B_260, E_261]: (v1_relat_1(k1_partfun1(A_259, B_260, '#skF_1', '#skF_2', E_261, '#skF_3')) | ~m1_subset_1(E_261, k1_zfmisc_1(k2_zfmisc_1(A_259, B_260))) | ~v1_funct_1(E_261))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4235])).
% 10.91/4.13  tff(c_4300, plain, (![A_33]: (v1_relat_1(k1_partfun1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')) | ~v1_funct_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_73, c_4273])).
% 10.91/4.13  tff(c_4331, plain, (![A_33]: (v1_relat_1(k1_partfun1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_4300])).
% 10.91/4.13  tff(c_7940, plain, (![A_351]: (v1_relat_1(k5_relat_1(k6_partfun1(A_351), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2742, c_4331])).
% 10.91/4.13  tff(c_7964, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_3', A_10)) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_7940])).
% 10.91/4.13  tff(c_7974, plain, (![A_10]: (v1_relat_1(k7_relat_1('#skF_3', A_10)))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_7964])).
% 10.91/4.13  tff(c_32, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.91/4.13  tff(c_4708, plain, (![A_282, D_284, E_281, B_283, C_279, F_280]: (v4_relat_1(k1_partfun1(A_282, B_283, C_279, D_284, E_281, F_280), A_282) | ~m1_subset_1(F_280, k1_zfmisc_1(k2_zfmisc_1(C_279, D_284))) | ~v1_funct_1(F_280) | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(E_281))), inference(resolution, [status(thm)], [c_2296, c_32])).
% 10.91/4.13  tff(c_4728, plain, (![A_282, B_283, E_281]: (v4_relat_1(k1_partfun1(A_282, B_283, '#skF_1', '#skF_2', E_281, '#skF_3'), A_282) | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(E_281))), inference(resolution, [status(thm)], [c_68, c_4708])).
% 10.91/4.13  tff(c_4787, plain, (![A_286, B_287, E_288]: (v4_relat_1(k1_partfun1(A_286, B_287, '#skF_1', '#skF_2', E_288, '#skF_3'), A_286) | ~m1_subset_1(E_288, k1_zfmisc_1(k2_zfmisc_1(A_286, B_287))) | ~v1_funct_1(E_288))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_4728])).
% 10.91/4.13  tff(c_4805, plain, (![A_33]: (v4_relat_1(k1_partfun1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3'), A_33) | ~v1_funct_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_73, c_4787])).
% 10.91/4.13  tff(c_4834, plain, (![A_33]: (v4_relat_1(k1_partfun1(A_33, A_33, '#skF_1', '#skF_2', k6_partfun1(A_33), '#skF_3'), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_4805])).
% 10.91/4.13  tff(c_7991, plain, (![A_353]: (v4_relat_1(k5_relat_1(k6_partfun1(A_353), '#skF_3'), A_353))), inference(demodulation, [status(thm), theory('equality')], [c_2742, c_4834])).
% 10.91/4.13  tff(c_8022, plain, (![A_10]: (v4_relat_1(k7_relat_1('#skF_3', A_10), A_10) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_7991])).
% 10.91/4.13  tff(c_8034, plain, (![A_354]: (v4_relat_1(k7_relat_1('#skF_3', A_354), A_354))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_8022])).
% 10.91/4.13  tff(c_8037, plain, (![A_354]: (k7_relat_1(k7_relat_1('#skF_3', A_354), A_354)=k7_relat_1('#skF_3', A_354) | ~v1_relat_1(k7_relat_1('#skF_3', A_354)))), inference(resolution, [status(thm)], [c_8034, c_2])).
% 10.91/4.13  tff(c_8051, plain, (![A_354]: (k7_relat_1(k7_relat_1('#skF_3', A_354), A_354)=k7_relat_1('#skF_3', A_354))), inference(demodulation, [status(thm), theory('equality')], [c_7974, c_8037])).
% 10.91/4.13  tff(c_7775, plain, (![A_33]: (v1_relat_1(k5_relat_1(k6_partfun1(A_33), '#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_2742, c_4331])).
% 10.91/4.13  tff(c_7994, plain, (![A_353]: (k7_relat_1(k5_relat_1(k6_partfun1(A_353), '#skF_3'), A_353)=k5_relat_1(k6_partfun1(A_353), '#skF_3') | ~v1_relat_1(k5_relat_1(k6_partfun1(A_353), '#skF_3')))), inference(resolution, [status(thm)], [c_7991, c_2])).
% 10.91/4.13  tff(c_10213, plain, (![A_396]: (k7_relat_1(k5_relat_1(k6_partfun1(A_396), '#skF_3'), A_396)=k5_relat_1(k6_partfun1(A_396), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_7775, c_7994])).
% 10.91/4.13  tff(c_10269, plain, (![A_10]: (k7_relat_1(k7_relat_1('#skF_3', A_10), A_10)=k5_relat_1(k6_partfun1(A_10), '#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_10213])).
% 10.91/4.13  tff(c_10293, plain, (![A_10]: (k5_relat_1(k6_partfun1(A_10), '#skF_3')=k7_relat_1('#skF_3', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_8051, c_10269])).
% 10.91/4.13  tff(c_62, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_133, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_62, c_120])).
% 10.91/4.13  tff(c_170, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_62, c_158])).
% 10.91/4.13  tff(c_179, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_170, c_2])).
% 10.91/4.13  tff(c_182, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_179])).
% 10.91/4.13  tff(c_16, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.91/4.13  tff(c_78, plain, (![A_14]: (v1_relat_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_16])).
% 10.91/4.13  tff(c_18, plain, (![A_14]: (v2_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.91/4.13  tff(c_77, plain, (![A_14]: (v2_funct_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_18])).
% 10.91/4.13  tff(c_26, plain, (![A_19]: (k2_funct_1(k6_relat_1(A_19))=k6_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.91/4.13  tff(c_74, plain, (![A_19]: (k2_funct_1(k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_48, c_26])).
% 10.91/4.13  tff(c_183, plain, (![A_70]: (v4_relat_1(k6_partfun1(A_70), A_70))), inference(resolution, [status(thm)], [c_73, c_158])).
% 10.91/4.13  tff(c_186, plain, (![A_70]: (k7_relat_1(k6_partfun1(A_70), A_70)=k6_partfun1(A_70) | ~v1_relat_1(k6_partfun1(A_70)))), inference(resolution, [status(thm)], [c_183, c_2])).
% 10.91/4.13  tff(c_189, plain, (![A_70]: (k7_relat_1(k6_partfun1(A_70), A_70)=k6_partfun1(A_70))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_186])).
% 10.91/4.13  tff(c_22, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.91/4.13  tff(c_249, plain, (![A_80]: (k5_relat_1(A_80, k2_funct_1(A_80))=k6_partfun1(k1_relat_1(A_80)) | ~v2_funct_1(A_80) | ~v1_funct_1(A_80) | ~v1_relat_1(A_80))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_22])).
% 10.91/4.13  tff(c_256, plain, (![A_10]: (k7_relat_1(k2_funct_1(k6_partfun1(A_10)), A_10)=k6_partfun1(k1_relat_1(k6_partfun1(A_10))) | ~v1_relat_1(k2_funct_1(k6_partfun1(A_10))) | ~v2_funct_1(k6_partfun1(A_10)) | ~v1_funct_1(k6_partfun1(A_10)) | ~v1_relat_1(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_249, c_81])).
% 10.91/4.13  tff(c_269, plain, (![A_10]: (k6_partfun1(k1_relat_1(k6_partfun1(A_10)))=k6_partfun1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79, c_77, c_78, c_74, c_189, c_74, c_256])).
% 10.91/4.13  tff(c_266, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(k1_relat_1(k6_partfun1(A_19))) | ~v2_funct_1(k6_partfun1(A_19)) | ~v1_funct_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_249])).
% 10.91/4.13  tff(c_274, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(k1_relat_1(k6_partfun1(A_19))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79, c_77, c_266])).
% 10.91/4.13  tff(c_424, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_269, c_274])).
% 10.91/4.13  tff(c_20, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.91/4.13  tff(c_275, plain, (![A_81]: (k5_relat_1(k2_funct_1(A_81), A_81)=k6_partfun1(k2_relat_1(A_81)) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 10.91/4.13  tff(c_284, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(k2_relat_1(k6_partfun1(A_19))) | ~v2_funct_1(k6_partfun1(A_19)) | ~v1_funct_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_275])).
% 10.91/4.13  tff(c_288, plain, (![A_19]: (k5_relat_1(k6_partfun1(A_19), k6_partfun1(A_19))=k6_partfun1(k2_relat_1(k6_partfun1(A_19))))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79, c_77, c_284])).
% 10.91/4.13  tff(c_458, plain, (![A_19]: (k6_partfun1(k2_relat_1(k6_partfun1(A_19)))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_288])).
% 10.91/4.13  tff(c_66, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_1982, plain, (![A_169, B_173, E_168]: (k1_partfun1(A_169, B_173, '#skF_2', '#skF_1', E_168, '#skF_4')=k5_relat_1(E_168, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_168, k1_zfmisc_1(k2_zfmisc_1(A_169, B_173))) | ~v1_funct_1(E_168))), inference(resolution, [status(thm)], [c_62, c_1972])).
% 10.91/4.13  tff(c_3097, plain, (![A_224, B_225, E_226]: (k1_partfun1(A_224, B_225, '#skF_2', '#skF_1', E_226, '#skF_4')=k5_relat_1(E_226, '#skF_4') | ~m1_subset_1(E_226, k1_zfmisc_1(k2_zfmisc_1(A_224, B_225))) | ~v1_funct_1(E_226))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1982])).
% 10.91/4.13  tff(c_3115, plain, (![A_33]: (k1_partfun1(A_33, A_33, '#skF_2', '#skF_1', k6_partfun1(A_33), '#skF_4')=k5_relat_1(k6_partfun1(A_33), '#skF_4') | ~v1_funct_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_73, c_3097])).
% 10.91/4.13  tff(c_3137, plain, (![A_33]: (k1_partfun1(A_33, A_33, '#skF_2', '#skF_1', k6_partfun1(A_33), '#skF_4')=k5_relat_1(k6_partfun1(A_33), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_3115])).
% 10.91/4.13  tff(c_4730, plain, (![A_282, B_283, E_281]: (v4_relat_1(k1_partfun1(A_282, B_283, '#skF_2', '#skF_1', E_281, '#skF_4'), A_282) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_281, k1_zfmisc_1(k2_zfmisc_1(A_282, B_283))) | ~v1_funct_1(E_281))), inference(resolution, [status(thm)], [c_62, c_4708])).
% 10.91/4.13  tff(c_5198, plain, (![A_295, B_296, E_297]: (v4_relat_1(k1_partfun1(A_295, B_296, '#skF_2', '#skF_1', E_297, '#skF_4'), A_295) | ~m1_subset_1(E_297, k1_zfmisc_1(k2_zfmisc_1(A_295, B_296))) | ~v1_funct_1(E_297))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_4730])).
% 10.91/4.13  tff(c_5216, plain, (![A_33]: (v4_relat_1(k1_partfun1(A_33, A_33, '#skF_2', '#skF_1', k6_partfun1(A_33), '#skF_4'), A_33) | ~v1_funct_1(k6_partfun1(A_33)))), inference(resolution, [status(thm)], [c_73, c_5198])).
% 10.91/4.13  tff(c_5245, plain, (![A_33]: (v4_relat_1(k1_partfun1(A_33, A_33, '#skF_2', '#skF_1', k6_partfun1(A_33), '#skF_4'), A_33))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_5216])).
% 10.91/4.13  tff(c_11466, plain, (![A_432]: (v4_relat_1(k5_relat_1(k6_partfun1(A_432), '#skF_4'), A_432))), inference(demodulation, [status(thm), theory('equality')], [c_3137, c_5245])).
% 10.91/4.13  tff(c_11751, plain, (![A_436]: (v4_relat_1(k5_relat_1(k6_partfun1(A_436), '#skF_4'), k2_relat_1(k6_partfun1(A_436))))), inference(superposition, [status(thm), theory('equality')], [c_458, c_11466])).
% 10.91/4.13  tff(c_11794, plain, (![A_10]: (v4_relat_1(k7_relat_1('#skF_4', A_10), k2_relat_1(k6_partfun1(A_10))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_81, c_11751])).
% 10.91/4.13  tff(c_11810, plain, (![A_437]: (v4_relat_1(k7_relat_1('#skF_4', A_437), k2_relat_1(k6_partfun1(A_437))))), inference(demodulation, [status(thm), theory('equality')], [c_133, c_11794])).
% 10.91/4.13  tff(c_11836, plain, (v4_relat_1('#skF_4', k2_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_182, c_11810])).
% 10.91/4.13  tff(c_11847, plain, (k7_relat_1('#skF_4', k2_relat_1(k6_partfun1('#skF_2')))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_11836, c_2])).
% 10.91/4.13  tff(c_11850, plain, (k7_relat_1('#skF_4', k2_relat_1(k6_partfun1('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_11847])).
% 10.91/4.13  tff(c_459, plain, (![A_90]: (k6_partfun1(k2_relat_1(k6_partfun1(A_90)))=k6_partfun1(A_90))), inference(demodulation, [status(thm), theory('equality')], [c_424, c_288])).
% 10.91/4.13  tff(c_513, plain, (![B_11, A_90]: (k7_relat_1(B_11, k2_relat_1(k6_partfun1(A_90)))=k5_relat_1(k6_partfun1(A_90), B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_459, c_81])).
% 10.91/4.13  tff(c_11869, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_11850, c_513])).
% 10.91/4.13  tff(c_11883, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_11869])).
% 10.91/4.13  tff(c_1481, plain, (![C_147, E_145, A_142, D_143, B_146, F_144]: (m1_subset_1(k1_partfun1(A_142, B_146, C_147, D_143, E_145, F_144), k1_zfmisc_1(k2_zfmisc_1(A_142, D_143))) | ~m1_subset_1(F_144, k1_zfmisc_1(k2_zfmisc_1(C_147, D_143))) | ~v1_funct_1(F_144) | ~m1_subset_1(E_145, k1_zfmisc_1(k2_zfmisc_1(A_142, B_146))) | ~v1_funct_1(E_145))), inference(cnfTransformation, [status(thm)], [f_124])).
% 10.91/4.13  tff(c_58, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_557, plain, (![D_91, C_92, A_93, B_94]: (D_91=C_92 | ~r2_relset_1(A_93, B_94, C_92, D_91) | ~m1_subset_1(D_91, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))) | ~m1_subset_1(C_92, k1_zfmisc_1(k2_zfmisc_1(A_93, B_94))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.91/4.13  tff(c_565, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_58, c_557])).
% 10.91/4.13  tff(c_580, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_73, c_565])).
% 10.91/4.13  tff(c_646, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_580])).
% 10.91/4.13  tff(c_1494, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1481, c_646])).
% 10.91/4.13  tff(c_1516, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_72, c_68, c_66, c_62, c_1494])).
% 10.91/4.13  tff(c_1517, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_580])).
% 10.91/4.13  tff(c_3118, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_3097])).
% 10.91/4.13  tff(c_3140, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1517, c_3118])).
% 10.91/4.13  tff(c_10, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.91/4.13  tff(c_60, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_162])).
% 10.91/4.13  tff(c_217, plain, (![A_75, B_76, C_77]: (k2_relset_1(A_75, B_76, C_77)=k2_relat_1(C_77) | ~m1_subset_1(C_77, k1_zfmisc_1(k2_zfmisc_1(A_75, B_76))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.91/4.13  tff(c_223, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_68, c_217])).
% 10.91/4.13  tff(c_229, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_60, c_223])).
% 10.91/4.13  tff(c_76, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_partfun1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_20])).
% 10.91/4.13  tff(c_363, plain, (![A_84, B_85, C_86]: (k5_relat_1(k5_relat_1(A_84, B_85), C_86)=k5_relat_1(A_84, k5_relat_1(B_85, C_86)) | ~v1_relat_1(C_86) | ~v1_relat_1(B_85) | ~v1_relat_1(A_84))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.91/4.13  tff(c_3534, plain, (![A_238, C_239]: (k5_relat_1(k6_partfun1(k2_relat_1(A_238)), C_239)=k5_relat_1(k2_funct_1(A_238), k5_relat_1(A_238, C_239)) | ~v1_relat_1(C_239) | ~v1_relat_1(A_238) | ~v1_relat_1(k2_funct_1(A_238)) | ~v2_funct_1(A_238) | ~v1_funct_1(A_238) | ~v1_relat_1(A_238))), inference(superposition, [status(thm), theory('equality')], [c_76, c_363])).
% 10.91/4.13  tff(c_3677, plain, (![C_239]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_239))=k5_relat_1(k6_partfun1('#skF_2'), C_239) | ~v1_relat_1(C_239) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_229, c_3534])).
% 10.91/4.13  tff(c_3732, plain, (![C_239]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_239))=k5_relat_1(k6_partfun1('#skF_2'), C_239) | ~v1_relat_1(C_239) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_132, c_72, c_56, c_132, c_3677])).
% 10.91/4.13  tff(c_12362, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3732])).
% 10.91/4.13  tff(c_12365, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_12362])).
% 10.91/4.13  tff(c_12369, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_72, c_12365])).
% 10.91/4.13  tff(c_13061, plain, (![C_455]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_455))=k5_relat_1(k6_partfun1('#skF_2'), C_455) | ~v1_relat_1(C_455))), inference(splitRight, [status(thm)], [c_3732])).
% 10.91/4.13  tff(c_13115, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3140, c_13061])).
% 10.91/4.13  tff(c_13149, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_133, c_11883, c_13115])).
% 10.91/4.13  tff(c_1739, plain, (![B_154, A_155]: (k5_relat_1(k2_funct_1(B_154), k2_funct_1(A_155))=k2_funct_1(k5_relat_1(A_155, B_154)) | ~v2_funct_1(B_154) | ~v2_funct_1(A_155) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154) | ~v1_funct_1(A_155) | ~v1_relat_1(A_155))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.91/4.13  tff(c_1770, plain, (![B_154, A_19]: (k5_relat_1(k2_funct_1(B_154), k6_partfun1(A_19))=k2_funct_1(k5_relat_1(k6_partfun1(A_19), B_154)) | ~v2_funct_1(B_154) | ~v2_funct_1(k6_partfun1(A_19)) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154) | ~v1_funct_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1739])).
% 10.91/4.13  tff(c_1776, plain, (![B_154, A_19]: (k5_relat_1(k2_funct_1(B_154), k6_partfun1(A_19))=k2_funct_1(k5_relat_1(k6_partfun1(A_19), B_154)) | ~v2_funct_1(B_154) | ~v1_funct_1(B_154) | ~v1_relat_1(B_154))), inference(demodulation, [status(thm), theory('equality')], [c_78, c_79, c_77, c_1770])).
% 10.91/4.13  tff(c_13167, plain, (k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))='#skF_4' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_13149, c_1776])).
% 10.91/4.13  tff(c_13188, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_132, c_72, c_56, c_176, c_10293, c_13167])).
% 10.91/4.13  tff(c_13190, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_13188])).
% 10.91/4.13  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.91/4.13  
% 10.91/4.13  Inference rules
% 10.91/4.13  ----------------------
% 10.91/4.13  #Ref     : 0
% 10.91/4.13  #Sup     : 2954
% 10.91/4.13  #Fact    : 0
% 10.91/4.13  #Define  : 0
% 10.91/4.13  #Split   : 2
% 10.91/4.13  #Chain   : 0
% 10.91/4.13  #Close   : 0
% 10.91/4.13  
% 10.91/4.13  Ordering : KBO
% 10.91/4.13  
% 10.91/4.13  Simplification rules
% 10.91/4.13  ----------------------
% 10.91/4.13  #Subsume      : 43
% 10.91/4.13  #Demod        : 4239
% 10.91/4.13  #Tautology    : 1011
% 10.91/4.13  #SimpNegUnit  : 1
% 10.91/4.13  #BackRed      : 38
% 10.91/4.13  
% 10.91/4.13  #Partial instantiations: 0
% 10.91/4.13  #Strategies tried      : 1
% 10.91/4.13  
% 10.91/4.13  Timing (in seconds)
% 10.91/4.13  ----------------------
% 11.17/4.13  Preprocessing        : 0.38
% 11.17/4.13  Parsing              : 0.21
% 11.17/4.13  CNF conversion       : 0.03
% 11.17/4.13  Main loop            : 2.91
% 11.17/4.13  Inferencing          : 0.65
% 11.17/4.13  Reduction            : 1.55
% 11.17/4.13  Demodulation         : 1.33
% 11.17/4.13  BG Simplification    : 0.08
% 11.17/4.13  Subsumption          : 0.49
% 11.17/4.13  Abstraction          : 0.12
% 11.17/4.13  MUC search           : 0.00
% 11.17/4.13  Cooper               : 0.00
% 11.17/4.13  Total                : 3.34
% 11.17/4.13  Index Insertion      : 0.00
% 11.17/4.13  Index Deletion       : 0.00
% 11.17/4.13  Index Matching       : 0.00
% 11.17/4.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------
