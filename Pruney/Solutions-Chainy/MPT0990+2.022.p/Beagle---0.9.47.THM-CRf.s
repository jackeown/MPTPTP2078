%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:12:58 EST 2020

% Result     : Theorem 10.49s
% Output     : CNFRefutation 10.49s
% Verified   : 
% Statistics : Number of formulae       :  157 ( 612 expanded)
%              Number of leaves         :   46 ( 239 expanded)
%              Depth                    :   19
%              Number of atoms          :  304 (1524 expanded)
%              Number of equality atoms :   76 ( 484 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(v1_partfun1,type,(
    v1_partfun1: ( $i * $i ) > $o )).

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

tff(f_164,negated_conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

tff(f_92,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => v1_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

tff(f_98,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => ( v4_relat_1(C,A)
        & v5_relat_1(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_relat_1(B)
        & v4_relat_1(B,A) )
     => B = k7_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

tff(f_138,axiom,(
    ! [A] : k6_partfun1(A) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k7_relat_1(B,A) = k5_relat_1(k6_relat_1(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

tff(f_61,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v2_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

tff(f_57,axiom,(
    ! [A] :
      ( v1_relat_1(k6_relat_1(A))
      & v1_funct_1(k6_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc3_funct_1)).

tff(f_88,axiom,(
    ! [A] : k2_funct_1(k6_relat_1(A)) = k6_relat_1(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_1)).

tff(f_126,axiom,(
    ! [A] :
      ( v1_partfun1(k6_partfun1(A),A)
      & m1_subset_1(k6_partfun1(A),k1_zfmisc_1(k2_zfmisc_1(A,A))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

tff(f_71,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v2_funct_1(A)
       => ( k5_relat_1(A,k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))
          & k5_relat_1(k2_funct_1(A),A) = k6_relat_1(k2_relat_1(A)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

tff(f_136,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => k1_partfun1(A,B,C,D,E,F) = k5_relat_1(E,F) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

tff(f_122,axiom,(
    ! [A,B,C,D,E,F] :
      ( ( v1_funct_1(E)
        & m1_subset_1(E,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & v1_funct_1(F)
        & m1_subset_1(F,k1_zfmisc_1(k2_zfmisc_1(C,D))) )
     => ( v1_funct_1(k1_partfun1(A,B,C,D,E,F))
        & m1_subset_1(k1_partfun1(A,B,C,D,E,F),k1_zfmisc_1(k2_zfmisc_1(A,D))) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

tff(f_110,axiom,(
    ! [A,B,C,D] :
      ( ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
        & m1_subset_1(D,k1_zfmisc_1(k2_zfmisc_1(A,B))) )
     => ( r2_relset_1(A,B,C,D)
      <=> C = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

tff(f_53,axiom,(
    ! [A] :
      ( ( v1_relat_1(A)
        & v1_funct_1(A) )
     => ( v1_relat_1(k2_funct_1(A))
        & v1_funct_1(k2_funct_1(A)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

tff(f_102,axiom,(
    ! [A,B,C] :
      ( m1_subset_1(C,k1_zfmisc_1(k2_zfmisc_1(A,B)))
     => k2_relset_1(A,B,C) = k2_relat_1(C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

tff(f_41,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ! [B] :
          ( v1_relat_1(B)
         => ! [C] :
              ( v1_relat_1(C)
             => k5_relat_1(k5_relat_1(A,B),C) = k5_relat_1(A,k5_relat_1(B,C)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_funct_1)).

tff(c_52,plain,(
    k2_funct_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_70,plain,(
    m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_122,plain,(
    ! [C_57,A_58,B_59] :
      ( v1_relat_1(C_57)
      | ~ m1_subset_1(C_57,k1_zfmisc_1(k2_zfmisc_1(A_58,B_59))) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_134,plain,(
    v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_122])).

tff(c_74,plain,(
    v1_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_58,plain,(
    v2_funct_1('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_145,plain,(
    ! [C_62,A_63,B_64] :
      ( v4_relat_1(C_62,A_63)
      | ~ m1_subset_1(C_62,k1_zfmisc_1(k2_zfmisc_1(A_63,B_64))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_156,plain,(
    v4_relat_1('#skF_3','#skF_1') ),
    inference(resolution,[status(thm)],[c_70,c_145])).

tff(c_159,plain,(
    ! [B_66,A_67] :
      ( k7_relat_1(B_66,A_67) = B_66
      | ~ v4_relat_1(B_66,A_67)
      | ~ v1_relat_1(B_66) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_168,plain,
    ( k7_relat_1('#skF_3','#skF_1') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_156,c_159])).

tff(c_177,plain,(
    k7_relat_1('#skF_3','#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_168])).

tff(c_50,plain,(
    ! [A_46] : k6_relat_1(A_46) = k6_partfun1(A_46) ),
    inference(cnfTransformation,[status(thm)],[f_138])).

tff(c_6,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_relat_1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_82,plain,(
    ! [A_10,B_11] :
      ( k5_relat_1(k6_partfun1(A_10),B_11) = k7_relat_1(B_11,A_10)
      | ~ v1_relat_1(B_11) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_6])).

tff(c_16,plain,(
    ! [A_14] : v1_relat_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [A_14] : v1_relat_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_14,plain,(
    ! [A_13] : v1_funct_1(k6_relat_1(A_13)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_80,plain,(
    ! [A_13] : v1_funct_1(k6_partfun1(A_13)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_14])).

tff(c_18,plain,(
    ! [A_14] : v2_funct_1(k6_relat_1(A_14)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_78,plain,(
    ! [A_14] : v2_funct_1(k6_partfun1(A_14)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_26,plain,(
    ! [A_19] : k2_funct_1(k6_relat_1(A_19)) = k6_relat_1(A_19) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_75,plain,(
    ! [A_19] : k2_funct_1(k6_partfun1(A_19)) = k6_partfun1(A_19) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_50,c_26])).

tff(c_46,plain,(
    ! [A_39] : m1_subset_1(k6_partfun1(A_39),k1_zfmisc_1(k2_zfmisc_1(A_39,A_39))) ),
    inference(cnfTransformation,[status(thm)],[f_126])).

tff(c_155,plain,(
    ! [A_39] : v4_relat_1(k6_partfun1(A_39),A_39) ),
    inference(resolution,[status(thm)],[c_46,c_145])).

tff(c_162,plain,(
    ! [A_39] :
      ( k7_relat_1(k6_partfun1(A_39),A_39) = k6_partfun1(A_39)
      | ~ v1_relat_1(k6_partfun1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_155,c_159])).

tff(c_171,plain,(
    ! [A_39] : k7_relat_1(k6_partfun1(A_39),A_39) = k6_partfun1(A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_162])).

tff(c_22,plain,(
    ! [A_15] :
      ( k5_relat_1(A_15,k2_funct_1(A_15)) = k6_relat_1(k1_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_251,plain,(
    ! [A_81] :
      ( k5_relat_1(A_81,k2_funct_1(A_81)) = k6_partfun1(k1_relat_1(A_81))
      | ~ v2_funct_1(A_81)
      | ~ v1_funct_1(A_81)
      | ~ v1_relat_1(A_81) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_22])).

tff(c_258,plain,(
    ! [A_10] :
      ( k7_relat_1(k2_funct_1(k6_partfun1(A_10)),A_10) = k6_partfun1(k1_relat_1(k6_partfun1(A_10)))
      | ~ v1_relat_1(k2_funct_1(k6_partfun1(A_10)))
      | ~ v2_funct_1(k6_partfun1(A_10))
      | ~ v1_funct_1(k6_partfun1(A_10))
      | ~ v1_relat_1(k6_partfun1(A_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_251,c_82])).

tff(c_271,plain,(
    ! [A_10] : k6_partfun1(k1_relat_1(k6_partfun1(A_10))) = k6_partfun1(A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_80,c_78,c_79,c_75,c_171,c_75,c_258])).

tff(c_1667,plain,(
    ! [F_166,E_163,D_165,C_167,A_164,B_168] :
      ( k1_partfun1(A_164,B_168,C_167,D_165,E_163,F_166) = k5_relat_1(E_163,F_166)
      | ~ m1_subset_1(F_166,k1_zfmisc_1(k2_zfmisc_1(C_167,D_165)))
      | ~ v1_funct_1(F_166)
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_168)))
      | ~ v1_funct_1(E_163) ) ),
    inference(cnfTransformation,[status(thm)],[f_136])).

tff(c_1675,plain,(
    ! [A_164,B_168,E_163] :
      ( k1_partfun1(A_164,B_168,'#skF_1','#skF_2',E_163,'#skF_3') = k5_relat_1(E_163,'#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_168)))
      | ~ v1_funct_1(E_163) ) ),
    inference(resolution,[status(thm)],[c_70,c_1667])).

tff(c_2209,plain,(
    ! [A_193,B_194,E_195] :
      ( k1_partfun1(A_193,B_194,'#skF_1','#skF_2',E_195,'#skF_3') = k5_relat_1(E_195,'#skF_3')
      | ~ m1_subset_1(E_195,k1_zfmisc_1(k2_zfmisc_1(A_193,B_194)))
      | ~ v1_funct_1(E_195) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1675])).

tff(c_2224,plain,(
    ! [A_39] :
      ( k1_partfun1(A_39,A_39,'#skF_1','#skF_2',k6_partfun1(A_39),'#skF_3') = k5_relat_1(k6_partfun1(A_39),'#skF_3')
      | ~ v1_funct_1(k6_partfun1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2209])).

tff(c_2243,plain,(
    ! [A_39] : k1_partfun1(A_39,A_39,'#skF_1','#skF_2',k6_partfun1(A_39),'#skF_3') = k5_relat_1(k6_partfun1(A_39),'#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2224])).

tff(c_1851,plain,(
    ! [D_181,E_178,A_177,F_180,B_182,C_179] :
      ( m1_subset_1(k1_partfun1(A_177,B_182,C_179,D_181,E_178,F_180),k1_zfmisc_1(k2_zfmisc_1(A_177,D_181)))
      | ~ m1_subset_1(F_180,k1_zfmisc_1(k2_zfmisc_1(C_179,D_181)))
      | ~ v1_funct_1(F_180)
      | ~ m1_subset_1(E_178,k1_zfmisc_1(k2_zfmisc_1(A_177,B_182)))
      | ~ v1_funct_1(E_178) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_32,plain,(
    ! [C_25,A_23,B_24] :
      ( v4_relat_1(C_25,A_23)
      | ~ m1_subset_1(C_25,k1_zfmisc_1(k2_zfmisc_1(A_23,B_24))) ) ),
    inference(cnfTransformation,[status(thm)],[f_98])).

tff(c_3719,plain,(
    ! [C_244,E_249,D_248,F_245,A_247,B_246] :
      ( v4_relat_1(k1_partfun1(A_247,B_246,C_244,D_248,E_249,F_245),A_247)
      | ~ m1_subset_1(F_245,k1_zfmisc_1(k2_zfmisc_1(C_244,D_248)))
      | ~ v1_funct_1(F_245)
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246)))
      | ~ v1_funct_1(E_249) ) ),
    inference(resolution,[status(thm)],[c_1851,c_32])).

tff(c_3739,plain,(
    ! [A_247,B_246,E_249] :
      ( v4_relat_1(k1_partfun1(A_247,B_246,'#skF_1','#skF_2',E_249,'#skF_3'),A_247)
      | ~ v1_funct_1('#skF_3')
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246)))
      | ~ v1_funct_1(E_249) ) ),
    inference(resolution,[status(thm)],[c_70,c_3719])).

tff(c_4784,plain,(
    ! [A_283,B_284,E_285] :
      ( v4_relat_1(k1_partfun1(A_283,B_284,'#skF_1','#skF_2',E_285,'#skF_3'),A_283)
      | ~ m1_subset_1(E_285,k1_zfmisc_1(k2_zfmisc_1(A_283,B_284)))
      | ~ v1_funct_1(E_285) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_3739])).

tff(c_4802,plain,(
    ! [A_39] :
      ( v4_relat_1(k1_partfun1(A_39,A_39,'#skF_1','#skF_2',k6_partfun1(A_39),'#skF_3'),A_39)
      | ~ v1_funct_1(k6_partfun1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_46,c_4784])).

tff(c_4831,plain,(
    ! [A_39] : v4_relat_1(k1_partfun1(A_39,A_39,'#skF_1','#skF_2',k6_partfun1(A_39),'#skF_3'),A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_4802])).

tff(c_10845,plain,(
    ! [A_418] : v4_relat_1(k5_relat_1(k6_partfun1(A_418),'#skF_3'),A_418) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2243,c_4831])).

tff(c_11344,plain,(
    ! [A_434] : v4_relat_1(k5_relat_1(k6_partfun1(A_434),'#skF_3'),k1_relat_1(k6_partfun1(A_434))) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_10845])).

tff(c_11387,plain,(
    ! [A_10] :
      ( v4_relat_1(k7_relat_1('#skF_3',A_10),k1_relat_1(k6_partfun1(A_10)))
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_11344])).

tff(c_11403,plain,(
    ! [A_435] : v4_relat_1(k7_relat_1('#skF_3',A_435),k1_relat_1(k6_partfun1(A_435))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_11387])).

tff(c_11429,plain,(
    v4_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_177,c_11403])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( k7_relat_1(B_2,A_1) = B_2
      | ~ v4_relat_1(B_2,A_1)
      | ~ v1_relat_1(B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_11440,plain,
    ( k7_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_11429,c_2])).

tff(c_11443,plain,(
    k7_relat_1('#skF_3',k1_relat_1(k6_partfun1('#skF_1'))) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_11440])).

tff(c_277,plain,(
    ! [A_82] : k6_partfun1(k1_relat_1(k6_partfun1(A_82))) = k6_partfun1(A_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_80,c_78,c_79,c_75,c_171,c_75,c_258])).

tff(c_304,plain,(
    ! [B_11,A_82] :
      ( k7_relat_1(B_11,k1_relat_1(k6_partfun1(A_82))) = k5_relat_1(k6_partfun1(A_82),B_11)
      | ~ v1_relat_1(B_11) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_277,c_82])).

tff(c_11474,plain,
    ( k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3'
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11443,c_304])).

tff(c_11490,plain,(
    k5_relat_1(k6_partfun1('#skF_1'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_11474])).

tff(c_64,plain,(
    m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1'))) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_135,plain,(
    v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_64,c_122])).

tff(c_157,plain,(
    v4_relat_1('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_64,c_145])).

tff(c_165,plain,
    ( k7_relat_1('#skF_4','#skF_2') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_157,c_159])).

tff(c_174,plain,(
    k7_relat_1('#skF_4','#skF_2') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_165])).

tff(c_68,plain,(
    v1_funct_1('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_1677,plain,(
    ! [A_164,B_168,E_163] :
      ( k1_partfun1(A_164,B_168,'#skF_2','#skF_1',E_163,'#skF_4') = k5_relat_1(E_163,'#skF_4')
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_163,k1_zfmisc_1(k2_zfmisc_1(A_164,B_168)))
      | ~ v1_funct_1(E_163) ) ),
    inference(resolution,[status(thm)],[c_64,c_1667])).

tff(c_2033,plain,(
    ! [A_188,B_189,E_190] :
      ( k1_partfun1(A_188,B_189,'#skF_2','#skF_1',E_190,'#skF_4') = k5_relat_1(E_190,'#skF_4')
      | ~ m1_subset_1(E_190,k1_zfmisc_1(k2_zfmisc_1(A_188,B_189)))
      | ~ v1_funct_1(E_190) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_1677])).

tff(c_2045,plain,(
    ! [A_39] :
      ( k1_partfun1(A_39,A_39,'#skF_2','#skF_1',k6_partfun1(A_39),'#skF_4') = k5_relat_1(k6_partfun1(A_39),'#skF_4')
      | ~ v1_funct_1(k6_partfun1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_46,c_2033])).

tff(c_2061,plain,(
    ! [A_39] : k1_partfun1(A_39,A_39,'#skF_2','#skF_1',k6_partfun1(A_39),'#skF_4') = k5_relat_1(k6_partfun1(A_39),'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_2045])).

tff(c_3741,plain,(
    ! [A_247,B_246,E_249] :
      ( v4_relat_1(k1_partfun1(A_247,B_246,'#skF_2','#skF_1',E_249,'#skF_4'),A_247)
      | ~ v1_funct_1('#skF_4')
      | ~ m1_subset_1(E_249,k1_zfmisc_1(k2_zfmisc_1(A_247,B_246)))
      | ~ v1_funct_1(E_249) ) ),
    inference(resolution,[status(thm)],[c_64,c_3719])).

tff(c_5063,plain,(
    ! [A_289,B_290,E_291] :
      ( v4_relat_1(k1_partfun1(A_289,B_290,'#skF_2','#skF_1',E_291,'#skF_4'),A_289)
      | ~ m1_subset_1(E_291,k1_zfmisc_1(k2_zfmisc_1(A_289,B_290)))
      | ~ v1_funct_1(E_291) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_68,c_3741])).

tff(c_5081,plain,(
    ! [A_39] :
      ( v4_relat_1(k1_partfun1(A_39,A_39,'#skF_2','#skF_1',k6_partfun1(A_39),'#skF_4'),A_39)
      | ~ v1_funct_1(k6_partfun1(A_39)) ) ),
    inference(resolution,[status(thm)],[c_46,c_5063])).

tff(c_5110,plain,(
    ! [A_39] : v4_relat_1(k1_partfun1(A_39,A_39,'#skF_2','#skF_1',k6_partfun1(A_39),'#skF_4'),A_39) ),
    inference(demodulation,[status(thm),theory(equality)],[c_80,c_5081])).

tff(c_8625,plain,(
    ! [A_358] : v4_relat_1(k5_relat_1(k6_partfun1(A_358),'#skF_4'),A_358) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2061,c_5110])).

tff(c_8896,plain,(
    ! [A_371] : v4_relat_1(k5_relat_1(k6_partfun1(A_371),'#skF_4'),k1_relat_1(k6_partfun1(A_371))) ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_8625])).

tff(c_8939,plain,(
    ! [A_10] :
      ( v4_relat_1(k7_relat_1('#skF_4',A_10),k1_relat_1(k6_partfun1(A_10)))
      | ~ v1_relat_1('#skF_4') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_8896])).

tff(c_8955,plain,(
    ! [A_372] : v4_relat_1(k7_relat_1('#skF_4',A_372),k1_relat_1(k6_partfun1(A_372))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_8939])).

tff(c_8981,plain,(
    v4_relat_1('#skF_4',k1_relat_1(k6_partfun1('#skF_2'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_174,c_8955])).

tff(c_8992,plain,
    ( k7_relat_1('#skF_4',k1_relat_1(k6_partfun1('#skF_2'))) = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(resolution,[status(thm)],[c_8981,c_2])).

tff(c_8995,plain,(
    k7_relat_1('#skF_4',k1_relat_1(k6_partfun1('#skF_2'))) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_8992])).

tff(c_9014,plain,
    ( k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4'
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_8995,c_304])).

tff(c_9028,plain,(
    k5_relat_1(k6_partfun1('#skF_2'),'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_9014])).

tff(c_1338,plain,(
    ! [E_140,B_144,A_139,F_142,C_141,D_143] :
      ( m1_subset_1(k1_partfun1(A_139,B_144,C_141,D_143,E_140,F_142),k1_zfmisc_1(k2_zfmisc_1(A_139,D_143)))
      | ~ m1_subset_1(F_142,k1_zfmisc_1(k2_zfmisc_1(C_141,D_143)))
      | ~ v1_funct_1(F_142)
      | ~ m1_subset_1(E_140,k1_zfmisc_1(k2_zfmisc_1(A_139,B_144)))
      | ~ v1_funct_1(E_140) ) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_60,plain,(
    r2_relset_1('#skF_1','#skF_1',k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k6_partfun1('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_621,plain,(
    ! [D_95,C_96,A_97,B_98] :
      ( D_95 = C_96
      | ~ r2_relset_1(A_97,B_98,C_96,D_95)
      | ~ m1_subset_1(D_95,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98)))
      | ~ m1_subset_1(C_96,k1_zfmisc_1(k2_zfmisc_1(A_97,B_98))) ) ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_629,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k6_partfun1('#skF_1'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1')))
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(resolution,[status(thm)],[c_60,c_621])).

tff(c_644,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1')
    | ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_629])).

tff(c_938,plain,(
    ~ m1_subset_1(k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4'),k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_1'))) ),
    inference(splitLeft,[status(thm)],[c_644])).

tff(c_1349,plain,
    ( ~ m1_subset_1('#skF_4',k1_zfmisc_1(k2_zfmisc_1('#skF_2','#skF_1')))
    | ~ v1_funct_1('#skF_4')
    | ~ m1_subset_1('#skF_3',k1_zfmisc_1(k2_zfmisc_1('#skF_1','#skF_2')))
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_1338,c_938])).

tff(c_1372,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_70,c_68,c_64,c_1349])).

tff(c_1373,plain,(
    k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(splitRight,[status(thm)],[c_644])).

tff(c_2048,plain,
    ( k1_partfun1('#skF_1','#skF_2','#skF_2','#skF_1','#skF_3','#skF_4') = k5_relat_1('#skF_3','#skF_4')
    | ~ v1_funct_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_2033])).

tff(c_2064,plain,(
    k5_relat_1('#skF_3','#skF_4') = k6_partfun1('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_1373,c_2048])).

tff(c_10,plain,(
    ! [A_12] :
      ( v1_relat_1(k2_funct_1(A_12))
      | ~ v1_funct_1(A_12)
      | ~ v1_relat_1(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_164])).

tff(c_220,plain,(
    ! [A_77,B_78,C_79] :
      ( k2_relset_1(A_77,B_78,C_79) = k2_relat_1(C_79)
      | ~ m1_subset_1(C_79,k1_zfmisc_1(k2_zfmisc_1(A_77,B_78))) ) ),
    inference(cnfTransformation,[status(thm)],[f_102])).

tff(c_226,plain,(
    k2_relset_1('#skF_1','#skF_2','#skF_3') = k2_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_220])).

tff(c_232,plain,(
    k2_relat_1('#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_226])).

tff(c_20,plain,(
    ! [A_15] :
      ( k5_relat_1(k2_funct_1(A_15),A_15) = k6_relat_1(k2_relat_1(A_15))
      | ~ v2_funct_1(A_15)
      | ~ v1_funct_1(A_15)
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_455,plain,(
    ! [A_91] :
      ( k5_relat_1(k2_funct_1(A_91),A_91) = k6_partfun1(k2_relat_1(A_91))
      | ~ v2_funct_1(A_91)
      | ~ v1_funct_1(A_91)
      | ~ v1_relat_1(A_91) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_20])).

tff(c_4,plain,(
    ! [A_3,B_7,C_9] :
      ( k5_relat_1(k5_relat_1(A_3,B_7),C_9) = k5_relat_1(A_3,k5_relat_1(B_7,C_9))
      | ~ v1_relat_1(C_9)
      | ~ v1_relat_1(B_7)
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2907,plain,(
    ! [A_219,C_220] :
      ( k5_relat_1(k6_partfun1(k2_relat_1(A_219)),C_220) = k5_relat_1(k2_funct_1(A_219),k5_relat_1(A_219,C_220))
      | ~ v1_relat_1(C_220)
      | ~ v1_relat_1(A_219)
      | ~ v1_relat_1(k2_funct_1(A_219))
      | ~ v2_funct_1(A_219)
      | ~ v1_funct_1(A_219)
      | ~ v1_relat_1(A_219) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_455,c_4])).

tff(c_3050,plain,(
    ! [C_220] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_220)) = k5_relat_1(k6_partfun1('#skF_2'),C_220)
      | ~ v1_relat_1(C_220)
      | ~ v1_relat_1('#skF_3')
      | ~ v1_relat_1(k2_funct_1('#skF_3'))
      | ~ v2_funct_1('#skF_3')
      | ~ v1_funct_1('#skF_3')
      | ~ v1_relat_1('#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_2907])).

tff(c_3106,plain,(
    ! [C_220] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_220)) = k5_relat_1(k6_partfun1('#skF_2'),C_220)
      | ~ v1_relat_1(C_220)
      | ~ v1_relat_1(k2_funct_1('#skF_3')) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_58,c_134,c_3050])).

tff(c_11615,plain,(
    ~ v1_relat_1(k2_funct_1('#skF_3')) ),
    inference(splitLeft,[status(thm)],[c_3106])).

tff(c_11618,plain,
    ( ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(resolution,[status(thm)],[c_10,c_11615])).

tff(c_11622,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_11618])).

tff(c_11851,plain,(
    ! [C_439] :
      ( k5_relat_1(k2_funct_1('#skF_3'),k5_relat_1('#skF_3',C_439)) = k5_relat_1(k6_partfun1('#skF_2'),C_439)
      | ~ v1_relat_1(C_439) ) ),
    inference(splitRight,[status(thm)],[c_3106])).

tff(c_11908,plain,
    ( k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = k5_relat_1(k6_partfun1('#skF_2'),'#skF_4')
    | ~ v1_relat_1('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_2064,c_11851])).

tff(c_11942,plain,(
    k5_relat_1(k2_funct_1('#skF_3'),k6_partfun1('#skF_1')) = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_135,c_9028,c_11908])).

tff(c_775,plain,(
    ! [B_104,A_105] :
      ( k5_relat_1(k2_funct_1(B_104),k2_funct_1(A_105)) = k2_funct_1(k5_relat_1(A_105,B_104))
      | ~ v2_funct_1(B_104)
      | ~ v2_funct_1(A_105)
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_funct_1(A_105)
      | ~ v1_relat_1(A_105) ) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_806,plain,(
    ! [B_104,A_19] :
      ( k5_relat_1(k2_funct_1(B_104),k6_partfun1(A_19)) = k2_funct_1(k5_relat_1(k6_partfun1(A_19),B_104))
      | ~ v2_funct_1(B_104)
      | ~ v2_funct_1(k6_partfun1(A_19))
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104)
      | ~ v1_funct_1(k6_partfun1(A_19))
      | ~ v1_relat_1(k6_partfun1(A_19)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_775])).

tff(c_812,plain,(
    ! [B_104,A_19] :
      ( k5_relat_1(k2_funct_1(B_104),k6_partfun1(A_19)) = k2_funct_1(k5_relat_1(k6_partfun1(A_19),B_104))
      | ~ v2_funct_1(B_104)
      | ~ v1_funct_1(B_104)
      | ~ v1_relat_1(B_104) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_79,c_80,c_78,c_806])).

tff(c_11960,plain,
    ( k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'),'#skF_3')) = '#skF_4'
    | ~ v2_funct_1('#skF_3')
    | ~ v1_funct_1('#skF_3')
    | ~ v1_relat_1('#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_11942,c_812])).

tff(c_11981,plain,(
    k2_funct_1('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_134,c_74,c_58,c_11490,c_11960])).

tff(c_11983,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_11981])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:16:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.49/4.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/4.14  
% 10.49/4.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/4.14  %$ r2_relset_1 > v1_funct_2 > v5_relat_1 > v4_relat_1 > v1_partfun1 > m1_subset_1 > v2_funct_1 > v1_relat_1 > v1_funct_1 > k1_partfun1 > k2_relset_1 > k7_relat_1 > k5_relat_1 > k2_zfmisc_1 > #nlpp > k6_relat_1 > k6_partfun1 > k2_relat_1 > k2_funct_1 > k1_zfmisc_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.49/4.14  
% 10.49/4.14  %Foreground sorts:
% 10.49/4.14  
% 10.49/4.14  
% 10.49/4.14  %Background operators:
% 10.49/4.14  
% 10.49/4.14  
% 10.49/4.14  %Foreground operators:
% 10.49/4.14  tff(k2_relset_1, type, k2_relset_1: ($i * $i * $i) > $i).
% 10.49/4.14  tff(v1_funct_1, type, v1_funct_1: $i > $o).
% 10.49/4.14  tff(k2_funct_1, type, k2_funct_1: $i > $i).
% 10.49/4.14  tff(v2_funct_1, type, v2_funct_1: $i > $o).
% 10.49/4.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.49/4.14  tff(r2_relset_1, type, r2_relset_1: ($i * $i * $i * $i) > $o).
% 10.49/4.14  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 10.49/4.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.49/4.14  tff(k5_relat_1, type, k5_relat_1: ($i * $i) > $i).
% 10.49/4.14  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 10.49/4.14  tff(k1_partfun1, type, k1_partfun1: ($i * $i * $i * $i * $i * $i) > $i).
% 10.49/4.14  tff(v1_funct_2, type, v1_funct_2: ($i * $i * $i) > $o).
% 10.49/4.14  tff('#skF_2', type, '#skF_2': $i).
% 10.49/4.14  tff(v1_partfun1, type, v1_partfun1: ($i * $i) > $o).
% 10.49/4.14  tff('#skF_3', type, '#skF_3': $i).
% 10.49/4.14  tff('#skF_1', type, '#skF_1': $i).
% 10.49/4.14  tff(v5_relat_1, type, v5_relat_1: ($i * $i) > $o).
% 10.49/4.14  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 10.49/4.14  tff(k6_partfun1, type, k6_partfun1: $i > $i).
% 10.49/4.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.49/4.14  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 10.49/4.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.49/4.14  tff('#skF_4', type, '#skF_4': $i).
% 10.49/4.14  tff(k6_relat_1, type, k6_relat_1: $i > $i).
% 10.49/4.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.49/4.14  tff(v4_relat_1, type, v4_relat_1: ($i * $i) > $o).
% 10.49/4.14  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 10.49/4.14  tff(m1_subset_1, type, m1_subset_1: ($i * $i) > $o).
% 10.49/4.14  
% 10.49/4.17  tff(f_164, negated_conjecture, ~(![A, B, C]: (((v1_funct_1(C) & v1_funct_2(C, A, B)) & m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (![D]: (((v1_funct_1(D) & v1_funct_2(D, B, A)) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(B, A)))) => ((((k2_relset_1(A, B, C) = B) & r2_relset_1(A, A, k1_partfun1(A, B, B, A, C, D), k6_partfun1(A))) & v2_funct_1(C)) => (((A = k1_xboole_0) | (B = k1_xboole_0)) | (D = k2_funct_1(C)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_funct_2)).
% 10.49/4.17  tff(f_92, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => v1_relat_1(C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc1_relset_1)).
% 10.49/4.17  tff(f_98, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (v4_relat_1(C, A) & v5_relat_1(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', cc2_relset_1)).
% 10.49/4.17  tff(f_31, axiom, (![A, B]: ((v1_relat_1(B) & v4_relat_1(B, A)) => (B = k7_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t209_relat_1)).
% 10.49/4.17  tff(f_138, axiom, (![A]: (k6_partfun1(A) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k6_partfun1)).
% 10.49/4.17  tff(f_45, axiom, (![A, B]: (v1_relat_1(B) => (k7_relat_1(B, A) = k5_relat_1(k6_relat_1(A), B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_relat_1)).
% 10.49/4.17  tff(f_61, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v2_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc4_funct_1)).
% 10.49/4.17  tff(f_57, axiom, (![A]: (v1_relat_1(k6_relat_1(A)) & v1_funct_1(k6_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc3_funct_1)).
% 10.49/4.17  tff(f_88, axiom, (![A]: (k2_funct_1(k6_relat_1(A)) = k6_relat_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_funct_1)).
% 10.49/4.17  tff(f_126, axiom, (![A]: (v1_partfun1(k6_partfun1(A), A) & m1_subset_1(k6_partfun1(A), k1_zfmisc_1(k2_zfmisc_1(A, A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k6_partfun1)).
% 10.49/4.17  tff(f_71, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v2_funct_1(A) => ((k5_relat_1(A, k2_funct_1(A)) = k6_relat_1(k1_relat_1(A))) & (k5_relat_1(k2_funct_1(A), A) = k6_relat_1(k2_relat_1(A))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t61_funct_1)).
% 10.49/4.17  tff(f_136, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (k1_partfun1(A, B, C, D, E, F) = k5_relat_1(E, F)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k1_partfun1)).
% 10.49/4.17  tff(f_122, axiom, (![A, B, C, D, E, F]: ((((v1_funct_1(E) & m1_subset_1(E, k1_zfmisc_1(k2_zfmisc_1(A, B)))) & v1_funct_1(F)) & m1_subset_1(F, k1_zfmisc_1(k2_zfmisc_1(C, D)))) => (v1_funct_1(k1_partfun1(A, B, C, D, E, F)) & m1_subset_1(k1_partfun1(A, B, C, D, E, F), k1_zfmisc_1(k2_zfmisc_1(A, D)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k1_partfun1)).
% 10.49/4.17  tff(f_110, axiom, (![A, B, C, D]: ((m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) & m1_subset_1(D, k1_zfmisc_1(k2_zfmisc_1(A, B)))) => (r2_relset_1(A, B, C, D) <=> (C = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_r2_relset_1)).
% 10.49/4.17  tff(f_53, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (v1_relat_1(k2_funct_1(A)) & v1_funct_1(k2_funct_1(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', dt_k2_funct_1)).
% 10.49/4.17  tff(f_102, axiom, (![A, B, C]: (m1_subset_1(C, k1_zfmisc_1(k2_zfmisc_1(A, B))) => (k2_relset_1(A, B, C) = k2_relat_1(C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', redefinition_k2_relset_1)).
% 10.49/4.17  tff(f_41, axiom, (![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (![C]: (v1_relat_1(C) => (k5_relat_1(k5_relat_1(A, B), C) = k5_relat_1(A, k5_relat_1(B, C))))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_relat_1)).
% 10.49/4.17  tff(f_86, axiom, (![A]: ((v1_relat_1(A) & v1_funct_1(A)) => (![B]: ((v1_relat_1(B) & v1_funct_1(B)) => ((v2_funct_1(A) & v2_funct_1(B)) => (k2_funct_1(k5_relat_1(A, B)) = k5_relat_1(k2_funct_1(B), k2_funct_1(A)))))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_funct_1)).
% 10.49/4.17  tff(c_52, plain, (k2_funct_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_70, plain, (m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_122, plain, (![C_57, A_58, B_59]: (v1_relat_1(C_57) | ~m1_subset_1(C_57, k1_zfmisc_1(k2_zfmisc_1(A_58, B_59))))), inference(cnfTransformation, [status(thm)], [f_92])).
% 10.49/4.17  tff(c_134, plain, (v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_122])).
% 10.49/4.17  tff(c_74, plain, (v1_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_58, plain, (v2_funct_1('#skF_3')), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_145, plain, (![C_62, A_63, B_64]: (v4_relat_1(C_62, A_63) | ~m1_subset_1(C_62, k1_zfmisc_1(k2_zfmisc_1(A_63, B_64))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.49/4.17  tff(c_156, plain, (v4_relat_1('#skF_3', '#skF_1')), inference(resolution, [status(thm)], [c_70, c_145])).
% 10.49/4.17  tff(c_159, plain, (![B_66, A_67]: (k7_relat_1(B_66, A_67)=B_66 | ~v4_relat_1(B_66, A_67) | ~v1_relat_1(B_66))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.49/4.17  tff(c_168, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_156, c_159])).
% 10.49/4.17  tff(c_177, plain, (k7_relat_1('#skF_3', '#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_168])).
% 10.49/4.17  tff(c_50, plain, (![A_46]: (k6_relat_1(A_46)=k6_partfun1(A_46))), inference(cnfTransformation, [status(thm)], [f_138])).
% 10.49/4.17  tff(c_6, plain, (![A_10, B_11]: (k5_relat_1(k6_relat_1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.49/4.17  tff(c_82, plain, (![A_10, B_11]: (k5_relat_1(k6_partfun1(A_10), B_11)=k7_relat_1(B_11, A_10) | ~v1_relat_1(B_11))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_6])).
% 10.49/4.17  tff(c_16, plain, (![A_14]: (v1_relat_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.49/4.17  tff(c_79, plain, (![A_14]: (v1_relat_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_16])).
% 10.49/4.17  tff(c_14, plain, (![A_13]: (v1_funct_1(k6_relat_1(A_13)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.49/4.17  tff(c_80, plain, (![A_13]: (v1_funct_1(k6_partfun1(A_13)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_14])).
% 10.49/4.17  tff(c_18, plain, (![A_14]: (v2_funct_1(k6_relat_1(A_14)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 10.49/4.17  tff(c_78, plain, (![A_14]: (v2_funct_1(k6_partfun1(A_14)))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_18])).
% 10.49/4.17  tff(c_26, plain, (![A_19]: (k2_funct_1(k6_relat_1(A_19))=k6_relat_1(A_19))), inference(cnfTransformation, [status(thm)], [f_88])).
% 10.49/4.17  tff(c_75, plain, (![A_19]: (k2_funct_1(k6_partfun1(A_19))=k6_partfun1(A_19))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_50, c_26])).
% 10.49/4.17  tff(c_46, plain, (![A_39]: (m1_subset_1(k6_partfun1(A_39), k1_zfmisc_1(k2_zfmisc_1(A_39, A_39))))), inference(cnfTransformation, [status(thm)], [f_126])).
% 10.49/4.17  tff(c_155, plain, (![A_39]: (v4_relat_1(k6_partfun1(A_39), A_39))), inference(resolution, [status(thm)], [c_46, c_145])).
% 10.49/4.17  tff(c_162, plain, (![A_39]: (k7_relat_1(k6_partfun1(A_39), A_39)=k6_partfun1(A_39) | ~v1_relat_1(k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_155, c_159])).
% 10.49/4.17  tff(c_171, plain, (![A_39]: (k7_relat_1(k6_partfun1(A_39), A_39)=k6_partfun1(A_39))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_162])).
% 10.49/4.17  tff(c_22, plain, (![A_15]: (k5_relat_1(A_15, k2_funct_1(A_15))=k6_relat_1(k1_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.49/4.17  tff(c_251, plain, (![A_81]: (k5_relat_1(A_81, k2_funct_1(A_81))=k6_partfun1(k1_relat_1(A_81)) | ~v2_funct_1(A_81) | ~v1_funct_1(A_81) | ~v1_relat_1(A_81))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_22])).
% 10.49/4.17  tff(c_258, plain, (![A_10]: (k7_relat_1(k2_funct_1(k6_partfun1(A_10)), A_10)=k6_partfun1(k1_relat_1(k6_partfun1(A_10))) | ~v1_relat_1(k2_funct_1(k6_partfun1(A_10))) | ~v2_funct_1(k6_partfun1(A_10)) | ~v1_funct_1(k6_partfun1(A_10)) | ~v1_relat_1(k6_partfun1(A_10)))), inference(superposition, [status(thm), theory('equality')], [c_251, c_82])).
% 10.49/4.17  tff(c_271, plain, (![A_10]: (k6_partfun1(k1_relat_1(k6_partfun1(A_10)))=k6_partfun1(A_10))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_80, c_78, c_79, c_75, c_171, c_75, c_258])).
% 10.49/4.17  tff(c_1667, plain, (![F_166, E_163, D_165, C_167, A_164, B_168]: (k1_partfun1(A_164, B_168, C_167, D_165, E_163, F_166)=k5_relat_1(E_163, F_166) | ~m1_subset_1(F_166, k1_zfmisc_1(k2_zfmisc_1(C_167, D_165))) | ~v1_funct_1(F_166) | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_168))) | ~v1_funct_1(E_163))), inference(cnfTransformation, [status(thm)], [f_136])).
% 10.49/4.17  tff(c_1675, plain, (![A_164, B_168, E_163]: (k1_partfun1(A_164, B_168, '#skF_1', '#skF_2', E_163, '#skF_3')=k5_relat_1(E_163, '#skF_3') | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_168))) | ~v1_funct_1(E_163))), inference(resolution, [status(thm)], [c_70, c_1667])).
% 10.49/4.17  tff(c_2209, plain, (![A_193, B_194, E_195]: (k1_partfun1(A_193, B_194, '#skF_1', '#skF_2', E_195, '#skF_3')=k5_relat_1(E_195, '#skF_3') | ~m1_subset_1(E_195, k1_zfmisc_1(k2_zfmisc_1(A_193, B_194))) | ~v1_funct_1(E_195))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1675])).
% 10.49/4.17  tff(c_2224, plain, (![A_39]: (k1_partfun1(A_39, A_39, '#skF_1', '#skF_2', k6_partfun1(A_39), '#skF_3')=k5_relat_1(k6_partfun1(A_39), '#skF_3') | ~v1_funct_1(k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_46, c_2209])).
% 10.49/4.17  tff(c_2243, plain, (![A_39]: (k1_partfun1(A_39, A_39, '#skF_1', '#skF_2', k6_partfun1(A_39), '#skF_3')=k5_relat_1(k6_partfun1(A_39), '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2224])).
% 10.49/4.17  tff(c_1851, plain, (![D_181, E_178, A_177, F_180, B_182, C_179]: (m1_subset_1(k1_partfun1(A_177, B_182, C_179, D_181, E_178, F_180), k1_zfmisc_1(k2_zfmisc_1(A_177, D_181))) | ~m1_subset_1(F_180, k1_zfmisc_1(k2_zfmisc_1(C_179, D_181))) | ~v1_funct_1(F_180) | ~m1_subset_1(E_178, k1_zfmisc_1(k2_zfmisc_1(A_177, B_182))) | ~v1_funct_1(E_178))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.49/4.17  tff(c_32, plain, (![C_25, A_23, B_24]: (v4_relat_1(C_25, A_23) | ~m1_subset_1(C_25, k1_zfmisc_1(k2_zfmisc_1(A_23, B_24))))), inference(cnfTransformation, [status(thm)], [f_98])).
% 10.49/4.17  tff(c_3719, plain, (![C_244, E_249, D_248, F_245, A_247, B_246]: (v4_relat_1(k1_partfun1(A_247, B_246, C_244, D_248, E_249, F_245), A_247) | ~m1_subset_1(F_245, k1_zfmisc_1(k2_zfmisc_1(C_244, D_248))) | ~v1_funct_1(F_245) | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))) | ~v1_funct_1(E_249))), inference(resolution, [status(thm)], [c_1851, c_32])).
% 10.49/4.17  tff(c_3739, plain, (![A_247, B_246, E_249]: (v4_relat_1(k1_partfun1(A_247, B_246, '#skF_1', '#skF_2', E_249, '#skF_3'), A_247) | ~v1_funct_1('#skF_3') | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))) | ~v1_funct_1(E_249))), inference(resolution, [status(thm)], [c_70, c_3719])).
% 10.49/4.17  tff(c_4784, plain, (![A_283, B_284, E_285]: (v4_relat_1(k1_partfun1(A_283, B_284, '#skF_1', '#skF_2', E_285, '#skF_3'), A_283) | ~m1_subset_1(E_285, k1_zfmisc_1(k2_zfmisc_1(A_283, B_284))) | ~v1_funct_1(E_285))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_3739])).
% 10.49/4.17  tff(c_4802, plain, (![A_39]: (v4_relat_1(k1_partfun1(A_39, A_39, '#skF_1', '#skF_2', k6_partfun1(A_39), '#skF_3'), A_39) | ~v1_funct_1(k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_46, c_4784])).
% 10.49/4.17  tff(c_4831, plain, (![A_39]: (v4_relat_1(k1_partfun1(A_39, A_39, '#skF_1', '#skF_2', k6_partfun1(A_39), '#skF_3'), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_4802])).
% 10.49/4.17  tff(c_10845, plain, (![A_418]: (v4_relat_1(k5_relat_1(k6_partfun1(A_418), '#skF_3'), A_418))), inference(demodulation, [status(thm), theory('equality')], [c_2243, c_4831])).
% 10.49/4.17  tff(c_11344, plain, (![A_434]: (v4_relat_1(k5_relat_1(k6_partfun1(A_434), '#skF_3'), k1_relat_1(k6_partfun1(A_434))))), inference(superposition, [status(thm), theory('equality')], [c_271, c_10845])).
% 10.49/4.17  tff(c_11387, plain, (![A_10]: (v4_relat_1(k7_relat_1('#skF_3', A_10), k1_relat_1(k6_partfun1(A_10))) | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_11344])).
% 10.49/4.17  tff(c_11403, plain, (![A_435]: (v4_relat_1(k7_relat_1('#skF_3', A_435), k1_relat_1(k6_partfun1(A_435))))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_11387])).
% 10.49/4.17  tff(c_11429, plain, (v4_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))), inference(superposition, [status(thm), theory('equality')], [c_177, c_11403])).
% 10.49/4.17  tff(c_2, plain, (![B_2, A_1]: (k7_relat_1(B_2, A_1)=B_2 | ~v4_relat_1(B_2, A_1) | ~v1_relat_1(B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 10.49/4.17  tff(c_11440, plain, (k7_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))='#skF_3' | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_11429, c_2])).
% 10.49/4.17  tff(c_11443, plain, (k7_relat_1('#skF_3', k1_relat_1(k6_partfun1('#skF_1')))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_11440])).
% 10.49/4.17  tff(c_277, plain, (![A_82]: (k6_partfun1(k1_relat_1(k6_partfun1(A_82)))=k6_partfun1(A_82))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_80, c_78, c_79, c_75, c_171, c_75, c_258])).
% 10.49/4.17  tff(c_304, plain, (![B_11, A_82]: (k7_relat_1(B_11, k1_relat_1(k6_partfun1(A_82)))=k5_relat_1(k6_partfun1(A_82), B_11) | ~v1_relat_1(B_11))), inference(superposition, [status(thm), theory('equality')], [c_277, c_82])).
% 10.49/4.17  tff(c_11474, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3' | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11443, c_304])).
% 10.49/4.17  tff(c_11490, plain, (k5_relat_1(k6_partfun1('#skF_1'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_11474])).
% 10.49/4.17  tff(c_64, plain, (m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1')))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_135, plain, (v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_64, c_122])).
% 10.49/4.17  tff(c_157, plain, (v4_relat_1('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_64, c_145])).
% 10.49/4.17  tff(c_165, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_157, c_159])).
% 10.49/4.17  tff(c_174, plain, (k7_relat_1('#skF_4', '#skF_2')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_165])).
% 10.49/4.17  tff(c_68, plain, (v1_funct_1('#skF_4')), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_1677, plain, (![A_164, B_168, E_163]: (k1_partfun1(A_164, B_168, '#skF_2', '#skF_1', E_163, '#skF_4')=k5_relat_1(E_163, '#skF_4') | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_163, k1_zfmisc_1(k2_zfmisc_1(A_164, B_168))) | ~v1_funct_1(E_163))), inference(resolution, [status(thm)], [c_64, c_1667])).
% 10.49/4.17  tff(c_2033, plain, (![A_188, B_189, E_190]: (k1_partfun1(A_188, B_189, '#skF_2', '#skF_1', E_190, '#skF_4')=k5_relat_1(E_190, '#skF_4') | ~m1_subset_1(E_190, k1_zfmisc_1(k2_zfmisc_1(A_188, B_189))) | ~v1_funct_1(E_190))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_1677])).
% 10.49/4.17  tff(c_2045, plain, (![A_39]: (k1_partfun1(A_39, A_39, '#skF_2', '#skF_1', k6_partfun1(A_39), '#skF_4')=k5_relat_1(k6_partfun1(A_39), '#skF_4') | ~v1_funct_1(k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_46, c_2033])).
% 10.49/4.17  tff(c_2061, plain, (![A_39]: (k1_partfun1(A_39, A_39, '#skF_2', '#skF_1', k6_partfun1(A_39), '#skF_4')=k5_relat_1(k6_partfun1(A_39), '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_2045])).
% 10.49/4.17  tff(c_3741, plain, (![A_247, B_246, E_249]: (v4_relat_1(k1_partfun1(A_247, B_246, '#skF_2', '#skF_1', E_249, '#skF_4'), A_247) | ~v1_funct_1('#skF_4') | ~m1_subset_1(E_249, k1_zfmisc_1(k2_zfmisc_1(A_247, B_246))) | ~v1_funct_1(E_249))), inference(resolution, [status(thm)], [c_64, c_3719])).
% 10.49/4.17  tff(c_5063, plain, (![A_289, B_290, E_291]: (v4_relat_1(k1_partfun1(A_289, B_290, '#skF_2', '#skF_1', E_291, '#skF_4'), A_289) | ~m1_subset_1(E_291, k1_zfmisc_1(k2_zfmisc_1(A_289, B_290))) | ~v1_funct_1(E_291))), inference(demodulation, [status(thm), theory('equality')], [c_68, c_3741])).
% 10.49/4.17  tff(c_5081, plain, (![A_39]: (v4_relat_1(k1_partfun1(A_39, A_39, '#skF_2', '#skF_1', k6_partfun1(A_39), '#skF_4'), A_39) | ~v1_funct_1(k6_partfun1(A_39)))), inference(resolution, [status(thm)], [c_46, c_5063])).
% 10.49/4.17  tff(c_5110, plain, (![A_39]: (v4_relat_1(k1_partfun1(A_39, A_39, '#skF_2', '#skF_1', k6_partfun1(A_39), '#skF_4'), A_39))), inference(demodulation, [status(thm), theory('equality')], [c_80, c_5081])).
% 10.49/4.17  tff(c_8625, plain, (![A_358]: (v4_relat_1(k5_relat_1(k6_partfun1(A_358), '#skF_4'), A_358))), inference(demodulation, [status(thm), theory('equality')], [c_2061, c_5110])).
% 10.49/4.17  tff(c_8896, plain, (![A_371]: (v4_relat_1(k5_relat_1(k6_partfun1(A_371), '#skF_4'), k1_relat_1(k6_partfun1(A_371))))), inference(superposition, [status(thm), theory('equality')], [c_271, c_8625])).
% 10.49/4.17  tff(c_8939, plain, (![A_10]: (v4_relat_1(k7_relat_1('#skF_4', A_10), k1_relat_1(k6_partfun1(A_10))) | ~v1_relat_1('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_8896])).
% 10.49/4.17  tff(c_8955, plain, (![A_372]: (v4_relat_1(k7_relat_1('#skF_4', A_372), k1_relat_1(k6_partfun1(A_372))))), inference(demodulation, [status(thm), theory('equality')], [c_135, c_8939])).
% 10.49/4.17  tff(c_8981, plain, (v4_relat_1('#skF_4', k1_relat_1(k6_partfun1('#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_174, c_8955])).
% 10.49/4.17  tff(c_8992, plain, (k7_relat_1('#skF_4', k1_relat_1(k6_partfun1('#skF_2')))='#skF_4' | ~v1_relat_1('#skF_4')), inference(resolution, [status(thm)], [c_8981, c_2])).
% 10.49/4.17  tff(c_8995, plain, (k7_relat_1('#skF_4', k1_relat_1(k6_partfun1('#skF_2')))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_8992])).
% 10.49/4.17  tff(c_9014, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4' | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_8995, c_304])).
% 10.49/4.17  tff(c_9028, plain, (k5_relat_1(k6_partfun1('#skF_2'), '#skF_4')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_9014])).
% 10.49/4.17  tff(c_1338, plain, (![E_140, B_144, A_139, F_142, C_141, D_143]: (m1_subset_1(k1_partfun1(A_139, B_144, C_141, D_143, E_140, F_142), k1_zfmisc_1(k2_zfmisc_1(A_139, D_143))) | ~m1_subset_1(F_142, k1_zfmisc_1(k2_zfmisc_1(C_141, D_143))) | ~v1_funct_1(F_142) | ~m1_subset_1(E_140, k1_zfmisc_1(k2_zfmisc_1(A_139, B_144))) | ~v1_funct_1(E_140))), inference(cnfTransformation, [status(thm)], [f_122])).
% 10.49/4.17  tff(c_60, plain, (r2_relset_1('#skF_1', '#skF_1', k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k6_partfun1('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_621, plain, (![D_95, C_96, A_97, B_98]: (D_95=C_96 | ~r2_relset_1(A_97, B_98, C_96, D_95) | ~m1_subset_1(D_95, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))) | ~m1_subset_1(C_96, k1_zfmisc_1(k2_zfmisc_1(A_97, B_98))))), inference(cnfTransformation, [status(thm)], [f_110])).
% 10.49/4.17  tff(c_629, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k6_partfun1('#skF_1'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1'))) | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(resolution, [status(thm)], [c_60, c_621])).
% 10.49/4.17  tff(c_644, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1') | ~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_629])).
% 10.49/4.17  tff(c_938, plain, (~m1_subset_1(k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4'), k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_1')))), inference(splitLeft, [status(thm)], [c_644])).
% 10.49/4.17  tff(c_1349, plain, (~m1_subset_1('#skF_4', k1_zfmisc_1(k2_zfmisc_1('#skF_2', '#skF_1'))) | ~v1_funct_1('#skF_4') | ~m1_subset_1('#skF_3', k1_zfmisc_1(k2_zfmisc_1('#skF_1', '#skF_2'))) | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_1338, c_938])).
% 10.49/4.17  tff(c_1372, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_74, c_70, c_68, c_64, c_1349])).
% 10.49/4.17  tff(c_1373, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(splitRight, [status(thm)], [c_644])).
% 10.49/4.17  tff(c_2048, plain, (k1_partfun1('#skF_1', '#skF_2', '#skF_2', '#skF_1', '#skF_3', '#skF_4')=k5_relat_1('#skF_3', '#skF_4') | ~v1_funct_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_2033])).
% 10.49/4.17  tff(c_2064, plain, (k5_relat_1('#skF_3', '#skF_4')=k6_partfun1('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_74, c_1373, c_2048])).
% 10.49/4.17  tff(c_10, plain, (![A_12]: (v1_relat_1(k2_funct_1(A_12)) | ~v1_funct_1(A_12) | ~v1_relat_1(A_12))), inference(cnfTransformation, [status(thm)], [f_53])).
% 10.49/4.17  tff(c_62, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')='#skF_2'), inference(cnfTransformation, [status(thm)], [f_164])).
% 10.49/4.17  tff(c_220, plain, (![A_77, B_78, C_79]: (k2_relset_1(A_77, B_78, C_79)=k2_relat_1(C_79) | ~m1_subset_1(C_79, k1_zfmisc_1(k2_zfmisc_1(A_77, B_78))))), inference(cnfTransformation, [status(thm)], [f_102])).
% 10.49/4.17  tff(c_226, plain, (k2_relset_1('#skF_1', '#skF_2', '#skF_3')=k2_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_70, c_220])).
% 10.49/4.17  tff(c_232, plain, (k2_relat_1('#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_226])).
% 10.49/4.17  tff(c_20, plain, (![A_15]: (k5_relat_1(k2_funct_1(A_15), A_15)=k6_relat_1(k2_relat_1(A_15)) | ~v2_funct_1(A_15) | ~v1_funct_1(A_15) | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_71])).
% 10.49/4.17  tff(c_455, plain, (![A_91]: (k5_relat_1(k2_funct_1(A_91), A_91)=k6_partfun1(k2_relat_1(A_91)) | ~v2_funct_1(A_91) | ~v1_funct_1(A_91) | ~v1_relat_1(A_91))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_20])).
% 10.49/4.17  tff(c_4, plain, (![A_3, B_7, C_9]: (k5_relat_1(k5_relat_1(A_3, B_7), C_9)=k5_relat_1(A_3, k5_relat_1(B_7, C_9)) | ~v1_relat_1(C_9) | ~v1_relat_1(B_7) | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.49/4.17  tff(c_2907, plain, (![A_219, C_220]: (k5_relat_1(k6_partfun1(k2_relat_1(A_219)), C_220)=k5_relat_1(k2_funct_1(A_219), k5_relat_1(A_219, C_220)) | ~v1_relat_1(C_220) | ~v1_relat_1(A_219) | ~v1_relat_1(k2_funct_1(A_219)) | ~v2_funct_1(A_219) | ~v1_funct_1(A_219) | ~v1_relat_1(A_219))), inference(superposition, [status(thm), theory('equality')], [c_455, c_4])).
% 10.49/4.17  tff(c_3050, plain, (![C_220]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_220))=k5_relat_1(k6_partfun1('#skF_2'), C_220) | ~v1_relat_1(C_220) | ~v1_relat_1('#skF_3') | ~v1_relat_1(k2_funct_1('#skF_3')) | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_232, c_2907])).
% 10.49/4.17  tff(c_3106, plain, (![C_220]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_220))=k5_relat_1(k6_partfun1('#skF_2'), C_220) | ~v1_relat_1(C_220) | ~v1_relat_1(k2_funct_1('#skF_3')))), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_58, c_134, c_3050])).
% 10.49/4.17  tff(c_11615, plain, (~v1_relat_1(k2_funct_1('#skF_3'))), inference(splitLeft, [status(thm)], [c_3106])).
% 10.49/4.17  tff(c_11618, plain, (~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(resolution, [status(thm)], [c_10, c_11615])).
% 10.49/4.17  tff(c_11622, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_11618])).
% 10.49/4.17  tff(c_11851, plain, (![C_439]: (k5_relat_1(k2_funct_1('#skF_3'), k5_relat_1('#skF_3', C_439))=k5_relat_1(k6_partfun1('#skF_2'), C_439) | ~v1_relat_1(C_439))), inference(splitRight, [status(thm)], [c_3106])).
% 10.49/4.17  tff(c_11908, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))=k5_relat_1(k6_partfun1('#skF_2'), '#skF_4') | ~v1_relat_1('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2064, c_11851])).
% 10.49/4.17  tff(c_11942, plain, (k5_relat_1(k2_funct_1('#skF_3'), k6_partfun1('#skF_1'))='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_135, c_9028, c_11908])).
% 10.49/4.17  tff(c_775, plain, (![B_104, A_105]: (k5_relat_1(k2_funct_1(B_104), k2_funct_1(A_105))=k2_funct_1(k5_relat_1(A_105, B_104)) | ~v2_funct_1(B_104) | ~v2_funct_1(A_105) | ~v1_funct_1(B_104) | ~v1_relat_1(B_104) | ~v1_funct_1(A_105) | ~v1_relat_1(A_105))), inference(cnfTransformation, [status(thm)], [f_86])).
% 10.49/4.17  tff(c_806, plain, (![B_104, A_19]: (k5_relat_1(k2_funct_1(B_104), k6_partfun1(A_19))=k2_funct_1(k5_relat_1(k6_partfun1(A_19), B_104)) | ~v2_funct_1(B_104) | ~v2_funct_1(k6_partfun1(A_19)) | ~v1_funct_1(B_104) | ~v1_relat_1(B_104) | ~v1_funct_1(k6_partfun1(A_19)) | ~v1_relat_1(k6_partfun1(A_19)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_775])).
% 10.49/4.17  tff(c_812, plain, (![B_104, A_19]: (k5_relat_1(k2_funct_1(B_104), k6_partfun1(A_19))=k2_funct_1(k5_relat_1(k6_partfun1(A_19), B_104)) | ~v2_funct_1(B_104) | ~v1_funct_1(B_104) | ~v1_relat_1(B_104))), inference(demodulation, [status(thm), theory('equality')], [c_79, c_80, c_78, c_806])).
% 10.49/4.17  tff(c_11960, plain, (k2_funct_1(k5_relat_1(k6_partfun1('#skF_1'), '#skF_3'))='#skF_4' | ~v2_funct_1('#skF_3') | ~v1_funct_1('#skF_3') | ~v1_relat_1('#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_11942, c_812])).
% 10.49/4.17  tff(c_11981, plain, (k2_funct_1('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_134, c_74, c_58, c_11490, c_11960])).
% 10.49/4.17  tff(c_11983, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_11981])).
% 10.49/4.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.49/4.17  
% 10.49/4.17  Inference rules
% 10.49/4.17  ----------------------
% 10.49/4.17  #Ref     : 0
% 10.49/4.17  #Sup     : 2712
% 10.49/4.17  #Fact    : 0
% 10.49/4.17  #Define  : 0
% 10.49/4.17  #Split   : 2
% 10.49/4.17  #Chain   : 0
% 10.49/4.17  #Close   : 0
% 10.49/4.17  
% 10.49/4.17  Ordering : KBO
% 10.49/4.17  
% 10.49/4.17  Simplification rules
% 10.49/4.17  ----------------------
% 10.49/4.17  #Subsume      : 40
% 10.49/4.17  #Demod        : 3846
% 10.49/4.17  #Tautology    : 884
% 10.49/4.17  #SimpNegUnit  : 1
% 10.49/4.17  #BackRed      : 26
% 10.49/4.17  
% 10.49/4.17  #Partial instantiations: 0
% 10.49/4.17  #Strategies tried      : 1
% 10.49/4.17  
% 10.49/4.17  Timing (in seconds)
% 10.49/4.17  ----------------------
% 10.74/4.17  Preprocessing        : 0.37
% 10.74/4.17  Parsing              : 0.21
% 10.74/4.17  CNF conversion       : 0.02
% 10.74/4.17  Main loop            : 2.98
% 10.74/4.17  Inferencing          : 0.66
% 10.74/4.17  Reduction            : 1.59
% 10.74/4.17  Demodulation         : 1.38
% 10.74/4.17  BG Simplification    : 0.08
% 10.74/4.17  Subsumption          : 0.51
% 10.74/4.17  Abstraction          : 0.11
% 10.74/4.17  MUC search           : 0.00
% 10.74/4.17  Cooper               : 0.00
% 10.74/4.17  Total                : 3.41
% 10.74/4.17  Index Insertion      : 0.00
% 10.74/4.17  Index Deletion       : 0.00
% 10.74/4.17  Index Matching       : 0.00
% 10.74/4.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------
